//! Concrete initialization flags and conditional cleanup control flow.
//!
//! Core instruction references deliberately reuse the validated MIR rather than
//! copying its expression/statement arenas. This artifact must travel with that
//! MIR and be revalidated after either representation changes.

mod glue;
mod lower;
mod paths;
mod visit;
use glue::Glues;
use lower::Builder;
use paths::Paths;
use visit::{captures, droppable_places, visit_moves};

use super::{BlockId as CoreBlock, LocalKind, Operand, Place, Projection, Rvalue};
use crate::{
    hir,
    local::properties::Properties,
    types::{GenericArg, Ty, TyId},
};
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Write},
    ops::Range,
};

const LIMIT: usize = 200_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FlagId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GlueId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub functions: Vec<Body>,
    pub glue: Vec<Glue>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub definition: hir::DefId,
    /// Flags start Clear; StorageLive also clears them on loop re-entry.
    pub flags: Vec<Flag>,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Flag {
    pub place: Place,
    pub ty: TyId,
    pub glue: GlueId,
    pub kind: FlagKind,
    pub guards: Vec<VariantGuard>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlagKind {
    Value,
    UserDestructor,
    Initialization,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantGuard {
    pub place: Place,
    pub variant: hir::DefId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlagValue {
    Clear,
    Set,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instruction {
    CoreStatement {
        source: CoreBlock,
        statement: u32,
    },
    SetFlag {
        flag: FlagId,
        value: FlagValue,
    },
    /// A destructor may run only after every field has become initialized.
    RecomputeFlag {
        flag: FlagId,
        all: Vec<FlagId>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    /// Successors have the core terminator's order: goto; yes/no;
    /// normal/panic/cancel; normal/trap. Terminal core operations have none.
    Core {
        source: CoreBlock,
        successors: Vec<BlockId>,
    },
    Goto(BlockId),
    TestFlag {
        flag: FlagId,
        initialized: BlockId,
        clear: BlockId,
    },
    TestVariant {
        place: Place,
        variant: hir::DefId,
        matches: BlockId,
        otherwise: BlockId,
    },
    InvokeGlue {
        place: Place,
        glue: GlueId,
        next: BlockId,
        unwind: BlockId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Glue {
    pub ty: TyId,
    pub kind: GlueKind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlueKind {
    TaskHandle,
    Trivial,
    Record(Vec<FieldGlue>),
    Array {
        element: GlueId,
        count: u64,
    },
    SymbolicArray {
        element: GlueId,
        count: crate::types::ConstId,
    },
    /// The internal iterator owns the array and its current consumption cursor.
    ArrayTail {
        element: GlueId,
        count: ArrayLength,
    },
    User {
        destructor: hir::traits::MethodSelection,
        fields: GlueId,
        concrete: bool,
    },
    /// Per-place owner flag invokes only the user body; field flags run next.
    Destructor {
        destructor: hir::traits::MethodSelection,
        concrete: bool,
    },
    /// Dispatch only the active variant, then visit its fields in declaration order.
    Enum(Vec<VariantGlue>),
    /// Monomorphization must replace this with the concrete type's glue.
    Parameter {
        owner: hir::DefId,
        index: u32,
    },
    /// Unions and other opaque ownership cannot invent an active field to drop.
    Manual,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArrayLength {
    Concrete(u64),
    Deferred(crate::types::ConstId),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldGlue {
    pub field: u32,
    pub glue: GlueId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantGlue {
    pub variant: hir::DefId,
    pub fields: Vec<GlueId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error(pub String);
impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}
impl std::error::Error for Error {}

pub fn elaborate(core: &super::Program, hir: &mut hir::Program) -> Result<Program, Error> {
    core.validate(hir)
        .map_err(|error| Error(error.to_string()))?;
    build(core, hir)
}

impl Program {
    /// Canonical correspondence is intentionally strict until optimizing passes
    /// have their own flag-preservation certificates. A changed core is rechecked.
    pub fn validate(&self, core: &super::Program, hir: &mut hir::Program) -> Result<(), Error> {
        let expected = elaborate(core, hir)?;
        if *self != expected {
            return Err(Error(
                "drop elaboration differs from its verified core MIR".into(),
            ));
        }
        Ok(())
    }
    pub fn require_concrete(&self) -> Result<(), Error> {
        if self.glue.iter().any(|glue| {
            matches!(
                glue.kind,
                GlueKind::Parameter { .. }
                    | GlueKind::Manual
                    | GlueKind::SymbolicArray { .. }
                    | GlueKind::ArrayTail {
                        count: ArrayLength::Deferred(_),
                        ..
                    }
                    | GlueKind::User {
                        concrete: false,
                        ..
                    }
                    | GlueKind::Destructor {
                        concrete: false,
                        ..
                    }
            )
        }) {
            return Err(Error(
                "drop glue still has generic or manual ownership obligations".into(),
            ));
        }
        Ok(())
    }
    pub fn dump(&self) -> String {
        let mut output = String::from("\nexplicit drop flags and glue\n");
        for (index, glue) in self.glue.iter().enumerate() {
            let _ = writeln!(output, "  glue g{index}: ty{} {:?}", glue.ty.0, glue.kind);
        }
        for body in &self.functions {
            dump_body(body, &mut output);
        }
        output
    }
}

fn dump_body(body: &Body, output: &mut String) {
    let _ = writeln!(
        output,
        "drop fn #{} entry db{} {{",
        body.definition.0, body.entry.0
    );
    for (index, flag) in body.flags.iter().enumerate() {
        let _ = writeln!(
            output,
            "  flag d{index} = clear; {:?}, glue g{}",
            flag.place, flag.glue.0
        );
    }
    for (index, block) in body.blocks.iter().enumerate() {
        let _ = writeln!(output, "  db{index}:");
        for instruction in &block.instructions {
            let _ = writeln!(output, "    {instruction:?}");
        }
        let _ = writeln!(output, "    {:?}", block.terminator);
    }
    output.push_str("}\n");
}

fn build(core: &super::Program, hir: &mut hir::Program) -> Result<Program, Error> {
    let properties = Properties::compute(hir);
    let mut glue = Glues {
        hir,
        properties: &properties,
        entries: Vec::new(),
        indices: HashMap::new(),
        structural: HashMap::new(),
        destructors: HashMap::new(),
        tails: HashMap::new(),
    };
    let mut functions = Vec::with_capacity(core.functions.len());
    for body in &core.functions {
        functions.push(Builder::new(body, &mut glue)?.build()?);
    }
    Ok(Program {
        functions,
        glue: glue.entries,
    })
}
