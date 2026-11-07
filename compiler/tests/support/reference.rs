//! A bounded execution oracle for tests. Its results never approve source or
//! become compiler evidence. Keep memory/validity rules independent of LLVM.
#[path = "reference/arithmetic.rs"]
mod arithmetic;
#[path = "reference/cleanup.rs"]
mod cleanup;
#[path = "reference/control.rs"]
mod control;
#[path = "reference/execute.rs"]
mod execute;
#[path = "reference/intrinsics.rs"]
mod intrinsics;
#[path = "reference/memory.rs"]
mod memory;
#[path = "reference/value.rs"]
mod value;

use cavo_compiler::{
    hir, layout, mir, mono,
    symbol::Interner,
    types::{Ty, TyId},
};
pub use memory::{Memory, Pointer};
use std::collections::{HashMap, HashSet};
pub use value::{Metadata, Value, ValueKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Undefined(&'static str),
    Trap(&'static str),
    Limit(&'static str),
    Unsupported(&'static str),
}
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Returned(Value),
    Panicked,
    Cancelled,
    Aborted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Destructor(hir::DefId),
    Freed(usize),
}

#[derive(Clone, Debug)]
pub enum Stimulus {
    Return(Value),
    Panic,
    Cancel,
}

#[derive(Clone, Copy)]
pub struct Limits {
    pub steps: usize,
    pub frames: usize,
    pub bytes: usize,
    pub objects: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            steps: 200_000,
            frames: 128,
            bytes: 16 * 1024 * 1024,
            objects: 100_000,
        }
    }
}

struct Frame<'a> {
    body: &'a mir::Body,
    cleanup: &'a mir::drop::Body,
    locals: Vec<Option<Pointer>>,
    captures: HashMap<mir::LocalId, Address>,
    flags: Vec<bool>,
    cursors: HashMap<mir::LocalId, u64>,
    registries: HashMap<mir::LocalId, Vec<usize>>,
    arguments: Vec<Value>,
    argument: usize,
    scopes: Vec<mir::ScopeId>,
}

#[derive(Clone, Debug)]
struct Address {
    pointer: Pointer,
    ty: TyId,
    metadata: Option<Metadata>,
    variant: Option<hir::DefId>,
}

struct Task {
    outcome: Option<Outcome>,
    observed: bool,
}

pub struct Machine<'a> {
    program: &'a mono::Program,
    symbols: &'a Interner,
    pub memory: Memory,
    pub events: Vec<Event>,
    pub stimuli: HashMap<hir::DefId, Stimulus>,
    limits: Limits,
    remaining: usize,
    depth: usize,
    copies: Vec<bool>,
    tasks: Vec<Task>,
    strings: HashMap<String, Pointer>,
    unions: HashMap<(usize, u64, hir::DefId), u32>,
}

impl<'a> Machine<'a> {
    pub fn new(program: &'a mono::Program, symbols: &'a Interner) -> Self {
        Self::with_limits(program, symbols, Limits::default())
    }

    pub fn with_limits(program: &'a mono::Program, symbols: &'a Interner, limits: Limits) -> Self {
        // Copy queries may intern substituted types. Use one private HIR
        // snapshot so execution cannot invalidate the compiler artifact's hash.
        let mut snapshot = program.hir.clone();
        let copies = (0..program.hir.types.values().len())
            .map(|index| hir::traits::is_copy(&mut snapshot, TyId(index as u32)))
            .collect();
        Self {
            program,
            symbols,
            memory: Memory::new(limits.bytes, limits.objects),
            events: Vec::new(),
            stimuli: HashMap::new(),
            remaining: limits.steps,
            limits,
            depth: 0,
            copies,
            tasks: Vec::new(),
            strings: HashMap::new(),
            unions: HashMap::new(),
        }
    }

    pub fn definition(&self, name: &str) -> hir::DefId {
        let internal = self.program.hir.internal_definitions();
        self.program
            .mir
            .functions
            .iter()
            .find(|body| {
                !internal.contains(&body.definition)
                    && self
                        .symbols
                        .get(self.program.hir.definitions[body.definition].name)
                        == name
            })
            .map(|body| body.definition)
            .or_else(|| {
                self.program
                    .hir
                    .definitions
                    .iter()
                    .enumerate()
                    .find(|(_, definition)| {
                        definition.kind == hir::DefinitionKind::Function
                            && self.symbols.get(definition.name) == name
                    })
                    .map(|(index, _)| hir::DefId(index as u32))
            })
            .expect("reference fixture function")
    }

    pub fn run(&mut self, name: &str, arguments: Vec<Value>) -> Result<Outcome> {
        match self.invoke(self.definition(name), arguments) {
            Err(Error::Trap(_)) => Ok(Outcome::Aborted),
            result => result,
        }
    }

    fn tick(&mut self) -> Result<()> {
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or(Error::Limit("execution step budget"))?;
        Ok(())
    }

    fn layout(&self, ty: TyId) -> Result<&layout::Layout> {
        self.program
            .layouts
            .get(ty)
            .ok_or(Error::Unsupported("missing concrete storage layout"))
    }
}
