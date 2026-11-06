//! Execution-oriented, pre-elaboration MIR. It is not an ownership certificate.
//!
//! Move operands clear the source's logical initialization paths; successful
//! assignments initialize the destination paths. `Drop` consults those paths,
//! clears them before invoking glue, and visits record fields in declaration
//! order. Concrete flags, Drop glue, ABI and cancellation points are still pending.

mod analysis;
mod dump;
mod lower;
mod verify;

pub mod borrow;
pub mod drop;
pub mod effects;
pub mod tasks;

pub use analysis::Analysis;
pub(crate) use analysis::analyze;
pub use lower::{LowerError, lower};
pub use verify::InvariantError;

use crate::{
    hir,
    source::Span,
    symbol::Symbol,
    syntax::ast::{BinaryOp, UnaryOp},
    types::{GenericArg, TyId},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Body>,
}

#[derive(Debug)]
pub struct Body {
    pub definition: hir::DefId,
    pub result: TyId,
    pub locals: Vec<Local>,
    pub scopes: Vec<Scope>,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
    pub return_local: LocalId,
}

#[derive(Debug)]
pub struct Local {
    pub ty: TyId,
    pub kind: LocalKind,
    pub scope: ScopeId,
    pub name: Option<Symbol>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalKind {
    TaskRegistry,
    Return,
    Parameter,
    Source,
    Temporary,
    /// Owns an array and a private cursor. Ordinary value access is forbidden;
    /// IteratorNext transfers one initialized element and advances atomically.
    ArrayIterator,
    /// Internal place handle: `ty` is the pointee, never a Cavo value type.
    Address,
}

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: LocalId,
    pub projection: Vec<Projection>,
}
impl Place {
    pub fn local(local: LocalId) -> Self {
        Self {
            local,
            projection: Vec::new(),
        }
    }
    pub fn project(mut self, projection: Projection) -> Self {
        self.projection.push(projection);
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Projection {
    Deref,
    Downcast(hir::DefId),
    Field(u32),
    Index(LocalId),
}

#[derive(Clone, Debug)]
pub enum Operand {
    ConstTerm {
        value: crate::types::ConstId,
        ty: TyId,
    },
    Constant {
        value: hir::Constant,
        ty: TyId,
    },
    Copy(Place),
    Move(Place),
    Function {
        definition: hir::DefId,
        ty: TyId,
    },
    Unit,
}

#[derive(Clone, Debug)]
pub enum Rvalue {
    IsVariant {
        place: Place,
        variant: hir::DefId,
    },
    RepeatConst {
        value: Operand,
        count: crate::types::ConstId,
    },
    Use(Operand),
    Unary {
        op: UnaryOp,
        operand: Operand,
    },
    Binary {
        op: BinaryOp,
        left: Operand,
        right: Operand,
    },
    Borrow {
        mutable: bool,
        place: Place,
    },
    /// Captures an address once, before a possibly effectful assignment RHS.
    AddressOf(Place),
    Array(Vec<Operand>),
    Repeat {
        value: Operand,
        count: u64,
    },
    Record {
        definition: hir::DefId,
        fields: Vec<(u32, Operand)>,
    },
    Variant {
        definition: hir::DefId,
        fields: Vec<Operand>,
    },
    ArrayToSlice(Operand),
    /// Retains reference permissions/origin while pairing its data with the
    /// concrete trait implementation witness selected by the type checker.
    DynCoerce {
        value: Operand,
        vtable: u32,
    },
    Length(Place),
}

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum StatementKind {
    RegistryStart(LocalId),
    Contract(crate::contracts::Statement),
    EnterScope(ScopeId),
    ExitScope(ScopeId),
    StorageLive(LocalId),
    StorageDead(LocalId),
    /// Initializes an incoming parameter; not an ordinary value copy.
    Argument(LocalId),
    IteratorStart {
        iterator: LocalId,
        value: Operand,
    },
    Assign {
        destination: Place,
        value: Rvalue,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExitKind {
    Normal,
    Panic,
    Cancel,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
    pub span: Span,
    pub cleanup: Option<ExitKind>,
}

#[derive(Debug)]
pub enum Terminator {
    Spawn {
        scope: ScopeId,
        registry: LocalId,
        callee: Operand,
        type_arguments: Vec<GenericArg>,
        arguments: Vec<Operand>,
        parameter_types: Vec<TyId>,
        child_result: TyId,
        capture_type: TyId,
        destination: Place,
        normal: BlockId,
        panic: BlockId,
        cancel: BlockId,
    },
    TaskDrain {
        scope: ScopeId,
        registry: LocalId,
        exit: tasks::ScopeExit,
        next: BlockId,
        abort: BlockId,
    },
    Goto(BlockId),
    /// Some initializes destination and consumes exactly one element. None
    /// leaves it uninitialized; cleanup drops only the iterator's remaining tail.
    IteratorNext {
        iterator: LocalId,
        destination: Place,
        some: BlockId,
        none: BlockId,
    },
    Switch {
        condition: Operand,
        yes: BlockId,
        no: BlockId,
    },
    Call {
        callee: Operand,
        type_arguments: Vec<GenericArg>,
        arguments: Vec<Operand>,
        parameter_types: Vec<TyId>,
        destination: Place,
        normal: BlockId,
        panic: BlockId,
        cancel: BlockId,
    },
    DynCall {
        receiver: Operand,
        trait_method: hir::DefId,
        arguments: Vec<Operand>,
        /// Explicit arguments only; the receiver is checked separately.
        parameter_types: Vec<TyId>,
        destination: Place,
        normal: BlockId,
        panic: BlockId,
        cancel: BlockId,
    },
    /// Arithmetic traps are explicit edges, not unchecked machine operations.
    Checked {
        value: Rvalue,
        destination: Place,
        normal: BlockId,
        trap: BlockId,
    },
    Bounds {
        base: Place,
        index: LocalId,
        normal: BlockId,
        trap: BlockId,
    },
    /// Conditional on logical initialization, including partial move paths.
    /// Concrete destructor/glue elaboration must preserve these edges and order.
    Drop {
        place: Place,
        next: BlockId,
        unwind: BlockId,
    },
    Return,
    Resume(ExitKind),
    Abort,
    Unreachable,
}

impl Body {
    pub fn block(&self, id: BlockId) -> &Block {
        &self.blocks[id]
    }
    pub fn local(&self, id: LocalId) -> &Local {
        &self.locals[id]
    }
}
