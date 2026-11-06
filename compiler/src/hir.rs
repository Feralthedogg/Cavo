//! Resolved, typed high-level IR. Expression/local IDs are scoped to their function.
//! Type checking does not authorize alias, ownership, contract, or LLVM assumptions.

mod closures;
pub mod traits;
mod verify;
pub use closures::{Closure, ClosureKind};
pub use verify::InvariantError;

use crate::{
    source::Span,
    symbol::Symbol,
    syntax::ast::{BinaryOp, ClauseKind, UnaryOp, Visibility},
    types::{GenericArg, GenericParamKind, TyId, TypeContext},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StmtId(pub u32);

#[derive(Clone, Debug)]
pub struct Program {
    pub constants: crate::ctfe::Program,
    pub stage: ValidationStage,
    pub modules: Vec<Module>,
    pub definitions: Vec<Definition>,
    pub types: TypeContext,
    pub records: Vec<Record>,
    pub enums: Vec<Enum>,
    pub functions: Vec<Function>,
    pub closures: Vec<Closure>,
    pub traits: Vec<traits::Trait>,
    pub implementations: Vec<traits::Impl>,
    pub vtables: Vec<traits::Vtable>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValidationStage {
    Types,
}
#[derive(Clone, Debug)]
pub struct Module {
    pub path: Vec<Symbol>,
    pub definitions: Vec<DefId>,
}
#[derive(Clone, Debug)]
pub struct Definition {
    /// Original checked const function, preserved by concrete instantiation.
    pub const_origin: Option<DefId>,
    pub name: Symbol,
    pub module: ModuleId,
    pub visibility: Visibility,
    pub kind: DefinitionKind,
    pub ty: TyId,
    pub span: Span,
    pub attributes: Vec<Attribute>,
    pub foreign_abi: Option<String>,
    pub lifetime_parameters: Vec<Symbol>,
    pub type_parameter_count: u32,
    /// All parameter kinds in declaration order, including explicit lifetimes.
    pub generic_parameter_kinds: Vec<GenericParamKind>,
    /// Source contracts remain unproven; body clauses have a separate typed IR.
    pub declaration_clauses: Vec<(ClauseKind, Span)>,
    pub bounds: Vec<traits::TraitBound>,
}
#[derive(Clone, Debug)]
pub struct Attribute {
    pub constant: Option<crate::types::ConstId>,
    pub name: Symbol,
    pub arguments: Vec<crate::syntax::token::Token>,
    pub span: Span,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefinitionKind {
    Function,
    TypeAlias,
    Record,
    Union,
    Enum,
    Variant { parent: DefId, index: u32 },
    Trait,
    Impl,
    Contract,
    Global,
}
#[derive(Clone, Debug)]
pub struct Record {
    pub definition: DefId,
    pub parameters: Vec<Symbol>,
    pub fields: Vec<Field>,
}
#[derive(Clone, Debug)]
pub struct Field {
    pub name: Symbol,
    pub ty: TyId,
    pub visibility: Visibility,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Enum {
    pub definition: DefId,
    pub variants: Vec<DefId>,
    pub discriminants: Vec<crate::types::ConstId>,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub definition: DefId,
    pub type_parameters: Vec<Symbol>,
    pub parameters: Vec<LocalId>,
    pub result: TyId,
    pub locals: Vec<Local>,
    pub clauses: Vec<Clause>,
    pub body: Block,
    pub expressions: Vec<Expr>,
    pub statements: Vec<Stmt>,
}
#[derive(Clone, Debug)]
pub struct Local {
    pub name: Symbol,
    pub ty: TyId,
    pub mutable: bool,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Clause {
    pub kind: ClauseKind,
    pub predicate: ExprId,
    pub result_local: Option<LocalId>,
}
#[derive(Clone, Debug)]
pub struct Block {
    pub statements: Vec<StmtId>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: TyId,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum ExprKind {
    Constant(Constant),
    ConstTerm(crate::types::ConstId),
    Local(LocalId),
    Definition(DefId),
    Unary {
        op: UnaryOp,
        operand: ExprId,
    },
    Binary {
        op: BinaryOp,
        left: ExprId,
        right: ExprId,
    },
    Call {
        callee: ExprId,
        type_arguments: Vec<GenericArg>,
        arguments: Vec<ExprId>,
        parameter_types: Vec<TyId>,
    },
    Field {
        base: ExprId,
        index: u32,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Array(Vec<ExprId>),
    Repeat {
        value: ExprId,
        count: u64,
    },
    RepeatConst {
        value: ExprId,
        count: crate::types::ConstId,
    },
    Record {
        definition: DefId,
        fields: Vec<(u32, ExprId)>,
    },
    CoerceArrayToSlice(ExprId),
    DynCoerce {
        value: ExprId,
        vtable: u32,
    },
    DynCall {
        receiver: ExprId,
        trait_method: DefId,
        arguments: Vec<ExprId>,
        parameter_types: Vec<TyId>,
    },
    IsVariant {
        base: ExprId,
        variant: DefId,
    },
    VariantField {
        base: ExprId,
        variant: DefId,
        index: u32,
    },
    Match {
        subject: ExprId,
        temporary: LocalId,
        arms: Vec<MatchArm>,
    },
    BlockValue {
        body: Block,
        value: Option<ExprId>,
    },
    Group(ExprId),
    Old(ExprId),
    Error,
}
#[derive(Clone, Debug)]
pub enum Constant {
    Integer { magnitude: u128, negative: bool },
    Float(f64),
    Bool(bool),
    Char(char),
    String(String),
    Null,
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<ExprId>,
    pub value: ExprId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingMode {
    Copy,
    Move,
    Shared,
    Mutable,
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub ty: TyId,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatternKind {
    Wildcard,
    Binding {
        local: LocalId,
        mode: BindingMode,
    },
    Literal(Constant),
    Variant {
        definition: DefId,
        fields: Vec<Pattern>,
    },
}
#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum StmtKind {
    Declare {
        local: LocalId,
        initializer: Option<ExprId>,
    },
    Expression(ExprId),
    Assign {
        target: ExprId,
        op: Option<BinaryOp>,
        value: ExprId,
    },
    Return(Option<ExprId>),
    Block(Block),
    Defer {
        /// Hidden reference bindings initialized when the cleanup is registered.
        captures: Vec<(LocalId, ExprId)>,
        body: Block,
    },
    If {
        condition: ExprId,
        then_block: Block,
        otherwise: Option<StmtId>,
    },
    While {
        condition: ExprId,
        body: Block,
    },
    For {
        initialize: Option<StmtId>,
        condition: Option<ExprId>,
        update: Option<StmtId>,
        body: Block,
    },
    ForIn {
        local: LocalId,
        iterable: ExprId,
        body: Block,
    },
    Break,
    Continue,
    Empty,
    Error,
}
