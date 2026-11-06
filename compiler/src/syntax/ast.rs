use super::token::Token;
use crate::{
    source::{FileId, Span},
    symbol::Symbol,
};

macro_rules! ids {
    ($($name:ident),+ $(,)?) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub u32);
    )+};
}
ids!(ExprId, StmtId, TypeId, ItemId);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Name {
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Debug, Default)]
pub struct Ast {
    pub modules: Vec<Module>,
    pub items: Vec<Item>,
    pub expressions: Vec<Expr>,
    pub statements: Vec<Stmt>,
    pub types: Vec<Type>,
}

impl Ast {
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.expressions[id]
    }
    pub fn stmt(&self, id: StmtId) -> &Stmt {
        &self.statements[id]
    }
    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id.0 as usize]
    }
    pub fn item(&self, id: ItemId) -> &Item {
        &self.items[id]
    }
    pub(crate) fn add_expr(&mut self, kind: ExprKind, span: Span) -> ExprId {
        let id = ExprId(
            self.expressions
                .len()
                .try_into()
                .expect("AST expression limit"),
        );
        self.expressions.push(Expr { kind, span });
        id
    }
    pub(crate) fn add_stmt(&mut self, kind: StmtKind, span: Span) -> StmtId {
        let id = StmtId(
            self.statements
                .len()
                .try_into()
                .expect("AST statement limit"),
        );
        self.statements.push(Stmt { kind, span });
        id
    }
    pub(crate) fn add_type(&mut self, kind: TypeKind, span: Span) -> TypeId {
        let id = TypeId(self.types.len().try_into().expect("AST type limit"));
        self.types.push(Type { kind, span });
        id
    }
    pub(crate) fn add_item(&mut self, item: Item) -> ItemId {
        let id = ItemId(self.items.len().try_into().expect("AST item limit"));
        self.items.push(item);
        id
    }
}

#[derive(Debug)]
pub struct Module {
    pub file: FileId,
    pub name: Vec<Name>,
    pub imports: Vec<Import>,
    pub items: Vec<ItemId>,
}
#[derive(Debug)]
pub struct Import {
    pub path: Vec<Name>,
    pub span: Span,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Package,
    Public,
}
#[derive(Debug)]
pub struct Attribute {
    pub expression: Option<ExprId>,
    pub name: Name,
    pub arguments: Vec<Token>,
    pub span: Span,
}
#[derive(Debug)]
pub struct Item {
    pub name: Option<Name>,
    pub visibility: Visibility,
    pub attributes: Vec<Attribute>,
    pub kind: ItemKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum ItemKind {
    Function(Function),
    TypeAlias {
        generics: Vec<GenericParam>,
        target: TypeId,
    },
    Record {
        union: bool,
        generics: Vec<GenericParam>,
        fields: Vec<Field>,
        assertions: Vec<StaticAssert>,
    },
    Enum {
        generics: Vec<GenericParam>,
        variants: Vec<Variant>,
    },
    Trait {
        generics: Vec<GenericParam>,
        bounds: Vec<TypeId>,
        methods: Vec<ItemId>,
    },
    Impl {
        generics: Vec<GenericParam>,
        trait_type: Option<TypeId>,
        target: TypeId,
        methods: Vec<ItemId>,
        trusted_reason: Option<ExprId>,
    },
    Contract {
        generics: Vec<GenericParam>,
        parameters: Vec<Parameter>,
        requirements: Vec<ExprId>,
    },
    Extern {
        abi: ExprId,
        items: Vec<ItemId>,
    },
    Global(Variable),
    StaticAssert(StaticAssert),
}
#[derive(Debug)]
pub struct Function {
    pub constant: bool,
    pub generics: Vec<GenericParam>,
    pub parameters: Vec<Parameter>,
    pub result: TypeId,
    pub clauses: Vec<Clause>,
    pub body: Option<Block>,
    pub variadic: bool,
}
#[derive(Debug)]
pub enum GenericParam {
    Type { name: Name, bounds: Vec<TypeId> },
    Const { name: Name, ty: TypeId },
    Lifetime(Name),
}
#[derive(Clone, Debug)]
pub enum GenericArg {
    Type(TypeId),
    Const(ExprId),
    /// A simple path is resolved according to the declaration's parameter kind.
    Path(Vec<Name>),
    Lifetime(Name),
}
#[derive(Debug)]
pub struct StaticAssert {
    pub condition: ExprId,
    pub message: Option<ExprId>,
    pub span: Span,
}
#[derive(Debug)]
pub struct Parameter {
    pub name: Name,
    pub ty: TypeId,
    pub moved: bool,
}
#[derive(Debug)]
pub struct Field {
    pub name: Name,
    pub ty: TypeId,
    pub visibility: Visibility,
}
#[derive(Debug)]
pub struct Variant {
    pub name: Name,
    pub fields: Vec<TypeId>,
    pub named_fields: Vec<Field>,
    pub discriminant: Option<ExprId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClauseKind {
    Requires,
    Ensures,
}
#[derive(Debug)]
pub struct Clause {
    pub kind: ClauseKind,
    pub predicate: ExprId,
}
#[derive(Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum TypeKind {
    Path {
        path: Vec<Name>,
        arguments: Vec<GenericArg>,
    },
    Reference {
        lifetime: Option<Name>,
        mutable: bool,
        inner: TypeId,
    },
    Const(TypeId),
    Slice(TypeId),
    Array {
        inner: TypeId,
        length: ExprId,
    },
    Function {
        lifetimes: Vec<Name>,
        parameters: Vec<TypeId>,
        result: TypeId,
        attributes: Vec<Attribute>,
    },
    Dynamic(Vec<TypeId>),
    Lifetime(Name),
    Infer,
    Error,
}
#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum ExprKind {
    Literal(LiteralKind),
    Path(Vec<Name>),
    Group(ExprId),
    Block(Block),
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
    },
    Field {
        base: ExprId,
        name: Name,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Try(ExprId),
    Array(Vec<ExprId>),
    Repeat {
        value: ExprId,
        count: ExprId,
    },
    Record {
        path: Vec<Name>,
        fields: Vec<(Name, ExprId)>,
    },
    Match {
        value: ExprId,
        arms: Vec<MatchArm>,
    },
    Closure {
        captures: Vec<Capture>,
        parameters: Vec<Parameter>,
        result: Option<TypeId>,
        body: Block,
    },
    Error,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralKind {
    Integer,
    Float,
    String,
    Char,
    Bool(bool),
    Null,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Negate,
    Positive,
    Not,
    BitNot,
    Dereference,
    Borrow,
    BorrowMut,
    Move,
    Spawn,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    BitAnd,
    BitXor,
    BitOr,
    And,
    Or,
}
#[derive(Debug)]
pub struct Capture {
    pub name: Name,
    pub mode: CaptureMode,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureMode {
    Move,
    Shared,
    Mutable,
}
#[derive(Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<ExprId>,
    pub value: ExprId,
}
#[derive(Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum PatternKind {
    Wildcard,
    Path {
        path: Vec<Name>,
        fields: Vec<Pattern>,
    },
    Literal(LiteralKind),
    Error,
}
#[derive(Debug)]
pub struct Block {
    pub statements: Vec<StmtId>,
    pub span: Span,
}
#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}
#[derive(Debug)]
pub enum StmtKind {
    Variable(Variable),
    StaticAssert(StaticAssert),
    Expression(ExprId),
    Assign {
        target: ExprId,
        op: Option<BinaryOp>,
        value: ExprId,
    },
    Return(Option<ExprId>),
    Block(Block),
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
        variable: Variable,
        iterable: ExprId,
        body: Block,
    },
    Scope {
        name: Option<Name>,
        body: Block,
    },
    Contract(Block),
    Defer(Block),
    Assume {
        predicate: ExprId,
        reason: ExprId,
    },
    Break,
    Continue,
    Empty,
    Error,
}
#[derive(Debug)]
pub struct Variable {
    pub constant: bool,
    pub name: Name,
    pub ty: TypeId,
    pub initializer: Option<ExprId>,
}
