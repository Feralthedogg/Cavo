//! Typed, target-width constant evaluation. No host function or runtime is called.

mod eval;
mod integer;
mod normalize;
mod terms;
mod verify;

pub use normalize::normalize_type_constants;
pub use terms::{check_assertions, evaluate_term};

use crate::{
    hir,
    source::Span,
    syntax::ast::{BinaryOp, UnaryOp},
    types::{GenericArg, TyId},
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Value {
    pub ty: TyId,
    pub kind: ValueKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueKind {
    Integer {
        magnitude: u128,
        negative: bool,
    },
    Bool(bool),
    Char(char),
    String(String),
    FloatBits(u64),
    Array(Vec<Value>),
    Record {
        definition: hir::DefId,
        fields: Vec<Value>,
    },
    Unit,
}

impl Value {
    pub fn usize_value(&self) -> Option<u64> {
        match self.kind {
            ValueKind::Integer {
                magnitude,
                negative: false,
            } => magnitude.try_into().ok(),
            _ => None,
        }
    }
    pub fn boolean(&self) -> Option<bool> {
        if let ValueKind::Bool(value) = self.kind {
            Some(value)
        } else {
            None
        }
    }
    pub fn scalar(&self) -> Option<hir::Constant> {
        Some(match &self.kind {
            ValueKind::Integer {
                magnitude,
                negative,
            } => hir::Constant::Integer {
                magnitude: *magnitude,
                negative: *negative,
            },
            ValueKind::Bool(value) => hir::Constant::Bool(*value),
            ValueKind::Char(value) => hir::Constant::Char(*value),
            ValueKind::String(value) => hir::Constant::String(value.clone()),
            ValueKind::FloatBits(value) => hir::Constant::Float(f64::from_bits(*value)),
            _ => return None,
        })
    }
    pub fn from_scalar(ty: TyId, constant: hir::Constant) -> Option<Self> {
        let kind = match constant {
            hir::Constant::Integer {
                magnitude,
                negative,
            } => ValueKind::Integer {
                magnitude,
                negative: negative && magnitude != 0,
            },
            hir::Constant::Bool(value) => ValueKind::Bool(value),
            hir::Constant::Char(value) => ValueKind::Char(value),
            hir::Constant::String(value) => ValueKind::String(value),
            hir::Constant::Float(value) => ValueKind::FloatBits(value.to_bits()),
            hir::Constant::Null => return None,
        };
        Some(Self { ty, kind })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);
#[derive(Clone, Debug)]
pub struct Expr {
    pub ty: TyId,
    pub span: Span,
    pub kind: ExprKind,
}
#[derive(Clone, Debug)]
pub enum ExprKind {
    Value(Value),
    IntegerBound {
        maximum: bool,
    },
    Local(u32),
    Global(hir::DefId),
    ConstParameter {
        owner: hir::DefId,
        index: u32,
    },
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
        function: hir::DefId,
        generics: Vec<GenericArg>,
        arguments: Vec<ExprId>,
    },
    Old(ExprId),
    Result,
    Array(Vec<ExprId>),
    Repeat {
        value: ExprId,
        count: ExprId,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}
#[derive(Clone, Debug)]
pub enum StatementKind {
    Declare {
        local: u32,
        value: Option<ExprId>,
    },
    Assign {
        local: u32,
        op: Option<BinaryOp>,
        value: ExprId,
    },
    Evaluate(ExprId),
    Return(Option<ExprId>),
    Block(Vec<Statement>),
    If {
        condition: ExprId,
        yes: Vec<Statement>,
        no: Vec<Statement>,
    },
    While {
        condition: ExprId,
        body: Vec<Statement>,
    },
    For {
        initialize: Vec<Statement>,
        condition: Option<ExprId>,
        update: Vec<Statement>,
        body: Vec<Statement>,
    },
    Break,
    Continue,
    Assert {
        condition: ExprId,
        message: String,
    },
}

#[derive(Clone, Debug)]
pub struct Function {
    pub definition: hir::DefId,
    pub parameters: Vec<TyId>,
    pub result: TyId,
    pub locals: Vec<TyId>,
    pub expressions: Vec<Expr>,
    pub requires: Vec<ExprId>,
    pub ensures: Vec<ExprId>,
    pub body: Vec<Statement>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Global {
    pub definition: hir::DefId,
    pub ty: TyId,
    pub expressions: Vec<Expr>,
    pub initializer: ExprId,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Assertion {
    pub owner: hir::DefId,
    pub condition: crate::types::ConstId,
    pub message: String,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub functions: BTreeMap<hir::DefId, Function>,
    pub globals: BTreeMap<hir::DefId, Global>,
    pub assertions: Vec<Assertion>,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub fuel: u64,
    pub frames: usize,
    pub queries: usize,
    pub data_bytes: u64,
    pub pointer_bits: u16,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            fuel: 100_000,
            frames: 128,
            queries: 4096,
            data_bytes: 1_048_576,
            pointer_bits: 64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    pub frames: Vec<Span>,
}
impl Error {
    pub fn new(code: &'static str, message: impl Into<String>, span: Span) -> Self {
        Self {
            code,
            message: message.into(),
            span,
            frames: Vec::new(),
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)
    }
}
impl std::error::Error for Error {}

pub fn evaluate_global(
    program: &hir::Program,
    definition: hir::DefId,
    limits: Limits,
) -> Result<Value, Error> {
    program.constants.validate(program)?;
    eval::Evaluator::new(program, limits).global(definition)
}

pub fn evaluate_function(
    program: &hir::Program,
    definition: hir::DefId,
    generics: Vec<GenericArg>,
    arguments: Vec<Value>,
    limits: Limits,
) -> Result<Value, Error> {
    program.constants.validate(program)?;
    eval::Evaluator::new(program, limits).call(definition, generics, arguments)
}

pub fn evaluate_expression(
    program: &hir::Program,
    expressions: &[Expr],
    root: ExprId,
    locals: Vec<Option<Value>>,
    limits: Limits,
) -> Result<Value, Error> {
    program.constants.validate(program)?;
    verify::expression_body(program, expressions, root, &locals)?;
    eval::Evaluator::new(program, limits).expression(expressions, root, locals)
}
