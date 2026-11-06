mod control;
mod expression;

use super::*;
use crate::types::{GenericArg, Region, Ty};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Binding {
    Type(TyId),
    Const(Value),
    Lifetime(Region),
}
#[derive(Clone, Debug, Default)]
pub(super) struct Bindings {
    pub owner: Option<hir::DefId>,
    pub values: Vec<Binding>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Query {
    Global(hir::DefId),
    Call(hir::DefId, Vec<Binding>, Vec<Value>),
}
#[derive(Clone)]
struct Cached {
    value: Value,
    fuel: u64,
    bytes: u64,
}

pub(super) struct Frame<'a> {
    expressions: &'a [Expr],
    locals: Vec<Option<Value>>,
    entry: Vec<Option<Value>>,
    bindings: Bindings,
    result: Option<Value>,
}

#[derive(Clone, Copy)]
struct View<'a> {
    expressions: &'a [Expr],
    locals: &'a [Option<Value>],
    entry: &'a [Option<Value>],
    bindings: &'a Bindings,
    result: Option<&'a Value>,
}
impl Frame<'_> {
    fn view(&self) -> View<'_> {
        View {
            expressions: self.expressions,
            locals: &self.locals,
            entry: &self.entry,
            bindings: &self.bindings,
            result: self.result.as_ref(),
        }
    }
}

pub(super) struct Evaluator<'a> {
    pub program: &'a hir::Program,
    pub limits: Limits,
    fuel: u64,
    bytes: u64,
    active: HashSet<Query>,
    cache: HashMap<Query, Cached>,
    frames: Vec<Span>,
    expression_depth: usize,
}

impl<'a> Evaluator<'a> {
    pub fn new(program: &'a hir::Program, limits: Limits) -> Self {
        Self {
            program,
            limits,
            fuel: 0,
            bytes: 0,
            active: HashSet::new(),
            cache: HashMap::new(),
            frames: Vec::new(),
            expression_depth: 0,
        }
    }
    pub fn global(&mut self, definition: hir::DefId) -> Result<Value, Error> {
        let global = self
            .program
            .constants
            .globals
            .get(&definition)
            .ok_or_else(|| {
                self.context_error(definition, "constant definition has no checked initializer")
            })?;
        let query = Query::Global(definition);
        if let Some(value) = self.cached(&query, global.span)? {
            return Ok(value);
        }
        let start = self.begin(query.clone(), global.span)?;
        let frame = Frame {
            expressions: &global.expressions,
            locals: Vec::new(),
            entry: Vec::new(),
            bindings: Bindings::default(),
            result: None,
        };
        let result = self.eval(global.initializer, &frame);
        self.finish(query, start, result)
    }
    pub fn call(
        &mut self,
        definition: hir::DefId,
        generics: Vec<GenericArg>,
        arguments: Vec<Value>,
    ) -> Result<Value, Error> {
        let bindings = self.resolve_bindings(definition, &generics, &Bindings::default())?;
        self.invoke(definition, bindings, arguments)
    }
    pub fn expression(
        &mut self,
        expressions: &[Expr],
        root: ExprId,
        locals: Vec<Option<Value>>,
    ) -> Result<Value, Error> {
        let frame = Frame {
            expressions,
            entry: locals.clone(),
            locals,
            bindings: Bindings::default(),
            result: None,
        };
        self.eval(root, &frame)
    }
    pub(in crate::ctfe) fn invoke(
        &mut self,
        definition: hir::DefId,
        bindings: Bindings,
        arguments: Vec<Value>,
    ) -> Result<Value, Error> {
        let function = self
            .program
            .constants
            .functions
            .get(&definition)
            .ok_or_else(|| {
                self.context_error(definition, "call does not name a checked const function")
            })?;
        self.check_arguments(function, &bindings, &arguments)?;
        let query = Query::Call(definition, bindings.values.clone(), arguments.clone());
        if let Some(value) = self.cached(&query, function.span)? {
            return Ok(value);
        }
        let start = self.begin(query.clone(), function.span)?;
        self.charge(0, function.locals.len() as u64 * 16, function.span)?;
        let mut locals = vec![None; function.locals.len()];
        for (slot, argument) in locals.iter_mut().zip(arguments) {
            *slot = Some(argument);
        }
        let mut frame = Frame {
            expressions: &function.expressions,
            entry: locals.clone(),
            locals,
            bindings,
            result: None,
        };
        let result = self.execute(function, &mut frame);
        self.finish(query, start, result)
    }
    fn execute(&mut self, function: &Function, frame: &mut Frame<'_>) -> Result<Value, Error> {
        self.assertions(function.definition, &frame.bindings)?;
        for &requirement in &function.requires {
            self.contract(requirement, frame, "requires condition is false")?;
        }
        let result = match self.block(&function.body, frame)? {
            control::Flow::Return(value) => value,
            control::Flow::Next if function.result == TyId::VOID => Value {
                ty: TyId::VOID,
                kind: ValueKind::Unit,
            },
            _ => {
                return Err(Error::new(
                    "E-CONST-CONTEXT",
                    "const function did not return a value",
                    function.span,
                ));
            }
        };
        let expected = self.bound_type(function.result, &frame.bindings);
        if !self.program.types.compatible(result.ty, expected) {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "const function result type mismatch",
                function.span,
            ));
        }
        frame.result = Some(result.clone());
        for &requirement in &function.ensures {
            self.contract(requirement, frame, "ensures condition is false")?;
        }
        Ok(result)
    }
    fn contract(
        &mut self,
        expression: ExprId,
        frame: &mut Frame<'_>,
        message: &str,
    ) -> Result<(), Error> {
        if self.eval(expression, frame)?.boolean() == Some(true) {
            return Ok(());
        }
        Err(Error::new(
            "E-CONST-CONTRACT",
            message,
            frame.expressions[expression.0 as usize].span,
        ))
    }
    fn check_arguments(
        &self,
        function: &Function,
        bindings: &Bindings,
        arguments: &[Value],
    ) -> Result<(), Error> {
        if arguments.len() != function.parameters.len() {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "const call argument count mismatch",
                function.span,
            ));
        }
        for (&parameter, argument) in function.parameters.iter().zip(arguments) {
            if !matches!(
                self.program.types.get(argument.ty),
                Ty::Integer { .. } | Ty::Bool | Ty::Char
            ) {
                return Err(Error::new(
                    "E-CONST-CONTEXT",
                    "const call arguments must instantiate to scalar values",
                    function.span,
                ));
            }
            integer::validate(
                &self.program.types,
                argument,
                self.limits.pointer_bits,
                function.span,
            )?;
            let expected = self.bound_type(parameter, bindings);
            if !self.program.types.compatible(argument.ty, expected) {
                return Err(Error::new(
                    "E-CONST-CONTEXT",
                    "const call argument type mismatch",
                    function.span,
                ));
            }
        }
        Ok(())
    }
    pub(in crate::ctfe) fn bound_type(&self, ty: TyId, bindings: &Bindings) -> TyId {
        if let Ty::Parameter { owner, index } = self.program.types.get(ty)
            && Some(*owner) == bindings.owner
            && let Some(Binding::Type(ty)) = bindings.values.get(*index as usize)
        {
            *ty
        } else {
            ty
        }
    }
    fn cached(&mut self, query: &Query, span: Span) -> Result<Option<Value>, Error> {
        let Some(cached) = self.cache.get(query).cloned() else {
            return Ok(None);
        };
        // Logical cost is replayed on hits: cache warmth cannot change whether a
        // required constant fits its evaluation budget.
        self.charge(cached.fuel, cached.bytes, span)?;
        Ok(Some(cached.value))
    }
    fn begin(&mut self, query: Query, span: Span) -> Result<(u64, u64), Error> {
        if self.frames.len() >= self.limits.frames
            || self.active.len() + self.cache.len() >= self.limits.queries
        {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant query depth or count limit exceeded",
                span,
            ));
        }
        if !self.active.insert(query) {
            return Err(Error::new(
                "E-CONST-CYCLE",
                "constant value dependency repeats an active query",
                span,
            ));
        }
        self.frames.push(span);
        let start = (self.fuel, self.bytes);
        self.charge(1, 0, span)?;
        Ok(start)
    }
    fn finish(
        &mut self,
        query: Query,
        start: (u64, u64),
        result: Result<Value, Error>,
    ) -> Result<Value, Error> {
        let span = *self.frames.last().expect("active constant query frame");
        let result = result
            .and_then(|value| {
                super::verify::valid_value(self.program, &value, span)?;
                self.charge(0, expression::value_cost(&value, span)?, span)?;
                Ok(value)
            })
            .map_err(|mut error| {
                if error.frames.is_empty() {
                    error.frames = self.frames.clone();
                }
                error
            });
        self.frames.pop();
        self.active.remove(&query);
        if let Ok(value) = &result {
            self.cache.insert(
                query,
                Cached {
                    value: value.clone(),
                    fuel: self.fuel - start.0,
                    bytes: self.bytes - start.1,
                },
            );
        }
        result
    }
    pub(in crate::ctfe) fn charge(
        &mut self,
        fuel: u64,
        bytes: u64,
        span: Span,
    ) -> Result<(), Error> {
        self.fuel = self.fuel.checked_add(fuel).ok_or_else(|| limit(span))?;
        self.bytes = self.bytes.checked_add(bytes).ok_or_else(|| limit(span))?;
        if self.fuel > self.limits.fuel || self.bytes > self.limits.data_bytes {
            return Err(limit(span));
        }
        Ok(())
    }
    fn context_error(&self, definition: hir::DefId, message: &str) -> Error {
        let span = self
            .program
            .definitions
            .get(definition.0 as usize)
            .map_or(Span::new(crate::source::FileId(0), 0, 0), |definition| {
                definition.span
            });
        Error::new("E-CONST-CONTEXT", message, span)
    }
}

fn limit(span: Span) -> Error {
    Error::new(
        "E-CONST-LIMIT",
        "constant evaluation exceeded its logical fuel or data budget",
        span,
    )
}
