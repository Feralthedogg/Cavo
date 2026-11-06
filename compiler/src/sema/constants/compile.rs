mod control;
mod expression;

use super::*;
use crate::{
    ctfe::{Expr, ExprId, ExprKind, Function, Statement},
    syntax::ast::{BinaryOp, UnaryOp},
    types::{GenericArg, GenericParamKind},
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Init {
    No,
    Yes,
    Maybe,
}
#[derive(Clone, Copy)]
struct Local {
    id: u32,
    ty: TyId,
    constant: bool,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Body,
    Requires,
    Ensures,
}

struct Compiler<'a, 'b> {
    context: &'b mut Context<'a>,
    module: ModuleId,
    owner: DefId,
    types: HashMap<Symbol, TyId>,
    external: &'b ConstBindings,
    scopes: Vec<HashMap<Symbol, Local>>,
    locals: Vec<TyId>,
    initialized: Vec<Init>,
    constant_values: HashMap<u32, ConstBinding>,
    expressions: Vec<Expr>,
    result: TyId,
    phase: Phase,
    loops: Vec<usize>,
    depth: usize,
    remaining: usize,
}

pub(super) fn expression(
    context: &mut Context<'_>,
    module: ModuleId,
    owner: DefId,
    expression: ast::ExprId,
    expected: TyId,
    bindings: &ConstBindings,
) -> Result<(Vec<Expr>, ExprId), Error> {
    let types = context.parameters(owner);
    let mut compiler = Compiler::new(context, module, owner, types, bindings, expected);
    let root = compiler.expression(expression, Some(expected))?;
    Ok((compiler.expressions, root))
}

pub(super) fn function(
    context: &mut Context<'_>,
    module: ModuleId,
    owner: DefId,
    source: &ast::Function,
    types: &HashMap<Symbol, TyId>,
) -> Result<Function, Error> {
    let Ty::Function { parameters, result } = context
        .program
        .types
        .get(context.definition(owner).ty)
        .clone()
    else {
        return Err(context.constant_error(owner, "const function has an invalid signature"));
    };
    let empty = ConstBindings::new();
    let mut compiler = Compiler::new(context, module, owner, types.clone(), &empty, result);
    compiler.check_scalar_signature(&parameters, result)?;
    for (parameter, &ty) in source.parameters.iter().zip(&parameters) {
        compiler.bind(parameter.name, ty, false, Init::Yes)?;
    }
    let (requires, ensures) = compiler.clauses(&source.clauses)?;
    compiler.phase = Phase::Body;
    let source_body = source.body.as_ref().expect("const source body checked");
    let (body, falls) = compiler.block(source_body)?;
    if falls && result != TyId::VOID {
        return Err(Error::new(
            "E-CONST-CONTEXT",
            "not every const function path returns a value",
            source_body.span,
        ));
    }
    Ok(Function {
        definition: owner,
        parameters,
        result,
        locals: compiler.locals,
        expressions: compiler.expressions,
        requires,
        ensures,
        body,
        span: source_body.span,
    })
}

impl<'a, 'b> Compiler<'a, 'b> {
    fn new(
        context: &'b mut Context<'a>,
        module: ModuleId,
        owner: DefId,
        types: HashMap<Symbol, TyId>,
        external: &'b ConstBindings,
        result: TyId,
    ) -> Self {
        Self {
            context,
            module,
            owner,
            types,
            external,
            scopes: vec![HashMap::new()],
            locals: Vec::new(),
            initialized: Vec::new(),
            constant_values: HashMap::new(),
            expressions: Vec::new(),
            result,
            phase: Phase::Body,
            loops: Vec::new(),
            depth: 0,
            remaining: 200_000,
        }
    }
    fn check_scalar_signature(&self, parameters: &[TyId], result: TyId) -> Result<(), Error> {
        let scalar = |ty| {
            matches!(
                self.context.program.types.get(ty),
                Ty::Integer { .. } | Ty::Bool | Ty::Char | Ty::Parameter { .. }
            )
        };
        if parameters.iter().all(|&ty| scalar(ty)) && (result == TyId::VOID || scalar(result)) {
            return Ok(());
        }
        Err(self.context.constant_error(
            self.owner,
            "const functions require integer, bool or char values and may return void",
        ))
    }
    fn clauses(&mut self, clauses: &[ast::Clause]) -> Result<(Vec<ExprId>, Vec<ExprId>), Error> {
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        for clause in clauses {
            self.phase = if clause.kind == ast::ClauseKind::Requires {
                Phase::Requires
            } else {
                Phase::Ensures
            };
            let expression = self.expression(clause.predicate, Some(TyId::BOOL))?;
            if self.phase == Phase::Requires {
                requires.push(expression);
            } else {
                ensures.push(expression);
            }
        }
        Ok((requires, ensures))
    }
    fn bind(&mut self, name: Name, ty: TyId, constant: bool, init: Init) -> Result<u32, Error> {
        let scope = self.scopes.last_mut().expect("const lexical scope");
        if scope.contains_key(&name.symbol) {
            return Err(Error::new(
                "E-NAME-DUPLICATE",
                "duplicate constant local binding",
                name.span,
            ));
        }
        let id = self.locals.len() as u32;
        self.locals.push(ty);
        self.initialized.push(init);
        scope.insert(name.symbol, Local { id, ty, constant });
        Ok(id)
    }
    fn local(&self, name: Symbol) -> Option<Local> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(&name).copied())
    }
    fn constant_bindings(&self) -> ConstBindings {
        let mut values = self.external.clone();
        for scope in &self.scopes {
            for (&name, local) in scope {
                values.insert(
                    name,
                    self.constant_values
                        .get(&local.id)
                        .cloned()
                        .unwrap_or(ConstBinding::Runtime),
                );
            }
        }
        values
    }
    fn constant_initializer(&mut self, variable: &ast::Variable, ty: TyId) -> Option<ConstBinding> {
        if !variable.constant {
            return None;
        }
        let initializer = variable.initializer?;
        let bindings = self.constant_bindings();
        if matches!(
            self.context.program.types.get(ty),
            Ty::Bool
                | Ty::Integer {
                    signed: false,
                    bits: 0
                }
        ) {
            self.context
                .const_expression(self.module, self.owner, initializer, ty, &bindings)
                .ok()
                .map(ConstBinding::Term)
        } else {
            self.context
                .eval_constant(self.module, self.owner, initializer, ty, &bindings)
                .ok()
                .map(ConstBinding::Value)
        }
    }
    fn add(&mut self, kind: ExprKind, ty: TyId, span: Span) -> ExprId {
        let id = ExprId(self.expressions.len() as u32);
        self.expressions.push(Expr { kind, ty, span });
        id
    }
    fn ty(&self, expression: ExprId) -> TyId {
        self.expressions[expression.0 as usize].ty
    }
    fn expect(&self, actual: TyId, expected: TyId, span: Span) -> Result<(), Error> {
        if actual == TyId::ERROR
            || expected == TyId::ERROR
            || !self.context.program.types.compatible(actual, expected)
        {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant expression has the wrong type for this context",
                span,
            ));
        }
        Ok(())
    }
    fn charge(&mut self, span: Span) -> Result<(), Error> {
        if self.remaining == 0 || self.depth >= 128 {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant typing exceeds its work or nesting limit",
                span,
            ));
        }
        self.remaining -= 1;
        Ok(())
    }
    fn resolve_type(&mut self, ty: ast::TypeId) -> Result<TyId, Error> {
        let bindings = self.constant_bindings();
        let value = self.context.resolve_type_with_bindings(
            ty,
            self.module,
            self.owner,
            &self.types,
            &bindings,
        );
        if value == TyId::ERROR {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "invalid type in constant expression",
                self.context.ast.ty(ty).span,
            ));
        }
        Ok(value)
    }
    fn merge(&mut self, before: &[Init], other: &[Init]) {
        for (index, &initial) in before.iter().enumerate() {
            self.initialized[index] = if initial == other[index] {
                initial
            } else {
                Init::Maybe
            };
        }
    }
}
