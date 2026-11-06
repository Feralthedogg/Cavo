use super::*;
use crate::sema::constants::ConstBinding;
use crate::{
    syntax::ast::{BinaryOp, ExprKind as A, LiteralKind, UnaryOp},
    types::{ConstError, ConstKind, ConstTerm, ConstValue},
};

impl Context<'_> {
    pub(in crate::sema) fn const_expression(
        &mut self,
        module: ModuleId,
        owner: DefId,
        expression: ast::ExprId,
        expected: TyId,
        bindings: &ConstBindings,
    ) -> Result<ConstId, ctfe::Error> {
        if !dependent(self, owner, expression, bindings)? {
            let value = self.eval_constant(module, owner, expression, expected, bindings)?;
            return constant_value(self, value, self.ast.expr(expression).span);
        }
        let mut compiler = Terms {
            context: self,
            module,
            owner,
            bindings,
            remaining: 4096,
        };
        let id = compiler.expression(expression, Some(expected), 0)?;
        compiler
            .context
            .program
            .types
            .normalize_const(id)
            .map_err(|error| constant_error(error, compiler.context.ast.expr(expression).span))
    }

    pub(in crate::sema) fn const_path(
        &mut self,
        module: ModuleId,
        owner: DefId,
        path: &[Name],
        bindings: &ConstBindings,
        span: Span,
    ) -> Result<ConstId, ctfe::Error> {
        let value = self.const_path_term(module, owner, path, bindings, span)?;
        if let ConstKind::Global(definition) = self.program.types.const_term(value).kind {
            let value = self.constant_value(definition)?;
            return constant_value(self, value, span);
        }
        Ok(value)
    }

    fn const_path_term(
        &mut self,
        module: ModuleId,
        owner: DefId,
        path: &[Name],
        bindings: &ConstBindings,
        span: Span,
    ) -> Result<ConstId, ctfe::Error> {
        if path.len() == 1 {
            if let Some(binding) = bindings.get(&path[0].symbol) {
                return match binding {
                    ConstBinding::Value(value) => constant_value(self, value.clone(), span),
                    ConstBinding::Term(id) => Ok(*id),
                    ConstBinding::Runtime => Err(ctfe::Error::new(
                        "E-CONST-CONTEXT",
                        "runtime local is not a compile-time constant",
                        span,
                    )),
                };
            }
            if let Some(index) = parameter_slot(self, owner, path[0].symbol) {
                return Ok(self.program.types.const_parameter(owner, index as u32));
            }
        }
        if let Some(value) = self.integer_constant(path, span)? {
            return constant_value(self, value, span);
        }
        let definition = self
            .resolve(module, path)
            .ok_or_else(|| ctfe::Error::new("E-CONST-CONTEXT", "unresolved constant name", span))?;
        let ty = self.constant_type(definition)?;
        self.program
            .types
            .intern_const(ConstTerm {
                ty,
                kind: ConstKind::Global(definition),
            })
            .map_err(|error| constant_error(error, span))
    }

    pub(in crate::sema) fn const_length(
        &mut self,
        module: ModuleId,
        owner: DefId,
        expression: ast::ExprId,
        bindings: &ConstBindings,
    ) -> Result<ConstId, ctfe::Error> {
        let ty = self.program.types.builtin("usize").expect("usize type");
        self.const_expression(module, owner, expression, ty, bindings)
    }

    pub(in crate::sema) fn assertion_message(
        &self,
        expression: ast::ExprId,
    ) -> Result<String, ctfe::Error> {
        let expression = self.ast.expr(expression);
        if !matches!(expression.kind, A::Literal(LiteralKind::String)) {
            return Err(ctfe::Error::new(
                "E-CONST-ASSERT",
                "static_assert message must be a string literal",
                expression.span,
            ));
        }
        let text = self
            .sources
            .file(expression.span.file)
            .slice(expression.span);
        literal::decode_quoted(text).ok_or_else(|| {
            ctfe::Error::new(
                "E-CONST-ASSERT",
                "invalid static_assert message string",
                expression.span,
            )
        })
    }

    pub(in crate::sema) fn check_static_assert(
        &mut self,
        assertion: &ast::StaticAssert,
        module: ModuleId,
        owner: DefId,
        bindings: &ConstBindings,
    ) -> Result<(), ctfe::Error> {
        let message = assertion
            .message
            .map(|value| self.assertion_message(value))
            .transpose()?
            .unwrap_or_else(|| "static assertion failed".into());
        let condition =
            self.const_expression(module, owner, assertion.condition, TyId::BOOL, bindings)?;
        match self.program.types.const_term(condition).kind {
            ConstKind::Value(ConstValue::Bool(true)) => Ok(()),
            ConstKind::Value(ConstValue::Bool(false)) => {
                Err(ctfe::Error::new("E-CONST-ASSERT", message, assertion.span))
            }
            _ => {
                if !self
                    .constant_assertions
                    .insert((owner, condition, assertion.span))
                {
                    return Ok(());
                }
                self.program.constants.assertions.push(ctfe::Assertion {
                    owner,
                    condition,
                    message,
                    span: assertion.span,
                });
                Ok(())
            }
        }
    }
}

fn parameter_slot(context: &Context<'_>, owner: DefId, symbol: Symbol) -> Option<usize> {
    context
        .program
        .types
        .generic_parameters(owner)
        .iter()
        .position(|&(name, kind)| name == symbol && kind == GenericParamKind::Const)
}

fn dependent(
    context: &Context<'_>,
    owner: DefId,
    root: ast::ExprId,
    bindings: &ConstBindings,
) -> Result<bool, ctfe::Error> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > 4096 {
            return Err(ctfe::Error::new(
                "E-CONST-LIMIT",
                "constant dependency query exceeds its work limit",
                context.ast.expr(root).span,
            ));
        }
        match &context.ast.expr(id).kind {
            A::Path(path) if path.len() == 1 => {
                if matches!(bindings.get(&path[0].symbol), Some(ConstBinding::Term(_))) {
                    return Ok(true);
                }
                if !bindings.contains_key(&path[0].symbol)
                    && parameter_slot(context, owner, path[0].symbol).is_some()
                {
                    return Ok(true);
                }
            }
            A::Group(value) | A::Unary { operand: value, .. } => pending.push(*value),
            A::Binary { left, right, .. } => {
                pending.push(*left);
                pending.push(*right);
            }
            A::Call {
                arguments,
                type_arguments,
                ..
            } => {
                pending.extend(arguments);
                if generic_dependency(context, owner, type_arguments, bindings) {
                    return Ok(true);
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

fn generic_dependency(
    context: &Context<'_>,
    owner: DefId,
    arguments: &[ast::GenericArg],
    bindings: &ConstBindings,
) -> bool {
    arguments.iter().any(|arg| match arg {
        ast::GenericArg::Path(path) if path.len() == 1 => {
            matches!(bindings.get(&path[0].symbol), Some(ConstBinding::Term(_)))
                || !bindings.contains_key(&path[0].symbol)
                    && parameter_slot(context, owner, path[0].symbol).is_some()
        }
        _ => false,
    })
}

struct ConstCall {
    definition: DefId,
    type_arguments: Vec<GenericArg>,
    parameters: Vec<TyId>,
    result: TyId,
}

struct Terms<'a, 'b> {
    context: &'a mut Context<'b>,
    module: ModuleId,
    owner: DefId,
    bindings: &'a ConstBindings,
    remaining: usize,
}
impl Terms<'_, '_> {
    fn expression(
        &mut self,
        id: ast::ExprId,
        expected: Option<TyId>,
        depth: usize,
    ) -> Result<ConstId, ctfe::Error> {
        let expression = self.context.ast.expr(id);
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or_else(|| constant_error(ConstError::Limit, expression.span))?;
        if depth >= 128 {
            return Err(constant_error(ConstError::Limit, expression.span));
        }
        let value = match &expression.kind {
            A::Literal(kind) => self.literal(*kind, expression.span, expected)?,
            A::Path(path) => self.context.const_path_term(
                self.module,
                self.owner,
                path,
                self.bindings,
                expression.span,
            )?,
            A::Group(value) => self.expression(*value, expected, depth + 1)?,
            A::Unary { op, operand } => {
                self.unary(*op, *operand, expected, expression.span, depth + 1)?
            }
            A::Binary { op, left, right } => {
                self.binary(*op, *left, *right, expression.span, depth + 1)?
            }
            A::Call {
                callee,
                type_arguments,
                arguments,
            } => self.call(
                *callee,
                type_arguments,
                arguments,
                expression.span,
                depth + 1,
            )?,
            _ => {
                return Err(ctfe::Error::new(
                    "E-CONST-CONTEXT",
                    "this dependent expression is outside the constant expression subset",
                    expression.span,
                ));
            }
        };
        if let Some(expected) = expected
            && self.context.program.types.const_term(value).ty != expected
        {
            return Err(ctfe::Error::new(
                "E-CONST-CONTEXT",
                "constant expression has the wrong scalar type",
                expression.span,
            ));
        }
        Ok(value)
    }

    fn literal(
        &mut self,
        kind: LiteralKind,
        span: Span,
        expected: Option<TyId>,
    ) -> Result<ConstId, ctfe::Error> {
        let expected = expected.unwrap_or_else(|| {
            if matches!(kind, LiteralKind::Bool(_)) {
                TyId::BOOL
            } else {
                self.context
                    .program
                    .types
                    .builtin("usize")
                    .expect("usize type")
            }
        });
        let text = self.context.sources.file(span.file).slice(span);
        let (ty, value) = literal::check(
            text,
            kind,
            Some(expected),
            false,
            span,
            &mut self.context.program.types,
            self.context.diagnostics,
        );
        if ty != expected {
            return Err(ctfe::Error::new(
                "E-CONST-CONTEXT",
                "constant literal does not match the required type",
                span,
            ));
        }
        let value = ctfe::Value::from_scalar(ty, value).ok_or_else(|| {
            ctfe::Error::new(
                "E-CONST-CONTEXT",
                "literal cannot be used in a generic constant",
                span,
            )
        })?;
        constant_value(self.context, value, span)
    }

    fn unary(
        &mut self,
        op: UnaryOp,
        operand: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
        depth: usize,
    ) -> Result<ConstId, ctfe::Error> {
        let operand = self.expression(operand, expected, depth)?;
        let ty = self.context.program.types.const_term(operand).ty;
        self.context
            .program
            .types
            .intern_const(ConstTerm {
                ty,
                kind: ConstKind::Unary { op, operand },
            })
            .map_err(|error| constant_error(error, span))
    }

    fn binary(
        &mut self,
        op: BinaryOp,
        left: ast::ExprId,
        right: ast::ExprId,
        span: Span,
        depth: usize,
    ) -> Result<ConstId, ctfe::Error> {
        let logical = matches!(op, BinaryOp::And | BinaryOp::Or);
        let left = self.expression(left, logical.then_some(TyId::BOOL), depth)?;
        let operand_type = self.context.program.types.const_term(left).ty;
        let right = self.expression(right, Some(operand_type), depth)?;
        let comparison = matches!(
            op,
            BinaryOp::Equal
                | BinaryOp::NotEqual
                | BinaryOp::Less
                | BinaryOp::LessEqual
                | BinaryOp::Greater
                | BinaryOp::GreaterEqual
        );
        let ty = if comparison { TyId::BOOL } else { operand_type };
        self.context
            .program
            .types
            .intern_const(ConstTerm {
                ty,
                kind: ConstKind::Binary { op, left, right },
            })
            .map_err(|error| constant_error(error, span))
    }

    fn call(
        &mut self,
        callee: ast::ExprId,
        syntax: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        span: Span,
        depth: usize,
    ) -> Result<ConstId, ctfe::Error> {
        let ConstCall {
            definition,
            type_arguments,
            parameters,
            result,
        } = self.callee(callee, syntax, span)?;
        if arguments.len() != parameters.len() {
            return Err(ctfe::Error::new(
                "E-CALL-ARITY",
                "constant call argument count mismatch",
                span,
            ));
        }
        let arguments = arguments
            .iter()
            .zip(parameters)
            .map(|(&value, ty)| self.expression(value, Some(ty), depth))
            .collect::<Result<_, _>>()?;
        self.context
            .program
            .types
            .intern_const(ConstTerm {
                ty: result,
                kind: ConstKind::Call {
                    definition,
                    type_arguments,
                    arguments,
                },
            })
            .map_err(|error| constant_error(error, span))
    }
    fn callee(
        &mut self,
        callee: ast::ExprId,
        syntax: &[ast::GenericArg],
        span: Span,
    ) -> Result<ConstCall, ctfe::Error> {
        let A::Path(path) = &self.context.ast.expr(callee).kind else {
            return Err(ctfe::Error::new(
                "E-CONST-CONTEXT",
                "constant calls require a direct source function",
                span,
            ));
        };
        let definition = self.context.resolve(self.module, path).ok_or_else(|| {
            ctfe::Error::new("E-CONST-CONTEXT", "unresolved constant function", span)
        })?;
        let signature = self.context.const_function_type(definition)?;
        let parameters = self.context.parameters(self.owner);
        let scope = TypeScope {
            module: self.module,
            owner: self.owner,
            parameters: &parameters,
        };
        let type_arguments = self.context.resolve_generic_arguments(
            definition,
            syntax,
            scope,
            self.bindings,
            span,
        )?;
        let signature = self
            .context
            .program
            .types
            .substitute_generics(signature, definition, &type_arguments)
            .map_err(|error| constant_error(error, span))?;
        let Ty::Function { parameters, result } = self.context.program.types.get(signature).clone()
        else {
            return Err(ctfe::Error::new(
                "E-CONST-CONTEXT",
                "constant call target is not a function",
                span,
            ));
        };
        Ok(ConstCall {
            definition,
            type_arguments,
            parameters,
            result,
        })
    }
}

fn constant_value(
    context: &mut Context<'_>,
    value: ctfe::Value,
    span: Span,
) -> Result<ConstId, ctfe::Error> {
    if value.ty == TyId::BOOL {
        return value
            .boolean()
            .map(|value| context.program.types.const_bool(value))
            .ok_or_else(|| constant_error(ConstError::Kind, span));
    }
    if !matches!(
        context.program.types.get(value.ty),
        Ty::Integer {
            signed: false,
            bits: 0
        }
    ) {
        return Err(ctfe::Error::new(
            "E-CONST-CONTEXT",
            "generic constants require usize or bool",
            span,
        ));
    }
    value
        .usize_value()
        .map(|value| context.program.types.const_value(value))
        .ok_or_else(|| constant_error(ConstError::Overflow, span))
}

fn constant_error(error: ConstError, span: Span) -> ctfe::Error {
    let code = match error {
        ConstError::Limit => "E-CONST-LIMIT",
        ConstError::Kind | ConstError::InvalidId | ConstError::Unresolved => "E-CONST-CONTEXT",
        _ => "E-CONST-EVAL",
    };
    ctfe::Error::new(code, error.to_string(), span)
}
