use super::*;
use crate::types::{GenericArg, GenericParamKind};

/// The receiver/environment is already evaluated exactly once. Generic seeds
/// are the inherited impl/trait/closure prefix, before method-local arguments.
pub(super) struct ResolvedCall {
    pub callee: ExprId,
    pub leading_arguments: Vec<ExprId>,
    pub generic_arguments: Vec<GenericArg>,
    pub prelude: Vec<StmtId>,
}

struct Invocation {
    callee: ExprId,
    owner: Option<DefId>,
    parameters: Vec<TyId>,
    result: TyId,
    inferred: Vec<Option<GenericArg>>,
    arguments: Vec<ExprId>,
    span: Span,
}

impl Body<'_, '_> {
    pub(super) fn call(
        &mut self,
        callee: ast::ExprId,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        expected: Option<TyId>,
        span: Span,
    ) -> ExprId {
        if self.in_contract
            && matches!(&self.context.ast.expr(callee).kind, A::Path(path)
            if path.len() == 1 && self.context.symbols.get(path[0].symbol) == "old")
        {
            return self.old_call(explicit, arguments, span);
        }
        if let Some(value) = self.method_call(callee, explicit, arguments, expected, span) {
            return value;
        }
        if let Some(value) = self.associated_call(callee, explicit, arguments, expected, span) {
            return value;
        }
        let callee = self
            .contextual_result_constructor(callee, expected)
            .unwrap_or_else(|| self.expression(callee, None));
        let target = self
            .closure_target(callee, span)
            .or_else(|| self.trait_callable_target(callee, span))
            .unwrap_or(ResolvedCall {
                callee,
                leading_arguments: Vec::new(),
                generic_arguments: Vec::new(),
                prelude: Vec::new(),
            });
        self.call_resolved(target, explicit, arguments, expected, span)
    }

    fn old_call(
        &mut self,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        span: Span,
    ) -> ExprId {
        if arguments.len() != 1 || !explicit.is_empty() {
            self.context
                .error("E-CALL-ARITY", "old requires exactly one argument", span);
            return self.add_expr(H::Error, TyId::ERROR, span);
        }
        let value = self.expression(arguments[0], None);
        self.add_expr(H::Old(value), self.ty(value), span)
    }

    pub(super) fn call_resolved(
        &mut self,
        target: ResolvedCall,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        expected: Option<TyId>,
        span: Span,
    ) -> ExprId {
        let Some(mut call) = self.invocation(target.callee, span) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        self.seed_call(&mut call, &target.generic_arguments, explicit, expected);
        let count = target.leading_arguments.len() + arguments.len();
        if call.parameters.len() != count {
            self.context.error(
                "E-CALL-ARITY",
                format!(
                    "expected {} arguments, found {count}",
                    call.parameters.len()
                ),
                span,
            );
        }
        for argument in target.leading_arguments {
            self.infer_argument(&mut call, argument);
        }
        for &argument in arguments {
            let hint = self.argument_hint(&call);
            let argument = self.expression(argument, hint);
            self.infer_argument(&mut call, argument);
        }
        let value = self.finish_call(call);
        if target.prelude.is_empty() {
            return value;
        }
        self.add_expr(
            H::BlockValue {
                body: hir::Block {
                    statements: target.prelude,
                    span,
                },
                value: Some(value),
            },
            self.ty(value),
            span,
        )
    }

    fn invocation(&mut self, callee: ExprId, span: Span) -> Option<Invocation> {
        let direct = self.direct_callee(callee);
        let signature = if let Some(owner) = direct {
            let ty = self.context.definition(owner).ty;
            self.context
                .program
                .types
                .instantiate_function_regions(ty, owner)
        } else {
            self.context.program.types.open_callable(self.ty(callee))
        };
        let Some(signature) = signature else {
            self.context.error(
                "E-REGION-LIMIT",
                "call region instantiation exceeds its resource limit",
                span,
            );
            return None;
        };
        let Ty::Function { parameters, result } = self.type_kind(signature) else {
            if signature != TyId::ERROR {
                self.context
                    .error("E-TYPE-CALL", "value is not callable", span);
            }
            return None;
        };
        let owner = direct.map(|id| match self.context.definition(id).kind {
            hir::DefinitionKind::Variant { parent, .. } => parent,
            _ => id,
        });
        let count = owner.map_or(0, |id| {
            self.context.definition(id).generic_parameter_kinds.len()
        });
        Some(Invocation {
            callee,
            owner,
            parameters: parameters.clone(),
            result: *result,
            inferred: vec![None; count],
            arguments: Vec::new(),
            span,
        })
    }

    fn direct_callee(&self, mut callee: ExprId) -> Option<DefId> {
        for _ in 0..128 {
            match self.expr(callee).kind {
                H::Group(inner) => callee = inner,
                H::Definition(definition) => return Some(definition),
                _ => return None,
            }
        }
        None
    }

    fn seed_call(
        &mut self,
        call: &mut Invocation,
        prefix: &[GenericArg],
        explicit: &[ast::GenericArg],
        expected: Option<TyId>,
    ) {
        let Some(owner) = call.owner else {
            if !explicit.is_empty() {
                self.context.error(
                    "E-TYPE-ARITY",
                    "indirect calls do not take generic arguments",
                    call.span,
                );
            }
            return;
        };
        let kinds = self
            .context
            .definition(owner)
            .generic_parameter_kinds
            .clone();
        for (slot, &kind) in call.inferred.iter_mut().zip(&kinds) {
            if kind == GenericParamKind::Lifetime {
                *slot = Some(GenericArg::Lifetime(
                    self.context.program.types.fresh_region(),
                ));
            }
        }
        if prefix.len() > kinds.len() {
            self.context.error(
                "E-TYPE-ARITY",
                "receiver has too many generic arguments",
                call.span,
            );
            return;
        }
        for (slot, value) in call.inferred.iter_mut().zip(prefix) {
            *slot = Some(*value);
        }
        if let Some(expected) = expected {
            self.infer_generic(call.result, expected, owner, &mut call.inferred, call.span);
        }
        self.explicit_call_arguments(call, &kinds, prefix.len(), explicit);
    }

    fn explicit_call_arguments(
        &mut self,
        call: &mut Invocation,
        kinds: &[GenericParamKind],
        prefix: usize,
        arguments: &[ast::GenericArg],
    ) {
        if arguments.is_empty() {
            return;
        }
        let all = kinds.len() - prefix;
        let slots: Vec<_> = (prefix..kinds.len())
            .filter(|&index| arguments.len() == all || kinds[index] != GenericParamKind::Lifetime)
            .collect();
        if slots.len() != arguments.len() {
            self.context.error(
                "E-TYPE-ARITY",
                format!(
                    "expected {} generic arguments, found {}",
                    slots.len(),
                    arguments.len()
                ),
                call.span,
            );
        }
        for (index, argument) in slots.into_iter().zip(arguments) {
            call.inferred[index] = self.resolve_explicit_generic(argument, kinds[index]);
        }
    }

    fn argument_hint(&mut self, call: &Invocation) -> Option<TyId> {
        let formal = *call.parameters.get(call.arguments.len())?;
        let Some(owner) = call.owner else {
            return Some(formal);
        };
        let arguments: Option<Vec<_>> = call.inferred.iter().copied().collect();
        Some(self.substitute_call_type(formal, owner, &arguments?, call.span))
    }

    fn infer_argument(&mut self, call: &mut Invocation, argument: ExprId) {
        if let (Some(&formal), Some(owner)) =
            (call.parameters.get(call.arguments.len()), call.owner)
        {
            self.infer_generic(
                formal,
                self.ty(argument),
                owner,
                &mut call.inferred,
                call.span,
            );
        }
        call.arguments.push(argument);
    }

    fn finish_call(&mut self, mut call: Invocation) -> ExprId {
        let Some(generics) = call.inferred.into_iter().collect::<Option<Vec<_>>>() else {
            self.context.error(
                "E-TYPE-INFER",
                "could not infer every generic argument",
                call.span,
            );
            return self.add_expr(H::Error, TyId::ERROR, call.span);
        };
        let mut parameter_types = Vec::with_capacity(call.parameters.len());
        for (argument, &formal) in call.arguments.iter_mut().zip(&call.parameters) {
            let expected = call.owner.map_or(formal, |owner| {
                self.substitute_call_type(formal, owner, &generics, call.span)
            });
            self.call_value_type(expected, call.span);
            *argument = self.coerce(*argument, expected);
            parameter_types.push(expected);
        }
        let result = call.owner.map_or(call.result, |owner| {
            self.substitute_call_type(call.result, owner, &generics, call.span)
        });
        self.call_value_type(result, call.span);
        if let Some(owner) = call.owner {
            self.context
                .check_generic_bounds(owner, &generics, call.span);
        }
        self.add_expr(
            H::Call {
                callee: call.callee,
                type_arguments: generics,
                arguments: call.arguments,
                parameter_types,
            },
            result,
            call.span,
        )
    }

    fn substitute_call_type(
        &mut self,
        ty: TyId,
        owner: DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> TyId {
        match self
            .context
            .program
            .types
            .substitute_generics(ty, owner, arguments)
        {
            Ok(ty) => match crate::ctfe::normalize_type_constants(
                &mut self.context.program,
                ty,
                crate::ctfe::Limits::default(),
            ) {
                Ok(ty) => ty,
                Err(error) => {
                    self.context.error(error.code, error.message, span);
                    TyId::ERROR
                }
            },
            Err(error) => {
                self.context.error("E-CONST-EVAL", error.to_string(), span);
                TyId::ERROR
            }
        }
    }

    fn call_value_type(&mut self, ty: TyId, span: Span) {
        if matches!(
            self.type_kind(ty),
            Ty::Str | Ty::Slice(_) | Ty::Dynamic { .. }
        ) {
            self.context.error(
                "E-TYPE-SIZED",
                "call arguments and results require a sized value type",
                span,
            );
        }
    }
}
