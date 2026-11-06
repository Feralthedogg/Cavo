//! Rejected admission returns an affine, callable environment. Its control
//! function remains private; retrying rechecks the original direct contract.
use super::*;

struct CaptureInvocation {
    function: DefId,
    receiver: TyId,
    result: TyId,
    parameters: Vec<TyId>,
    arguments: Vec<GenericArg>,
    callee_type: TyId,
    target: Option<DefId>,
}

impl Body<'_, '_> {
    pub(super) fn task_capture_invoker(&mut self, environment: DefId, child: ExprId, span: Span) {
        let Some(invocation) = self.capture_invocation(environment, child, span) else {
            return;
        };
        let CaptureInvocation {
            function,
            receiver,
            result,
            parameters,
            arguments,
            callee_type,
            target,
        } = invocation;
        let name = ast::Name {
            symbol: self.context.definition(self.definition).name,
            span,
        };
        let mut checker = Body::new(self.context, self.module, function, span);
        let local = checker.bind(name, receiver, true, Init::Initialized);
        checker.function.parameters.push(local);
        let base = checker.add_expr(H::Local(local), receiver, span);
        let callee = match target {
            Some(definition) => checker.add_expr(H::Definition(definition), callee_type, span),
            None => checker.add_expr(H::Field { base, index: 0 }, callee_type, span),
        };
        let call = capture_call(
            &mut checker,
            base,
            callee,
            parameters,
            arguments,
            result,
            span,
        );
        let returned = checker.add_stmt(S::Return(Some(call)), span);
        checker.function.body.statements.push(returned);
        checker.context.program.functions.push(checker.function);
        checker.context.program.closures.push(hir::Closure {
            environment,
            function,
            kind: hir::ClosureKind::FnOnce,
            adapters: Vec::new(),
        });
    }

    fn capture_type_arguments(
        &mut self,
        arguments: Vec<GenericArg>,
        own: &[GenericArg],
        span: Span,
    ) -> Option<Vec<GenericArg>> {
        let arguments = arguments
            .into_iter()
            .map(|argument| {
                self.context
                    .program
                    .types
                    .substitute_arg(argument, self.definition, own)
            })
            .collect::<Result<Vec<_>, _>>();
        match arguments {
            Ok(arguments) => Some(arguments),
            Err(error) => {
                self.context
                    .error("E-TASK-CAPTURE", error.to_string(), span);
                None
            }
        }
    }

    fn capture_invocation(
        &mut self,
        environment: DefId,
        child: ExprId,
        span: Span,
    ) -> Option<CaptureInvocation> {
        let H::Call {
            callee,
            type_arguments,
            parameter_types,
            ..
        } = self.expr(child).kind.clone()
        else {
            unreachable!("typed capture call");
        };
        let name = ast::Name {
            symbol: self.context.definition(self.definition).name,
            span,
        };
        let function = self.context.add_definition(
            name,
            self.module,
            hir::DefinitionKind::Function,
            ast::Visibility::Private,
            None,
        );
        self.inherit_closure_generics(function, span);
        let own = self.context.program.types.generic_arguments(function);
        let receiver = self.environment_type(environment, function);
        let result = self.closure_substitute(self.ty(child), self.definition, &own, span);
        let parameters = parameter_types
            .iter()
            .map(|&ty| self.closure_substitute(ty, self.definition, &own, span))
            .collect();
        let arguments = self.capture_type_arguments(type_arguments, &own, span)?;
        let callee_type = self.closure_substitute(self.ty(callee), self.definition, &own, span);
        let target = direct_target(&self.function, callee);
        self.context.program.definitions[function].ty =
            self.context.program.types.intern(Ty::Function {
                parameters: vec![receiver],
                result,
            });
        Some(CaptureInvocation {
            function,
            receiver,
            result,
            parameters,
            arguments,
            callee_type,
            target,
        })
    }
}

fn capture_call(
    checker: &mut Body<'_, '_>,
    base: ExprId,
    callee: ExprId,
    parameters: Vec<TyId>,
    type_arguments: Vec<GenericArg>,
    result: TyId,
    span: Span,
) -> ExprId {
    let arguments = parameters
        .iter()
        .enumerate()
        .map(|(index, &ty)| {
            let field = checker.add_expr(
                H::Field {
                    base,
                    index: index as u32 + 1,
                },
                ty,
                span,
            );
            checker.add_expr(
                H::Unary {
                    op: U::Move,
                    operand: field,
                },
                ty,
                span,
            )
        })
        .collect();
    checker.add_expr(
        H::Call {
            callee,
            arguments,
            type_arguments,
            parameter_types: parameters,
        },
        result,
        span,
    )
}

fn direct_target(function: &hir::Function, mut callee: ExprId) -> Option<DefId> {
    for _ in 0..128 {
        match function.expressions[callee].kind {
            H::Group(inner) => callee = inner,
            H::Definition(id) => return Some(id),
            _ => return None,
        }
    }
    None
}
