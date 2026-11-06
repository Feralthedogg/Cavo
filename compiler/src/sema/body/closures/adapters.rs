use super::*;

struct Entry {
    parameters: Vec<(Symbol, TyId)>,
    result: TyId,
}

impl Body<'_, '_> {
    pub(super) fn closure_adapters(
        &mut self,
        declaration: &Declaration,
        kind: ClosureKind,
        span: Span,
    ) -> Vec<(ClosureKind, DefId)> {
        let function = self
            .context
            .program
            .functions
            .last()
            .expect("published closure body");
        debug_assert_eq!(function.definition, declaration.function);
        let entry = Entry {
            parameters: function
                .parameters
                .iter()
                .skip(1)
                .map(|local| {
                    let local = &function.locals[local.0 as usize];
                    (local.name, local.ty)
                })
                .collect(),
            result: function.result,
        };
        let mut adapters = Vec::new();
        for requested in [ClosureKind::FnMut, ClosureKind::FnOnce] {
            if kind < requested {
                let definition = self.closure_adapter(declaration, kind, requested, &entry, span);
                adapters.push((requested, definition));
            }
        }
        adapters
    }

    fn closure_adapter(
        &mut self,
        declaration: &Declaration,
        source: ClosureKind,
        requested: ClosureKind,
        entry: &Entry,
        span: Span,
    ) -> DefId {
        let name = ast::Name {
            symbol: self.context.definition(self.definition).name,
            span,
        };
        let owner = self.context.add_definition(
            name,
            self.module,
            hir::DefinitionKind::Function,
            ast::Visibility::Private,
            None,
        );
        self.inherit_closure_generics(owner, span);
        let placeholder = self.context.program.types.intern(Ty::Function {
            parameters: Vec::new(),
            result: TyId::VOID,
        });
        self.context.program.definitions[owner.0 as usize].ty = placeholder;
        let mut checker = Body::new(self.context, self.module, owner, span);
        let arguments = checker.context.program.types.generic_arguments(owner);
        checker.function.result =
            checker.closure_substitute(entry.result, declaration.function, &arguments, span);
        let environment = checker.environment_type(declaration.environment, owner);
        checker.adapter_parameters(
            entry,
            declaration.function,
            &arguments,
            environment,
            requested,
        );
        let receiver = checker.adapter_receiver(environment, source, requested, span);
        let values = checker.adapter_arguments(receiver, span);
        let callee = checker.adapter_callee(declaration.function, span);
        let target = ResolvedCall {
            callee,
            leading_arguments: values,
            generic_arguments: arguments,
            prelude: Vec::new(),
        };
        let value = checker.call_resolved(target, &[], &[], Some(checker.function.result), span);
        let returned = checker.add_stmt(S::Return(Some(value)), span);
        checker.function.body.statements.push(returned);
        let parameters = checker
            .function
            .parameters
            .iter()
            .map(|local| checker.function.locals[local.0 as usize].ty)
            .collect();
        let signature = checker.context.program.types.intern(Ty::Function {
            parameters,
            result: checker.function.result,
        });
        checker.context.program.definitions[owner.0 as usize].ty = signature;
        let function = checker.function;
        self.context.program.functions.push(function);
        owner
    }

    fn adapter_parameters(
        &mut self,
        entry: &Entry,
        source: DefId,
        arguments: &[GenericArg],
        environment: TyId,
        requested: ClosureKind,
    ) {
        let span = self.function.body.span;
        let receiver = if requested == ClosureKind::FnOnce {
            environment
        } else {
            let region = self.context.program.types.fresh_region();
            self.context.program.types.intern(Ty::Reference {
                region,
                mutable: true,
                inner: environment,
            })
        };
        let name = self.context.definition(self.definition).name;
        self.adapter_parameter(name, receiver, span);
        for &(name, ty) in &entry.parameters {
            let ty = self.closure_substitute(ty, source, arguments, span);
            self.adapter_parameter(name, ty, span);
        }
    }

    fn adapter_parameter(&mut self, name: Symbol, ty: TyId, span: Span) {
        let local = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(hir::Local {
            name,
            ty,
            mutable: true,
            span,
        });
        self.function.parameters.push(local);
        self.states.push(Init::Initialized);
    }

    fn adapter_receiver(
        &mut self,
        environment: TyId,
        source: ClosureKind,
        requested: ClosureKind,
        span: Span,
    ) -> ExprId {
        let ty = self.function.locals[0].ty;
        let receiver = self.add_expr(H::Local(LocalId(0)), ty, span);
        let place = if requested == ClosureKind::FnOnce {
            receiver
        } else {
            self.add_expr(
                H::Unary {
                    op: U::Dereference,
                    operand: receiver,
                },
                environment,
                span,
            )
        };
        let mutable = source == ClosureKind::FnMut;
        let region = self.context.program.types.fresh_region();
        let ty = self.context.program.types.intern(Ty::Reference {
            region,
            mutable,
            inner: environment,
        });
        self.add_expr(
            H::Unary {
                op: if mutable { U::BorrowMut } else { U::Borrow },
                operand: place,
            },
            ty,
            span,
        )
    }

    fn adapter_arguments(&mut self, receiver: ExprId, span: Span) -> Vec<ExprId> {
        let mut arguments = vec![receiver];
        for index in 1..self.function.parameters.len() {
            let local = self.function.parameters[index];
            let ty = self.function.locals[local.0 as usize].ty;
            let operand = self.add_expr(H::Local(local), ty, span);
            arguments.push(self.add_expr(
                H::Unary {
                    op: U::Move,
                    operand,
                },
                ty,
                span,
            ));
        }
        arguments
    }

    fn adapter_callee(&mut self, definition: DefId, span: Span) -> ExprId {
        let signature = self.context.definition(definition).ty;
        let ty = self
            .context
            .program
            .types
            .generalize_callable(signature, definition)
            .unwrap_or_else(|| {
                self.context.error(
                    "E-CLOSURE-TYPE",
                    "closure adapter generalization exceeds its limit",
                    span,
                );
                TyId::ERROR
            });
        self.add_expr(H::Definition(definition), ty, span)
    }
}
