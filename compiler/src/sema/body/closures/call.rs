use super::*;

impl Body<'_, '_> {
    pub(in crate::sema::body) fn closure_target(
        &mut self,
        callee: ExprId,
        span: Span,
    ) -> Option<ResolvedCall> {
        let (environment, borrowed) = match *self.type_kind(self.ty(callee)) {
            Ty::Reference { inner, mutable, .. } => (inner, Some(mutable)),
            _ => (self.ty(callee), None),
        };
        let Ty::Named {
            definition,
            arguments,
        } = self.type_kind(environment)
        else {
            return None;
        };
        let closure = self
            .context
            .program
            .closures
            .iter()
            .find(|closure| closure.environment == *definition)?
            .clone();
        let generic_arguments = arguments.clone();
        let mut prelude = Vec::new();
        let receiver = self.closure_receiver(
            callee,
            environment,
            borrowed,
            closure.kind,
            &mut prelude,
            span,
        );
        let signature = self.context.definition(closure.function).ty;
        let signature = self
            .context
            .program
            .types
            .generalize_callable(signature, closure.function)
            .unwrap_or_else(|| {
                self.context.error(
                    "E-CLOSURE-TYPE",
                    "closure callable generalization exceeds its limit",
                    span,
                );
                TyId::ERROR
            });
        let callee = self.add_expr(H::Definition(closure.function), signature, span);
        Some(ResolvedCall {
            callee,
            leading_arguments: vec![receiver],
            generic_arguments,
            prelude,
        })
    }

    fn closure_receiver(
        &mut self,
        callee: ExprId,
        environment: TyId,
        borrowed: Option<bool>,
        kind: ClosureKind,
        prelude: &mut Vec<StmtId>,
        span: Span,
    ) -> ExprId {
        if kind == ClosureKind::FnOnce {
            if borrowed.is_some() || self.closure_place(callee) {
                report(self.context.diagnostics, Diagnostic::error("E-CLOSURE-MOVE", "calling this closure consumes its environment", span)
                    .help("call a stored closure as `(move closure)(...)`; a borrowed closure cannot be consumed"));
            }
            return callee;
        }
        let place = if borrowed.is_some() {
            self.add_expr(
                H::Unary {
                    op: U::Dereference,
                    operand: callee,
                },
                environment,
                span,
            )
        } else if self.closure_place(callee) {
            callee
        } else {
            self.closure_temporary(callee, environment, prelude, span)
        };
        let mutable = kind == ClosureKind::FnMut;
        if mutable && !self.mutable_place(place) {
            self.context.error(
                "E-CLOSURE-MUTABLE",
                "calling this closure requires a mutable environment",
                span,
            );
        }
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

    fn closure_temporary(
        &mut self,
        value: ExprId,
        ty: TyId,
        prelude: &mut Vec<StmtId>,
        span: Span,
    ) -> ExprId {
        let local = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(hir::Local {
            name: self.context.definition(self.definition).name,
            ty,
            mutable: true,
            span,
        });
        self.states.push(Init::Initialized);
        prelude.push(self.add_stmt(
            S::Declare {
                local,
                initializer: Some(value),
            },
            span,
        ));
        self.add_expr(H::Local(local), ty, span)
    }

    fn closure_place(&self, mut expression: ExprId) -> bool {
        for _ in 0..256 {
            match self.expr(expression).kind {
                H::Group(inner) => expression = inner,
                H::Local(_)
                | H::Field { .. }
                | H::Index { .. }
                | H::Unary {
                    op: U::Dereference, ..
                } => return true,
                _ => return false,
            }
        }
        false
    }
}
