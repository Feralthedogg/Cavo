use super::*;

struct Iteration {
    base: Place,
    index: LocalId,
    length: LocalId,
    usize_ty: TyId,
}

impl Builder<'_> {
    pub(super) fn for_in(
        &mut self,
        local: hir::LocalId,
        iterable: hir::ExprId,
        body: &hir::Block,
        span: Span,
    ) -> Result<(), LowerError> {
        let element = self.source.locals[local].ty;
        let iterable_ty = self.source.expressions[iterable].ty;
        if !self.properties.get(element).copy || !self.properties.get(iterable_ty).copy {
            return self.owned_for_in(local, iterable, body, span);
        }
        self.enter(span)?;
        let iteration = self.iteration_values(iterable, span)?;
        let header = self.new_block(span, None)?;
        let entered = self.new_block(span, None)?;
        let updated = self.new_block(span, None)?;
        let exit = self.new_block(span, None)?;
        let stopped = self.cleanup_to(self.scopes.len() - 1, exit, ExitKind::Normal)?;
        self.goto(header);
        self.current = Some(header);
        self.iteration_condition(&iteration, entered, stopped, span)?;
        self.loops.push(Loop {
            exit,
            update: updated,
            depth: self.scopes.len(),
        });
        self.current = Some(entered);
        self.enter(span)?;
        self.iteration_binding(&iteration, local, span)?;
        self.block(body)?;
        self.leave(span)?;
        self.goto(updated);
        self.current = Some(updated);
        self.iteration_advance(&iteration, span)?;
        self.goto(header);
        self.loops.pop();
        self.scopes.pop();
        self.current = Some(exit);
        Ok(())
    }

    fn iteration_values(
        &mut self,
        iterable: hir::ExprId,
        span: Span,
    ) -> Result<Iteration, LowerError> {
        let ty = self.source.expressions[iterable].ty;
        if !self.properties.get(ty).copy {
            return self.fail(
                span,
                "MIR iteration of a non-Copy iterable is not implemented",
            );
        }
        // A value array is snapshotted, while a reference keeps its original
        // pointee. In either case evaluation and handle capture occur only once.
        // `eval` already snapshots place reads and call results into a temporary
        // in this scope. Reuse it instead of copying a whole array a second time.
        let Operand::Copy(owner) = self.eval(iterable)? else {
            return self.fail(span, "MIR iterable has no stable Copy value");
        };
        let (base, ty) = match self.program.types.get(ty) {
            Ty::Reference { inner, .. } => (owner.project(Projection::Deref), *inner),
            _ => (owner, ty),
        };
        if !matches!(
            self.program.types.get(ty),
            Ty::Array { .. } | Ty::SymbolicArray { .. } | Ty::Slice(_)
        ) {
            return self.fail(span, "MIR iteration requires an array or slice");
        }
        let base = self.capture(base, ty, span)?;
        let usize_ty = self.usize_ty;
        let index = self.local(usize_ty, LocalKind::Temporary, None, span)?;
        self.assign(Place::local(index), Rvalue::Use(integer(0, usize_ty)), span);
        let length = self.local(usize_ty, LocalKind::Temporary, None, span)?;
        self.assign(Place::local(length), Rvalue::Length(base.clone()), span);
        Ok(Iteration {
            base,
            index,
            length,
            usize_ty,
        })
    }

    fn iteration_condition(
        &mut self,
        iteration: &Iteration,
        yes: BlockId,
        no: BlockId,
        span: Span,
    ) -> Result<(), LowerError> {
        self.enter(span)?;
        let condition = self.materialize(
            TyId::BOOL,
            Rvalue::Binary {
                op: BinaryOp::Less,
                left: Operand::Copy(Place::local(iteration.index)),
                right: Operand::Copy(Place::local(iteration.length)),
            },
            span,
        )?;
        let yes = self.cleanup_to(self.scopes.len() - 1, yes, ExitKind::Normal)?;
        let no = self.cleanup_to(self.scopes.len() - 1, no, ExitKind::Normal)?;
        self.terminate(Terminator::Switch { condition, yes, no });
        self.scopes.pop();
        Ok(())
    }

    fn iteration_binding(
        &mut self,
        iteration: &Iteration,
        binding: hir::LocalId,
        span: Span,
    ) -> Result<(), LowerError> {
        let local = self.source_local(binding, LocalKind::Source)?;
        let normal = self.new_block(span, None)?;
        self.terminate(Terminator::Bounds {
            base: iteration.base.clone(),
            index: iteration.index,
            normal,
            trap: self.abort,
        });
        self.current = Some(normal);
        let element = iteration
            .base
            .clone()
            .project(Projection::Index(iteration.index));
        self.assign(
            Place::local(local),
            Rvalue::Use(Operand::Copy(element)),
            span,
        );
        Ok(())
    }

    fn iteration_advance(&mut self, iteration: &Iteration, span: Span) -> Result<(), LowerError> {
        self.enter(span)?;
        // Reaching the body required index < length <= usize::MAX. Even its
        // last advance is at most usize::MAX; an exhausted iterator never adds.
        let value = self.operation(
            iteration.usize_ty,
            Rvalue::Binary {
                op: BinaryOp::Add,
                left: Operand::Copy(Place::local(iteration.index)),
                right: integer(1, iteration.usize_ty),
            },
            span,
        )?;
        self.assign(Place::local(iteration.index), Rvalue::Use(value), span);
        self.leave(span)
    }
}

fn integer(value: u128, ty: TyId) -> Operand {
    Operand::Constant {
        value: hir::Constant::Integer {
            magnitude: value,
            negative: false,
        },
        ty,
    }
}
