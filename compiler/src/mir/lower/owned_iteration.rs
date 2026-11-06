use super::*;

impl Builder<'_> {
    pub(super) fn owned_for_in(
        &mut self,
        binding: hir::LocalId,
        iterable: hir::ExprId,
        body: &hir::Block,
        span: Span,
    ) -> Result<(), LowerError> {
        let ty = self.source.expressions[iterable.0 as usize].ty;
        if !matches!(
            self.program.types.get(ty),
            Ty::Array { .. } | Ty::SymbolicArray { .. }
        ) {
            return self.fail(
                span,
                "consuming iteration requires an owned array, not borrowed elements",
            );
        }
        self.enter(span)?;
        let iterator = self.local(ty, LocalKind::ArrayIterator, None, span)?;
        let value = self.eval(iterable)?;
        self.emit(StatementKind::IteratorStart { iterator, value }, span);
        let header = self.new_block(span, None)?;
        let entered = self.new_block(span, None)?;
        let exit = self.new_block(span, None)?;
        self.goto(header);
        self.current = Some(header);
        let depth = self.scopes.len();
        self.enter(span)?;
        let destination = self.source_local(binding, LocalKind::Source)?;
        let exhausted = self.cleanup_to(depth - 1, exit, ExitKind::Normal)?;
        self.terminate(Terminator::IteratorNext {
            iterator,
            destination: Place::local(destination),
            some: entered,
            none: exhausted,
        });
        self.loops.push(Loop {
            exit,
            update: header,
            depth,
        });
        self.current = Some(entered);
        self.block(body)?;
        self.leave(span)?;
        self.goto(header);
        self.loops.pop();
        self.scopes.pop();
        self.current = Some(exit);
        Ok(())
    }
}
