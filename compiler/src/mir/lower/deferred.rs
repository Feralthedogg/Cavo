use super::*;

impl Builder<'_> {
    pub(super) fn register_defer(
        &mut self,
        id: hir::StmtId,
        captures: &[(hir::LocalId, hir::ExprId)],
        span: Span,
    ) -> Result<(), LowerError> {
        for &(capture, initializer) in captures {
            let local = self.source_local(capture, LocalKind::Source)?;
            self.enter(span)?;
            let value = self.eval(initializer)?;
            self.assign(Place::local(local), Rvalue::Use(value), span);
            self.leave(span)?;
        }
        self.scopes
            .last_mut()
            .expect("defer scope")
            .registrations
            .push(Registration::Defer(id));
        Ok(())
    }

    pub(super) fn cleanup_registration(
        &mut self,
        registration: Registration,
        next: BlockId,
        reason: ExitKind,
    ) -> Result<BlockId, LowerError> {
        match registration {
            Registration::Defer(id) => self.cleanup_action(Cleanup::Defer(id), next, reason),
            Registration::Local(local) => {
                let dead = self.cleanup_action(Cleanup::Dead(local), next, reason)?;
                if self.body.local(local).kind == LocalKind::Address {
                    return Ok(dead);
                }
                self.cleanup_action(Cleanup::Drop(local), dead, reason)
            }
        }
    }

    pub(super) fn emit_deferred(
        &mut self,
        id: hir::StmtId,
        next: BlockId,
        reason: ExitKind,
    ) -> Result<BlockId, LowerError> {
        let S::Defer { body, .. } = &self.source.statements[id].kind else {
            return self.fail(
                self.source.body.span,
                "cleanup registration is not a defer body",
            );
        };
        let (owner, registration) = self
            .scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(scope, active)| {
                active
                    .registrations
                    .iter()
                    .position(|entry| matches!(entry, Registration::Defer(found) if *found == id))
                    .map(|index| (scope, index))
            })
            .expect("active defer registration");
        let first = self.body.blocks.len();
        let entry = self.new_block(body.span, Some(reason))?;
        let current = self.current.replace(entry);
        // Inner scopes and later registrations have already been cleaned when
        // this action executes. Lower under that runtime lexical prefix.
        let inner = self.scopes.split_off(owner + 1);
        let later = self.scopes[owner].registrations.split_off(registration);
        self.cleanup_depth += 1;
        let result = self.block(body);
        self.cleanup_depth -= 1;
        if result.is_ok() {
            self.goto(next);
        }
        self.scopes.truncate(owner + 1);
        self.scopes[owner].registrations.extend(later);
        self.scopes.extend(inner);
        self.current = current;
        result?;
        // Even an ordinary lexical block inside deferred code executes under
        // cleanup's bounded, non-suspending contract and fatal failure policy.
        for block in &mut self.body.blocks[first..] {
            block.cleanup = Some(reason);
        }
        Ok(entry)
    }
}
