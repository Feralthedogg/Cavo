use super::*;
use crate::hir::{BindingMode, Pattern, PatternKind};

struct Binding {
    local: hir::LocalId,
    mode: BindingMode,
    place: Place,
    span: Span,
}

impl Builder<'_> {
    pub(super) fn match_value(
        &mut self,
        subject: hir::ExprId,
        temporary: hir::LocalId,
        arms: &[hir::MatchArm],
        ty: TyId,
        span: Span,
    ) -> Result<Operand, LowerError> {
        let result = self.local(ty, LocalKind::Temporary, None, span)?;
        self.enter(span)?;
        let owner = self.source_local(temporary, LocalKind::Temporary)?;
        let value = self.eval(subject)?;
        self.assign(Place::local(owner), Rvalue::Use(value), span);
        let mut place = Place::local(owner);
        if matches!(
            self.program
                .types
                .get(self.source.expressions[subject.0 as usize].ty),
            Ty::Reference { .. }
        ) {
            place = place.project(Projection::Deref);
        }
        let join = self.new_block(span, None)?;
        for arm in arms {
            let next = self.new_block(arm.pattern.span, None)?;
            self.match_arm(arm, place.clone(), result, join, next)?;
            self.current = Some(next);
        }
        self.terminate(Terminator::Unreachable);
        self.current = Some(join);
        self.leave(span)?;
        Ok(self.take(Place::local(result), ty))
    }

    fn match_arm(
        &mut self,
        arm: &hir::MatchArm,
        place: Place,
        result: LocalId,
        join: BlockId,
        next: BlockId,
    ) -> Result<(), LowerError> {
        let span = arm.pattern.span;
        let depth = self.scopes.len();
        self.enter(span)?;
        let matched = self.new_block(span, None)?;
        self.test_pattern(&arm.pattern, place.clone(), matched, next, depth)?;
        self.current = Some(matched);
        let mut bindings = Vec::new();
        collect_bindings(&arm.pattern, place, &mut bindings);
        self.preview_bindings(&mut bindings)?;
        if let Some(guard) = arm.guard {
            self.pattern_guard(guard, next, depth)?;
        }
        self.commit_bindings(&bindings)?;
        let value = self.eval(arm.value)?;
        self.assign(Place::local(result), Rvalue::Use(value), span);
        self.leave(span)?;
        self.goto(join);
        Ok(())
    }

    fn test_pattern(
        &mut self,
        pattern: &Pattern,
        place: Place,
        yes: BlockId,
        no: BlockId,
        depth: usize,
    ) -> Result<(), LowerError> {
        self.charge(pattern.span)?;
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Binding { .. } => {
                self.terminate(Terminator::Goto(yes))
            }
            PatternKind::Literal(value) => {
                let condition = self.materialize(
                    TyId::BOOL,
                    Rvalue::Binary {
                        op: BinaryOp::Equal,
                        left: Operand::Copy(place),
                        right: Operand::Constant {
                            value: value.clone(),
                            ty: pattern.ty,
                        },
                    },
                    pattern.span,
                )?;
                let no = self.cleanup_to(depth, no, ExitKind::Normal)?;
                self.terminate(Terminator::Switch { condition, yes, no });
            }
            PatternKind::Variant { definition, fields } => {
                let entered = self.new_block(pattern.span, None)?;
                let condition = self.materialize(
                    TyId::BOOL,
                    Rvalue::IsVariant {
                        place: place.clone(),
                        variant: *definition,
                    },
                    pattern.span,
                )?;
                let failed = self.cleanup_to(depth, no, ExitKind::Normal)?;
                self.terminate(Terminator::Switch {
                    condition,
                    yes: entered,
                    no: failed,
                });
                self.current = Some(entered);
                self.test_fields(
                    fields,
                    place.project(Projection::Downcast(*definition)),
                    yes,
                    no,
                    depth,
                )?;
            }
        }
        Ok(())
    }

    fn test_fields(
        &mut self,
        fields: &[Pattern],
        place: Place,
        yes: BlockId,
        no: BlockId,
        depth: usize,
    ) -> Result<(), LowerError> {
        for (index, field) in fields.iter().enumerate() {
            let next = self.new_block(field.span, None)?;
            self.test_pattern(
                field,
                place.clone().project(Projection::Field(index as u32)),
                next,
                no,
                depth,
            )?;
            self.current = Some(next);
        }
        self.terminate(Terminator::Goto(yes));
        Ok(())
    }

    fn preview_bindings(&mut self, bindings: &mut [Binding]) -> Result<(), LowerError> {
        for binding in bindings {
            let ty = self.source.locals[binding.local.0 as usize].ty;
            if binding.mode == BindingMode::Move {
                // Freeze the tested payload address, not its value. Guard calls
                // cannot cause us to re-evaluate an index or stale discriminant.
                binding.place = self.capture(binding.place.clone(), ty, binding.span)?;
                self.pattern_bindings
                    .insert(binding.local, binding.place.clone());
                continue;
            }
            let local = self.source_local(binding.local, LocalKind::Source)?;
            let value = match binding.mode {
                BindingMode::Copy => Rvalue::Use(Operand::Copy(binding.place.clone())),
                BindingMode::Shared | BindingMode::Mutable => Rvalue::Borrow {
                    mutable: binding.mode == BindingMode::Mutable,
                    place: binding.place.clone(),
                },
                BindingMode::Move => unreachable!("deferred ownership commit"),
            };
            self.assign(Place::local(local), value, binding.span);
        }
        Ok(())
    }

    fn pattern_guard(
        &mut self,
        guard: hir::ExprId,
        next: BlockId,
        depth: usize,
    ) -> Result<(), LowerError> {
        let span = self.source.expressions[guard.0 as usize].span;
        self.enter(span)?;
        let condition = self.eval(guard)?;
        let committed = self.new_block(span, None)?;
        let yes = self.cleanup_to(self.scopes.len() - 1, committed, ExitKind::Normal)?;
        let no = self.cleanup_to(depth, next, ExitKind::Normal)?;
        self.terminate(Terminator::Switch { condition, yes, no });
        self.scopes.pop();
        self.current = Some(committed);
        Ok(())
    }

    fn commit_bindings(&mut self, bindings: &[Binding]) -> Result<(), LowerError> {
        for binding in bindings {
            if binding.mode != BindingMode::Move {
                continue;
            }
            self.pattern_bindings.remove(&binding.local);
            let local = self.source_local(binding.local, LocalKind::Source)?;
            self.assign(
                Place::local(local),
                Rvalue::Use(Operand::Move(binding.place.clone())),
                binding.span,
            );
        }
        Ok(())
    }

    pub(super) fn block_value(
        &mut self,
        body: &hir::Block,
        value: Option<hir::ExprId>,
        ty: TyId,
        span: Span,
    ) -> Result<Operand, LowerError> {
        let result = self.local(ty, LocalKind::Temporary, None, span)?;
        self.enter(body.span)?;
        for &statement in &body.statements {
            self.statement(statement)?;
        }
        if self.current.is_some() {
            let value = match value {
                Some(value) => self.eval(value)?,
                None => Operand::Unit,
            };
            self.assign(Place::local(result), Rvalue::Use(value), span);
        }
        self.leave(span)?;
        if self.current.is_none() {
            // The continuation is structurally typed but unreachable: a block
            // that returns from the function never manufactures a value.
            self.current = Some(self.new_block(span, None)?);
        }
        Ok(self.take(Place::local(result), ty))
    }
}

fn collect_bindings(pattern: &Pattern, place: Place, output: &mut Vec<Binding>) {
    match &pattern.kind {
        PatternKind::Binding { local, mode } => output.push(Binding {
            local: *local,
            mode: *mode,
            place,
            span: pattern.span,
        }),
        PatternKind::Variant { definition, fields } => {
            let place = place.project(Projection::Downcast(*definition));
            for (index, field) in fields.iter().enumerate() {
                collect_bindings(
                    field,
                    place.clone().project(Projection::Field(index as u32)),
                    output,
                );
            }
        }
        _ => {}
    }
}
