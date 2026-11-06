use super::*;

impl Builder<'_> {
    pub(super) fn task_scope(&mut self, source: u32, body: &hir::Block) -> Result<(), LowerError> {
        self.enter(body.span)?;
        let registry = self.local(TyId::VOID, LocalKind::TaskRegistry, None, body.span)?;
        self.emit(StatementKind::RegistryStart(registry), body.span);
        self.scopes.last_mut().expect("entered task scope").task = Some((source, registry));
        for &statement in &body.statements {
            self.statement(statement)?;
        }
        self.leave(body.span)
    }

    pub(super) fn spawn_expression(
        &mut self,
        expression: &hir::Expr,
    ) -> Result<Operand, LowerError> {
        let H::Spawn {
            scope,
            callee,
            type_arguments,
            arguments,
            parameter_types,
            child_result,
            capture_type,
        } = &expression.kind
        else {
            unreachable!("spawn expression");
        };
        let Some((owner, registry)) = self.scopes.iter().rev().find_map(|active| {
            active
                .task
                .filter(|(source, _)| source == scope)
                .map(|(_, registry)| (active.id, registry))
        }) else {
            return self.fail(expression.span, "spawn is outside its owning task scope");
        };
        let callee = self.eval(*callee)?;
        let arguments = self.call_arguments(arguments, parameter_types)?;
        if let Operand::Function { definition, .. } = callee {
            self.call_contracts(definition, &arguments, expression.span)?;
        }
        let destination = self.local(expression.ty, LocalKind::Temporary, None, expression.span)?;
        let normal = self.new_block(expression.span, None)?;
        let panic = self.abnormal(ExitKind::Panic)?;
        let cancel = self.abnormal(ExitKind::Cancel)?;
        self.terminate(Terminator::Spawn {
            scope: owner,
            registry,
            callee,
            type_arguments: type_arguments.clone(),
            arguments,
            parameter_types: parameter_types.clone(),
            child_result: *child_result,
            capture_type: *capture_type,
            destination: Place::local(destination),
            normal,
            panic,
            cancel,
        });
        self.current = Some(normal);
        Ok(self.take(Place::local(destination), expression.ty))
    }
}
