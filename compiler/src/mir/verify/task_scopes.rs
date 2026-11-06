use super::*;

impl Verifier<'_> {
    pub(super) fn task_registry(
        &self,
        scope: ScopeId,
        registry: LocalId,
    ) -> Result<(), InvariantError> {
        self.scope(scope)?;
        let local = self.local(registry)?;
        require(
            local.kind == LocalKind::TaskRegistry && local.scope == scope && local.ty == TyId::VOID,
            "task registry is not owned by the declared scope",
        )
    }

    pub(super) fn spawn_structure(&self, terminator: &Terminator) -> Result<(), InvariantError> {
        let Terminator::Spawn {
            scope,
            registry,
            callee,
            type_arguments,
            arguments,
            parameter_types,
            child_result,
            capture_type,
            destination,
            normal,
            panic,
            cancel,
        } = terminator
        else {
            return fail("expected task admission");
        };
        self.task_registry(*scope, *registry)?;
        let ty = self.operand(callee)?;
        let signature = if let Operand::Function { definition, .. } = callee {
            self.signatures
                .direct(*definition, type_arguments)
                .ok_or_else(|| InvariantError::new("missing instantiated child signature".into()))?
        } else {
            require(
                type_arguments.is_empty(),
                "indirect child call has generic arguments",
            )?;
            match self.ty(ty)? {
                Ty::ForAll { inner, .. } => *inner,
                _ => ty,
            }
        };
        let Ty::Function { parameters, result } = self.ty(signature)? else {
            return fail("task child is not callable");
        };
        require(
            parameters.len() == arguments.len() && arguments.len() == parameter_types.len(),
            "task capture arity differs from its child signature",
        )?;
        for ((argument, supplied), expected) in
            arguments.iter().zip(parameter_types).zip(parameters)
        {
            self.compatible(self.operand(argument)?, *supplied)?;
            self.compatible(*supplied, *expected)?;
        }
        self.compatible(*result, *child_result)?;
        self.verify_capture_type(*capture_type, signature, parameter_types)?;
        let destination = self.value_place(destination)?;
        require(
            crate::tasks::admission_result(self.program, destination, *child_result, *capture_type),
            "spawn destination does not preserve Task or the failed admission captures",
        )?;
        self.block(*normal)?;
        self.abnormal_target(*panic, ExitKind::Panic)?;
        self.abnormal_target(*cancel, ExitKind::Cancel)
    }

    fn verify_capture_type(
        &self,
        ty: TyId,
        callee: TyId,
        parameters: &[TyId],
    ) -> Result<(), InvariantError> {
        let fields = self
            .properties
            .fields(ty)
            .ok_or_else(|| InvariantError::new("task capture is not an owned record".into()))?;
        require(
            fields.len() == parameters.len() + 1,
            "task capture record loses an evaluated operand",
        )?;
        // The private record stores this invocation's code pointer. Its free
        // call regions are already checked with the captured arguments above;
        // re-quantifying them as an independent callable changes their meaning.
        let (
            Ty::Function {
                parameters: actual,
                result: output,
            },
            Ty::Function {
                parameters: expected,
                result,
            },
        ) = (self.ty(fields[0])?, self.ty(callee)?)
        else {
            return fail("capture code pointer is not callable");
        };
        require(
            actual.len() == expected.len(),
            "capture code pointer arity mismatch",
        )?;
        for (&actual, &expected) in actual.iter().zip(expected) {
            self.compatible(actual, expected)?;
        }
        self.compatible(*output, *result)?;
        for (&field, &parameter) in fields[1..].iter().zip(parameters) {
            self.compatible(field, parameter)?;
        }
        Ok(())
    }
}
