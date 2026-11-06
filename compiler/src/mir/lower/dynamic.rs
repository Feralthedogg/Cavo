use super::*;

impl Builder<'_> {
    pub(super) fn dyn_coerce(
        &mut self,
        value: hir::ExprId,
        vtable: u32,
        ty: TyId,
        span: Span,
    ) -> Result<Operand, LowerError> {
        let value = self.eval(value)?;
        self.materialize(ty, Rvalue::DynCoerce { value, vtable }, span)
    }

    pub(super) fn dyn_call(
        &mut self,
        expression: hir::ExprId,
        receiver: hir::ExprId,
        trait_method: hir::DefId,
        arguments: &[hir::ExprId],
        parameter_types: &[TyId],
    ) -> Result<Operand, LowerError> {
        let node = &self.source.expressions[expression];
        let (ty, span) = (node.ty, node.span);
        let receiver_ty = self.source.expressions[receiver].ty;
        // Receiver evaluation and its reborrow precede every explicit argument.
        let receiver = self.call_argument(receiver, receiver_ty)?;
        let arguments = self.call_arguments(arguments, parameter_types)?;
        let mut obligations = vec![receiver.clone()];
        obligations.extend(arguments.iter().cloned());
        self.call_contracts(trait_method, &obligations, span)?;
        let local = self.local(ty, LocalKind::Temporary, None, span)?;
        let normal = self.new_block(span, None)?;
        let panic = self.abnormal(ExitKind::Panic)?;
        let cancel = self.abnormal(ExitKind::Cancel)?;
        self.terminate(Terminator::DynCall {
            receiver,
            trait_method,
            arguments,
            parameter_types: parameter_types.to_vec(),
            destination: Place::local(local),
            normal,
            panic,
            cancel,
        });
        self.current = Some(normal);
        Ok(self.take(Place::local(local), ty))
    }
}
