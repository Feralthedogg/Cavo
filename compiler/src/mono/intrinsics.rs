use super::*;

impl Builder<'_> {
    pub(super) fn specialize_intrinsic(
        &mut self,
        definition: hir::DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> Result<hir::DefId, Error> {
        let key = InstanceKey {
            definition,
            arguments: arguments.to_vec(),
        };
        if let Some(&found) = self.intrinsic_instances.get(&key) {
            return Ok(found);
        }
        if self.intrinsic_instances.len() >= self.options.limits.instances {
            return Err(problem(
                span,
                "E-MONO-LIMIT",
                "intrinsic specialization budget exceeded",
            ));
        }
        hir::traits::check_bounds(&mut self.program, definition, arguments)
            .map_err(|error| problem(span, "E-MONO-BOUND", error.to_string()))?;
        let mut item = self.program.definitions[definition].clone();
        let ty = self
            .program
            .types
            .substitute_generics(item.ty, definition, arguments)
            .map_err(|error| problem(span, "E-MONO-TYPE", error.to_string()))?;
        item.ty = ctfe::normalize_type_constants(&mut self.program, ty, self.options.constants)
            .map_err(|error| problem(error.span, error.code, error.message))?;
        item.type_parameter_count = 0;
        item.generic_parameter_kinds.clear();
        item.lifetime_parameters.clear();
        item.bounds.clear();
        let output = hir::DefId(self.program.definitions.len() as u32);
        self.program.definitions.push(item);
        let role = self.program.contracts.intrinsics[&definition];
        self.program.contracts.intrinsics.insert(output, role);
        self.intrinsic_instances.insert(key, output);
        Ok(output)
    }
}
