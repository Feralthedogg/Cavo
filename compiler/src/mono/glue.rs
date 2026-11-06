use super::*;
use crate::types::Ty;

impl Builder<'_> {
    pub(super) fn enqueue_drop_glue(&mut self, function: &hir::Function) -> Result<(), Error> {
        let mut pending: Vec<_> = function
            .locals
            .iter()
            .map(|local| (local.ty, 0usize))
            .collect();
        while let Some((ty, depth)) = pending.pop() {
            if !self.drop_types.insert(ty) {
                continue;
            }
            if depth >= 128 || self.drop_types.len() > 200_000 {
                return Err(problem(
                    function.body.span,
                    "E-MONO-LIMIT",
                    "concrete Drop dependency limit exceeded",
                ));
            }
            let selected = hir::traits::select_drop(&self.program, ty)
                .map_err(|error| problem(function.body.span, "E-MONO-DROP", error.to_string()))?;
            if let Some(selected) = selected {
                let instance = self.enqueue(InstanceKey {
                    definition: selected.definition,
                    arguments: selected.type_arguments,
                })?;
                self.drop_instances.push(DropInstance { ty, instance });
            }
            let children = self.owned_children(ty, function.body.span)?;
            pending.extend(children.into_iter().map(|child| (child, depth + 1)));
        }
        Ok(())
    }

    fn owned_children(&mut self, ty: TyId, span: Span) -> Result<Vec<TyId>, Error> {
        match self.program.types.get(ty).clone() {
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => Ok(vec![inner]),
            Ty::Named {
                definition,
                arguments,
            } => self.nominal_children(definition, &arguments, span),
            _ => Ok(Vec::new()),
        }
    }

    fn nominal_children(
        &mut self,
        definition: hir::DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> Result<Vec<TyId>, Error> {
        let fields: Vec<_> = if let Some(index) = self.record_indices[definition.0 as usize] {
            if self.program.definitions[definition.0 as usize].kind == hir::DefinitionKind::Union {
                return Ok(Vec::new());
            }
            self.program.records[index]
                .fields
                .iter()
                .map(|field| field.ty)
                .collect()
        } else if let Some(index) = self.enum_indices[definition.0 as usize] {
            self.program.enums[index]
                .variants
                .iter()
                .flat_map(|variant| {
                    let ty = self.program.definitions[variant.0 as usize].ty;
                    match self.program.types.get(ty) {
                        Ty::Function { parameters, .. } => parameters.clone(),
                        _ => Vec::new(),
                    }
                })
                .collect()
        } else {
            Vec::new()
        };
        fields
            .into_iter()
            .map(|field| {
                self.program
                    .types
                    .substitute_generics(field, definition, arguments)
                    .map_err(|error| problem(span, "E-MONO-TYPE", error.to_string()))
            })
            .collect()
    }
}
