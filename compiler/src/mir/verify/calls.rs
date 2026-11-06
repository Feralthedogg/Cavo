use super::*;
use crate::types::GenericArg;
use std::collections::HashMap;

#[derive(Default)]
pub(super) struct Signatures {
    direct: HashMap<hir::DefId, HashMap<Vec<GenericArg>, TyId>>,
    dynamic: HashMap<(TyId, hir::DefId), TyId>,
}

impl Signatures {
    pub fn prepare(mir: &Program, hir: &mut hir::Program) -> Result<Self, InvariantError> {
        let mut result = Self::default();
        for body in &mir.functions {
            for block in &body.blocks {
                if let Terminator::Call {
                    callee: Operand::Function { definition, .. },
                    type_arguments,
                    ..
                } = &block.terminator
                {
                    let signatures = result.direct.entry(*definition).or_default();
                    if !signatures.contains_key(type_arguments.as_slice()) {
                        let ty = instantiate(hir, *definition, type_arguments)?;
                        signatures.insert(type_arguments.clone(), ty);
                    }
                }
            }
        }
        let dynamic_types: Vec<_> = hir
            .types
            .values()
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                if let Ty::Dynamic {
                    trait_definition,
                    arguments,
                } = ty
                {
                    Some((
                        TyId(index as u32),
                        hir::traits::TraitRef {
                            definition: *trait_definition,
                            arguments: arguments.clone(),
                        },
                    ))
                } else {
                    None
                }
            })
            .collect();
        for (ty, principal) in dynamic_types {
            result.prepare_dynamic(hir, ty, &principal)?;
        }
        Ok(result)
    }

    fn prepare_dynamic(
        &mut self,
        hir: &mut hir::Program,
        ty: TyId,
        principal: &hir::traits::TraitRef,
    ) -> Result<(), InvariantError> {
        let traits = hir::traits::supertraits(hir, principal)
            .map_err(|error| InvariantError::new(error.to_string()))?;
        for trait_ref in traits {
            let methods = hir
                .traits
                .iter()
                .find(|item| item.definition == trait_ref.definition)
                .ok_or_else(|| InvariantError::new("dynamic type has no trait metadata".into()))?
                .methods
                .clone();
            for method in methods {
                let mut arguments = vec![GenericArg::Type(ty)];
                arguments.extend(&trait_ref.arguments);
                let kinds = hir.definitions[method.definition.0 as usize]
                    .generic_parameter_kinds
                    .clone();
                for kind in &kinds[arguments.len().min(kinds.len())..] {
                    require(
                        *kind == crate::types::GenericParamKind::Lifetime,
                        "dynamic method has unresolved generic arguments",
                    )?;
                    arguments.push(GenericArg::Lifetime(hir.types.fresh_region()));
                }
                let signature = instantiate(hir, method.definition, &arguments)?;
                self.dynamic.insert((ty, method.definition), signature);
            }
        }
        Ok(())
    }

    pub fn direct(&self, definition: hir::DefId, arguments: &[GenericArg]) -> Option<TyId> {
        self.direct.get(&definition)?.get(arguments).copied()
    }
    pub fn dynamic(&self, ty: TyId, method: hir::DefId) -> Option<TyId> {
        self.dynamic.get(&(ty, method)).copied()
    }
}

fn instantiate(
    hir: &mut hir::Program,
    definition: hir::DefId,
    arguments: &[GenericArg],
) -> Result<TyId, InvariantError> {
    let item = hir
        .definitions
        .get(definition.0 as usize)
        .ok_or_else(|| InvariantError::new("invalid call definition".into()))?;
    require(
        item.generic_parameter_kinds.len() == arguments.len(),
        "call generic argument count mismatch",
    )?;
    for (&argument, &kind) in arguments.iter().zip(&item.generic_parameter_kinds) {
        require(
            argument.kind() == kind,
            "call generic argument kind mismatch",
        )?;
        hir.types
            .validate_generic_arg(argument)
            .map_err(|error| InvariantError::new(error.to_string()))?;
    }
    // Verification must not manufacture fresh caller regions on every replay.
    // The call carries its resolved lifetime arguments; substitute those and
    // retain the declaration's own closed callable binders.
    let signature = hir
        .types
        .substitute_generics(item.ty, definition, arguments)
        .map_err(|error| InvariantError::new(error.to_string()))?;
    crate::ctfe::normalize_type_constants(hir, signature, crate::ctfe::Limits::default())
        .map_err(|error| InvariantError::new(error.to_string()))
}

impl Verifier<'_> {
    pub(super) fn call_structure(&self, terminator: &Terminator) -> Result<(), InvariantError> {
        let Terminator::Call {
            callee,
            type_arguments,
            arguments,
            parameter_types,
            destination,
            normal,
            panic,
            cancel,
        } = terminator
        else {
            return fail("expected a call terminator");
        };
        let callee_ty = self.operand(callee)?;
        let signature = if let Operand::Function { definition, .. } = callee {
            self.signatures
                .direct(*definition, type_arguments)
                .ok_or_else(|| InvariantError::new("missing instantiated call signature".into()))?
        } else {
            require(
                type_arguments.is_empty(),
                "indirect call has generic arguments",
            )?;
            match self.ty(callee_ty)? {
                Ty::ForAll { inner, .. } => *inner,
                _ => callee_ty,
            }
        };
        self.check_arguments(signature, arguments, parameter_types, destination)?;
        self.block(*normal)?;
        self.abnormal_target(*panic, ExitKind::Panic)?;
        self.abnormal_target(*cancel, ExitKind::Cancel)
    }

    pub(super) fn dynamic_structure(&self, terminator: &Terminator) -> Result<(), InvariantError> {
        let Terminator::DynCall {
            receiver,
            trait_method,
            arguments,
            parameter_types,
            destination,
            normal,
            panic,
            cancel,
        } = terminator
        else {
            return fail("expected a dynamic call terminator");
        };
        let receiver_ty = self.operand(receiver)?;
        let Ty::Reference { inner, .. } = self.ty(receiver_ty)? else {
            return fail("dynamic receiver is not a reference");
        };
        let signature = self
            .signatures
            .dynamic(*inner, *trait_method)
            .ok_or_else(|| {
                InvariantError::new("method is not present in the dynamic trait".into())
            })?;
        let Ty::Function { parameters, result } = self.ty(signature)? else {
            return fail("dynamic method is not callable");
        };
        let (self_ty, rest) = parameters
            .split_first()
            .ok_or_else(|| InvariantError::new("dynamic method has no receiver".into()))?;
        self.compatible(receiver_ty, *self_ty)?;
        self.argument_types(rest, arguments, parameter_types)?;
        self.compatible(self.place(destination)?, *result)?;
        self.block(*normal)?;
        self.abnormal_target(*panic, ExitKind::Panic)?;
        self.abnormal_target(*cancel, ExitKind::Cancel)
    }

    fn check_arguments(
        &self,
        signature: TyId,
        arguments: &[Operand],
        supplied: &[TyId],
        destination: &Place,
    ) -> Result<(), InvariantError> {
        let Ty::Function { parameters, result } = self.ty(signature)? else {
            return fail("call operand is not callable");
        };
        self.argument_types(parameters, arguments, supplied)?;
        self.compatible(self.place(destination)?, *result)
    }

    fn argument_types(
        &self,
        expected: &[TyId],
        arguments: &[Operand],
        supplied: &[TyId],
    ) -> Result<(), InvariantError> {
        require(
            expected.len() == arguments.len() && supplied.len() == arguments.len(),
            "call argument count mismatch",
        )?;
        for ((argument, supplied), expected) in arguments.iter().zip(supplied).zip(expected) {
            self.compatible(self.operand(argument)?, *supplied)?;
            self.compatible(*supplied, *expected)?;
        }
        Ok(())
    }
}
