use super::*;
use crate::types::{ConstKind, GenericParamKind, Region};

impl Context<'_> {
    pub(super) fn validate_drop_target(&mut self, implementation: &model::Impl) {
        let span = self.definition(implementation.definition).span;
        let Ty::Named {
            definition,
            arguments,
        } = self.program.types.get(implementation.target).clone()
        else {
            self.error(
                "E-DROP-TARGET",
                "Drop requires a record or enum owned by this package",
                span,
            );
            return;
        };
        if !matches!(self.definition(definition).kind, D::Record | D::Enum) {
            self.error(
                "E-DROP-TARGET",
                "Drop requires a record or enum owned by this package",
                span,
            );
            return;
        }
        if !self.drop_covers_nominal(implementation.definition, definition, &arguments) {
            self.error(
                "E-DROP-SPECIALIZATION",
                "Drop must cover every generic instance of its nominal type",
                span,
            );
            return;
        }
        let Some(allowed) = self.nominal_drop_bounds(definition, &arguments, span) else {
            return;
        };
        for bound in self.definition(implementation.definition).bounds.clone() {
            let established = allowed.iter().any(|expected| {
                expected.parameter == bound.parameter
                    && model::supertraits(&mut self.program, &expected.trait_ref)
                        .is_ok_and(|references| references.contains(&bound.trait_ref))
            });
            if !established {
                self.error(
                    "E-DROP-BOUND",
                    "Drop cannot add bounds beyond its nominal type declaration",
                    span,
                );
            }
        }
    }

    fn drop_covers_nominal(
        &self,
        implementation: DefId,
        nominal: DefId,
        arguments: &[GenericArg],
    ) -> bool {
        let parameters = &self.definition(implementation).generic_parameter_kinds;
        let nominal = &self.definition(nominal).generic_parameter_kinds;
        if parameters.len() != nominal.len() || arguments.len() != nominal.len() {
            return false;
        }
        let mut used = HashSet::new();
        arguments.iter().zip(nominal).all(|(&argument, &kind)| {
            let Some(index) = self.drop_argument_parameter(implementation, argument) else {
                return false;
            };
            parameters.get(index as usize) == Some(&kind) && used.insert(index)
        })
    }

    fn drop_argument_parameter(&self, owner: DefId, argument: GenericArg) -> Option<u32> {
        match argument {
            GenericArg::Type(ty) => match *self.program.types.get(ty) {
                Ty::Parameter {
                    owner: found,
                    index,
                } if found == owner => Some(index),
                _ => None,
            },
            GenericArg::Const(value) => match self.program.types.const_term(value).kind {
                ConstKind::Parameter {
                    owner: found,
                    index,
                } if found == owner => Some(index),
                _ => None,
            },
            GenericArg::Lifetime(Region::Named { owner: found, name }) if found == owner => self
                .program
                .types
                .generic_parameters(owner)
                .iter()
                .position(|(candidate, kind)| {
                    *candidate == name && *kind == GenericParamKind::Lifetime
                })
                .map(|index| index as u32),
            _ => None,
        }
    }

    fn nominal_drop_bounds(
        &mut self,
        nominal: DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> Option<Vec<model::TraitBound>> {
        let mut bounds = self.definition(nominal).bounds.clone();
        for bound in &mut bounds {
            let Some(GenericArg::Type(target)) = arguments.get(bound.parameter as usize) else {
                return None;
            };
            let Ty::Parameter { index, .. } = *self.program.types.get(*target) else {
                return None;
            };
            bound.parameter = index;
            for argument in &mut bound.trait_ref.arguments {
                match self
                    .program
                    .types
                    .substitute_arg(*argument, nominal, arguments)
                {
                    Ok(value) => *argument = value,
                    Err(error) => {
                        self.error("E-DROP-BOUND", error.to_string(), span);
                        return None;
                    }
                }
            }
        }
        Some(bounds)
    }
}

pub(crate) fn validate_destructors(program: &mut hir::Program, diagnostics: &mut Vec<Diagnostic>) {
    let Some(drop) = program
        .traits
        .iter()
        .find(|trait_| trait_.language_item == Some(model::LanguageItem::Drop))
        .map(|trait_| trait_.definition)
    else {
        return;
    };
    let methods: Vec<_> = program
        .implementations
        .iter()
        .filter(|implementation| {
            implementation
                .trait_ref
                .as_ref()
                .is_some_and(|reference| reference.definition == drop)
        })
        .flat_map(|implementation| {
            implementation
                .methods
                .iter()
                .map(|method| method.implementation)
        })
        .collect();
    if methods.is_empty() {
        return;
    }
    let candidates = match crate::mir::effects::cleanup_candidates(program) {
        Ok(candidates) => candidates,
        Err(error) => {
            report(
                diagnostics,
                Diagnostic::error(
                    "E-DROP-EFFECT",
                    error.to_string(),
                    program.definitions[drop.0 as usize].span,
                ),
            );
            return;
        }
    };
    for method in methods {
        if !candidates.allows(method) {
            report(
                diagnostics,
                Diagnostic::error(
                    "E-DROP-EFFECT",
                    "destructor requires established bounded nosuspend, nocancel, nopanic and noalloc effects",
                    program.definitions[method.0 as usize].span,
                ),
            );
        }
    }
}
