use super::*;
use crate::tasks::transfer::Property;

impl Context<'_> {
    pub(super) fn validate_negative_implementation(&mut self, item: &model::Impl) {
        let span = self.definition(item.definition).span;
        let role = item.trait_ref.as_ref().and_then(|reference| {
            self.program
                .traits
                .iter()
                .find(|trait_| trait_.definition == reference.definition)?
                .language_item
        });
        if role.and_then(Property::from_role).is_none() {
            self.error(
                "E-IMPL-NEGATIVE",
                "negative impls are restricted to Send, Sync, TaskTransfer and SuspendSafe",
                span,
            );
            return;
        }
        if !item.methods.is_empty() || self.program.tasks.trusted.contains_key(&item.definition) {
            self.error(
                "E-IMPL-NEGATIVE",
                "a negative marker impl has no methods or trusted guarantee",
                span,
            );
        }
        let Some((definition, arguments)) = self.negative_target(item) else {
            return;
        };
        self.validate_negative_bounds(item, definition, &arguments);
    }

    fn negative_target(&mut self, item: &model::Impl) -> Option<(DefId, Vec<GenericArg>)> {
        let span = self.definition(item.definition).span;
        let Ty::Named {
            definition,
            arguments,
        } = self.program.types.get(item.target).clone()
        else {
            self.error(
                "E-IMPL-NEGATIVE",
                "negative impls require a locally defined nominal type",
                span,
            );
            return None;
        };
        if !matches!(
            self.definition(definition).kind,
            D::Record | D::Enum | D::Union
        ) || self.package(self.definition(definition).module)
            != self.package(self.definition(item.definition).module)
        {
            self.error(
                "E-IMPL-ORPHAN",
                "only the defining package may restrict a nominal type's structural traits",
                span,
            );
            return None;
        }
        if !self.drop_covers_nominal(item.definition, definition, &arguments) {
            self.error(
                "E-IMPL-NEGATIVE",
                "negative impls must cover every generic instance of their nominal type",
                span,
            );
            return None;
        }
        Some((definition, arguments))
    }

    fn validate_negative_bounds(
        &mut self,
        item: &model::Impl,
        nominal: DefId,
        arguments: &[GenericArg],
    ) {
        let span = self.definition(item.definition).span;
        let Some(allowed) = self.nominal_drop_bounds(nominal, arguments, span) else {
            return;
        };
        for bound in self.definition(item.definition).bounds.clone() {
            if !allowed.iter().any(|expected| {
                expected.parameter == bound.parameter
                    && model::supertraits(&mut self.program, &expected.trait_ref)
                        .is_ok_and(|references| references.contains(&bound.trait_ref))
            }) {
                self.error(
                    "E-IMPL-NEGATIVE",
                    "negative impls cannot add bounds beyond their nominal type declaration",
                    span,
                );
            }
        }
    }
}
