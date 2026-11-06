use super::*;
use crate::types::{GenericArg, GenericParamKind};

struct Construction {
    definition: DefId,
    fields: HashMap<Symbol, (usize, TyId, ast::Visibility)>,
    initialized: Vec<bool>,
    inferred: Vec<Option<GenericArg>>,
    alias: Option<(DefId, TyId)>,
}
impl Construction {
    fn new(
        definition: DefId,
        inferred: Vec<Option<GenericArg>>,
        alias: Option<(DefId, TyId)>,
        fields: &[hir::Field],
    ) -> Self {
        Self {
            definition,
            inferred,
            alias,
            initialized: vec![false; fields.len()],
            fields: fields
                .iter()
                .enumerate()
                .map(|(index, field)| (field.name, (index, field.ty, field.visibility)))
                .collect(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Seed {
    Fixed,
    Infer,
}
struct Origin {
    ty: TyId,
    alias: Option<(DefId, TyId)>,
    seed: Seed,
}

impl Body<'_, '_> {
    pub(super) fn record(
        &mut self,
        path: &[ast::Name],
        fields: &[(ast::Name, ast::ExprId)],
        expected: Option<TyId>,
        span: Span,
    ) -> ExprId {
        let Some(mut construction) = self.record_target(path, expected, span) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let mut values = Vec::with_capacity(fields.len());
        // Keep source evaluation order; the declaration index selects storage.
        for &(name, value) in fields {
            if let Some(field) = self.record_field(&mut construction, name) {
                let hint = self.record_hint(field.1, &construction, span);
                let value = self.expression(value, hint);
                self.infer_generic(
                    field.1,
                    self.ty(value),
                    construction.definition,
                    &mut construction.inferred,
                    span,
                );
                values.push((field.0 as u32, value, field.1));
            } else {
                self.expression(value, None);
            }
        }
        let union =
            self.context.definition(construction.definition).kind == hir::DefinitionKind::Union;
        if union && values.len() != 1 {
            self.context.error(
                "E-UNION-INIT",
                "union construction must select exactly one active field",
                span,
            );
        } else if !union && construction.initialized.contains(&false) {
            self.context.error(
                "E-FIELD-MISSING",
                "record literal must initialize every field",
                span,
            );
        }
        if union && self.contract_depth == 0 {
            self.context.error(
                "E-CONTRACT-BOUNDARY",
                "union construction requires a contract boundary",
                span,
            );
        }
        self.finish_record(construction, values, span)
    }

    fn record_target(
        &mut self,
        path: &[ast::Name],
        expected: Option<TyId>,
        span: Span,
    ) -> Option<Construction> {
        let Origin {
            ty: template,
            alias,
            seed,
        } = self.record_origin(path)?;
        let Ty::Named {
            definition,
            arguments: template_arguments,
        } = self.type_kind(template).clone()
        else {
            self.context.error(
                "E-TYPE-RECORD",
                "record literal requires a known struct type",
                span,
            );
            return None;
        };
        let Some(index) = self
            .context
            .record_indices
            .get(definition.0 as usize)
            .copied()
            .flatten()
        else {
            self.context.error(
                "E-TYPE-RECORD",
                "record literal requires a struct type",
                span,
            );
            return None;
        };
        if self.context.program.tasks.task == Some(definition) {
            self.context.error(
                "E-TASK-CONSTRUCT",
                "task handles can only be created by checked task admission",
                span,
            );
            return None;
        }
        let mut inferred = self.record_parameters(definition);
        if seed == Seed::Fixed {
            inferred
                .iter_mut()
                .zip(template_arguments)
                .for_each(|(slot, value)| *slot = Some(value));
        } else if let Some(expected) = expected
            && let Ty::Named {
                definition: found,
                arguments,
            } = self.type_kind(expected)
            && *found == definition
        {
            inferred
                .iter_mut()
                .zip(arguments)
                .for_each(|(slot, &value)| *slot = Some(value));
        }
        let fields = &self.context.program.records[index].fields;
        Some(Construction::new(definition, inferred, alias, fields))
    }

    fn record_origin(&mut self, path: &[ast::Name]) -> Option<Origin> {
        if path.len() == 1
            && self.context.symbols.get(path[0].symbol) == "Self"
            && let Some(&ty) = self.generic_types.get(&path[0].symbol)
        {
            return Some(Origin {
                ty,
                alias: None,
                seed: Seed::Fixed,
            });
        }
        let owner = self.context.resolve(self.module, path)?;
        let definition = self.context.definition(owner);
        let ty = definition.ty;
        let alias = (definition.kind == hir::DefinitionKind::TypeAlias).then_some((owner, ty));
        let seed = if alias.is_some() && definition.generic_parameter_kinds.is_empty() {
            Seed::Fixed
        } else {
            Seed::Infer
        };
        Some(Origin { ty, alias, seed })
    }

    fn record_parameters(&mut self, definition: DefId) -> Vec<Option<GenericArg>> {
        let kinds = self
            .context
            .definition(definition)
            .generic_parameter_kinds
            .clone();
        kinds
            .into_iter()
            .map(|kind| {
                (kind == GenericParamKind::Lifetime)
                    .then(|| GenericArg::Lifetime(self.context.program.types.fresh_region()))
            })
            .collect()
    }

    fn record_field(
        &mut self,
        construction: &mut Construction,
        name: ast::Name,
    ) -> Option<(usize, TyId)> {
        let Some(&(index, ty, visibility)) = construction.fields.get(&name.symbol) else {
            self.context
                .error("E-TYPE-FIELD", "unknown field in record literal", name.span);
            return None;
        };
        if std::mem::replace(&mut construction.initialized[index], true) {
            self.context.error(
                "E-FIELD-DUPLICATE",
                "field initialized more than once",
                name.span,
            );
        }
        if !self.context.visible(
            visibility,
            self.context.definition(construction.definition).module,
            self.module,
        ) {
            self.context.error(
                "E-NAME-PRIVATE",
                "cannot initialize private field",
                name.span,
            );
        }
        Some((index, ty))
    }

    fn record_hint(&mut self, ty: TyId, construction: &Construction, span: Span) -> Option<TyId> {
        let arguments = construction
            .inferred
            .iter()
            .copied()
            .collect::<Option<Vec<_>>>()?;
        Some(self.record_field_type(ty, construction.definition, &arguments, span))
    }

    fn record_field_type(
        &mut self,
        ty: TyId,
        owner: DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> TyId {
        let ty = self
            .context
            .program
            .types
            .substitute_generics(ty, owner, arguments)
            .unwrap_or_else(|error| {
                self.context.error("E-CONST-EVAL", error.to_string(), span);
                TyId::ERROR
            });
        match crate::ctfe::normalize_type_constants(
            &mut self.context.program,
            ty,
            crate::ctfe::Limits::default(),
        ) {
            Ok(ty) => ty,
            Err(error) => {
                self.context.report_constant(error);
                TyId::ERROR
            }
        }
    }

    fn finish_record(
        &mut self,
        construction: Construction,
        values: Vec<(u32, ExprId, TyId)>,
        span: Span,
    ) -> ExprId {
        let Some(arguments) = construction
            .inferred
            .into_iter()
            .collect::<Option<Vec<_>>>()
        else {
            self.context.error("E-TYPE-INFER", "record literal requires an expected type or enough field information to infer every generic argument", span);
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        self.context
            .check_generic_bounds(construction.definition, &arguments, span);
        let mut checked = Vec::with_capacity(values.len());
        for (index, value, ty) in values {
            let ty = self.record_field_type(ty, construction.definition, &arguments, span);
            checked.push((index, self.coerce(value, ty)));
        }
        let ty = self.context.program.types.intern(Ty::Named {
            definition: construction.definition,
            arguments,
        });
        if let Some((owner, template)) = construction.alias {
            self.check_record_alias(owner, template, ty, span);
        }
        self.add_expr(
            H::Record {
                definition: construction.definition,
                fields: checked,
            },
            ty,
            span,
        )
    }

    fn check_record_alias(&mut self, owner: DefId, template: TyId, actual: TyId, span: Span) {
        let mut inferred = self.record_parameters(owner);
        self.infer_generic(template, actual, owner, &mut inferred, span);
        let Some(arguments) = inferred.into_iter().collect::<Option<Vec<_>>>() else {
            self.context.error(
                "E-TYPE-INFER",
                "could not infer the record alias arguments",
                span,
            );
            return;
        };
        self.context.check_generic_bounds(owner, &arguments, span);
        let expected = self.record_field_type(template, owner, &arguments, span);
        if !self.context.program.types.compatible(actual, expected) {
            self.mismatch(actual, expected, span);
        }
    }

    pub(super) fn unit_variant_type(
        &mut self,
        definition: DefId,
        expected: Option<TyId>,
        span: Span,
    ) -> Option<TyId> {
        let hir::DefinitionKind::Variant { parent, .. } = self.context.definition(definition).kind
        else {
            return None;
        };
        let ty = self.context.definition(definition).ty;
        if matches!(self.type_kind(ty), Ty::Function { .. }) {
            return None;
        }
        if self
            .context
            .definition(parent)
            .generic_parameter_kinds
            .is_empty()
        {
            return Some(ty);
        }
        if let Some(expected) = expected
            && matches!(self.type_kind(expected), Ty::Named { definition, .. } if *definition == parent)
        {
            return Some(expected);
        }
        self.context.error(
            "E-TYPE-INFER",
            "generic unit variant requires an expected enum type",
            span,
        );
        Some(TyId::ERROR)
    }
}
