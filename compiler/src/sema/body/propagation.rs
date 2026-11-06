use super::*;
use crate::{
    hir::{BindingMode, Pattern, PatternKind},
    local::properties::Properties,
    syntax::token::TokenKind,
    types::GenericParamKind,
};

pub(in crate::sema) fn result_item(context: &mut Context<'_>) -> Option<DefId> {
    let providers: Vec<_> = context
        .program
        .definitions
        .iter()
        .enumerate()
        .filter_map(|(index, definition)| {
            provides_result(context, definition).then_some(DefId(index as u32))
        })
        .collect();
    let first = providers.first().copied()?;
    for &duplicate in &providers[1..] {
        context.error(
            "E-LANG-DUPLICATE",
            "only one declaration may provide the Result language item",
            context.definition(duplicate).span,
        );
    }
    if !valid_result_item(context, first) {
        context.error(
            "E-LANG-RESULT",
            "@lang(result) requires enum Result<T, E> with exactly Ok(T) and Err(E)",
            context.definition(first).span,
        );
        return None;
    }
    Some(first)
}

fn provides_result(context: &Context<'_>, definition: &hir::Definition) -> bool {
    definition.attributes.iter().any(|attribute| {
        if context.symbols.get(attribute.name) != "lang" {
            return false;
        }
        let [token] = attribute.arguments.as_slice() else {
            return false;
        };
        matches!(token.kind, TokenKind::Ident(name) if context.symbols.get(name) == "result")
    })
}

fn valid_result_item(context: &Context<'_>, owner: DefId) -> bool {
    let declaration = context.definition(owner);
    if declaration.kind != hir::DefinitionKind::Enum
        || declaration.generic_parameter_kinds != [GenericParamKind::Type, GenericParamKind::Type]
    {
        return false;
    }
    let Some(enumeration) = context
        .program
        .enums
        .iter()
        .find(|item| item.definition == owner)
    else {
        return false;
    };
    if enumeration.variants.len() != 2 {
        return false;
    }
    enumeration
        .variants
        .iter()
        .all(|&variant| valid_result_variant(context, owner, variant))
}

fn valid_result_variant(context: &Context<'_>, owner: DefId, variant: DefId) -> bool {
    let declaration = context.definition(variant);
    let index = match context.symbols.get(declaration.name) {
        "Ok" => 0,
        "Err" => 1,
        _ => return false,
    };
    let Ty::Function { parameters, .. } = context.program.types.get(declaration.ty) else {
        return false;
    };
    let [parameter] = parameters.as_slice() else {
        return false;
    };
    matches!(context.program.types.get(*parameter), Ty::Parameter { owner: found, index: position } if *found == owner && *position == index)
}

impl Body<'_, '_> {
    pub(super) fn contextual_result_constructor(
        &mut self,
        callee: ast::ExprId,
        expected: Option<TyId>,
    ) -> Option<ExprId> {
        let A::Path(path) = &self.context.ast.expr(callee).kind else {
            return None;
        };
        let [name] = path.as_slice() else {
            return None;
        };
        if self.find_local(name.symbol).is_some()
            || self.context.names[self.module.0 as usize].contains_key(&name.symbol)
            || self.context.imports[self.module.0 as usize].contains_key(&name.symbol)
        {
            return None;
        }
        let variant_name = match self.context.symbols.get(name.symbol) {
            "ok" => "Ok",
            "err" => "Err",
            _ => return None,
        };
        let Ty::Named { definition, .. } = self.type_kind(expected?) else {
            return None;
        };
        if Some(*definition) != self.context.result_item {
            return None;
        }
        let enumeration = self
            .context
            .program
            .enums
            .iter()
            .find(|item| item.definition == *definition)?;
        let variant = enumeration.variants.iter().copied().find(|&variant| {
            self.context
                .symbols
                .get(self.context.definition(variant).name)
                == variant_name
        })?;
        Some(self.add_expr(
            H::Definition(variant),
            self.context.definition(variant).ty,
            self.context.ast.expr(callee).span,
        ))
    }

    pub(super) fn propagate(
        &mut self,
        source: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
    ) -> ExprId {
        let value = self.expression(source, None);
        let Some((ok, err)) = self.result_variants(self.ty(value), span) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let Some((_, returned_err)) = self.result_variants(self.function.result, span) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let success = self.variant_fields(self.ty(value), ok)[0];
        let failure = self.variant_fields(self.ty(value), err)[0];
        let target_error = self.variant_fields(self.function.result, returned_err)[0];
        if let Some(expected) = expected
            && !self.context.program.types.compatible(success, expected)
        {
            self.mismatch(success, expected, span);
        }
        let properties = Properties::compute(&mut self.context.program);
        let temporary = self.pattern_temporary(self.ty(value), span);
        let subject_ty = self.ty(value);
        let successful = self.pattern_temporary(success, span);
        let failed = self.pattern_temporary(failure, span);
        let ok_value = self.propagation_binding(successful, &properties, span);
        let error_value = self.propagation_binding(failed, &properties, span);
        let converted = self.convert_error(error_value, target_error, span);
        let propagated = self.return_error(returned_err, converted, success, span);
        let arms = vec![
            hir::MatchArm {
                pattern: self.result_pattern(ok, subject_ty, successful, &properties, span),
                guard: None,
                value: ok_value,
            },
            hir::MatchArm {
                pattern: self.result_pattern(err, subject_ty, failed, &properties, span),
                guard: None,
                value: propagated,
            },
        ];
        self.add_expr(
            H::Match {
                subject: value,
                temporary,
                arms,
            },
            success,
            span,
        )
    }

    fn result_variants(&mut self, ty: TyId, span: Span) -> Option<(DefId, DefId)> {
        let Some(owner) = self.context.result_item else {
            self.context.error(
                "E-TRY-RESULT",
                "`?` requires a declared @lang(result) enum",
                span,
            );
            return None;
        };
        if !matches!(self.type_kind(ty), Ty::Named { definition, .. } if *definition == owner) {
            self.context.error(
                "E-TRY-RESULT",
                "`?` consumes Result and requires a Result return type",
                span,
            );
            return None;
        }
        let enumeration = self
            .context
            .program
            .enums
            .iter()
            .find(|item| item.definition == owner)?;
        let find = |name| {
            enumeration
                .variants
                .iter()
                .find(|&&id| self.context.symbols.get(self.context.definition(id).name) == name)
                .copied()
        };
        Some((find("Ok")?, find("Err")?))
    }

    fn propagation_binding(
        &mut self,
        local: LocalId,
        properties: &Properties,
        span: Span,
    ) -> ExprId {
        let ty = self.function.locals[local.0 as usize].ty;
        let value = self.add_expr(H::Local(local), ty, span);
        if properties.get(ty).copy {
            value
        } else {
            self.add_expr(
                H::Unary {
                    op: U::Move,
                    operand: value,
                },
                ty,
                span,
            )
        }
    }

    fn result_pattern(
        &self,
        variant: DefId,
        subject: TyId,
        local: LocalId,
        properties: &Properties,
        span: Span,
    ) -> Pattern {
        let ty = self.function.locals[local.0 as usize].ty;
        let mode = if properties.get(ty).copy {
            BindingMode::Copy
        } else {
            BindingMode::Move
        };
        let pattern = Pattern {
            kind: PatternKind::Binding { local, mode },
            ty,
            span,
        };
        Pattern {
            kind: PatternKind::Variant {
                definition: variant,
                fields: vec![pattern],
            },
            ty: subject,
            span,
        }
    }

    fn convert_error(&mut self, value: ExprId, target: TyId, span: Span) -> ExprId {
        let source = self.ty(value);
        if self.context.program.types.compatible(source, target) {
            return value;
        }
        let diagnostics = self.context.diagnostics.len();
        let Some(selection) = self.context.select_from_conversion(source, target, span) else {
            if self.context.diagnostics.len() == diagnostics {
                self.context.error("E-TRY-FROM", "no declared From implementation converts this Result error to the function's error type", span);
            }
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let declared = self.context.definition(selection.definition).ty;
        let Some(ty) = self
            .context
            .program
            .types
            .generalize_callable(declared, selection.definition)
        else {
            self.context.error(
                "E-REGION-LIMIT",
                "From callable generalization exceeds its resource limit",
                span,
            );
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let callee = self.add_expr(H::Definition(selection.definition), ty, span);
        self.add_expr(
            H::Call {
                callee,
                type_arguments: selection.type_arguments,
                arguments: vec![value],
                parameter_types: vec![source],
            },
            target,
            span,
        )
    }

    fn return_error(&mut self, variant: DefId, error: ExprId, result: TyId, span: Span) -> ExprId {
        let returned = self.function.result;
        let Ty::Named { arguments, .. } = self.type_kind(returned).clone() else {
            unreachable!("validated Result return");
        };
        let callee = self.add_expr(
            H::Definition(variant),
            self.context.definition(variant).ty,
            span,
        );
        let value = self.add_expr(
            H::Call {
                callee,
                type_arguments: arguments,
                arguments: vec![error],
                parameter_types: vec![self.ty(error)],
            },
            returned,
            span,
        );
        let statement = self.add_stmt(S::Return(Some(value)), span);
        self.add_expr(
            H::BlockValue {
                body: hir::Block {
                    statements: vec![statement],
                    span,
                },
                value: None,
            },
            result,
            span,
        )
    }
}
