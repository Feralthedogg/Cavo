use crate::{
    diagnostic::Diagnostic,
    hir,
    symbol::Interner,
    types::{Ty, TyId},
};
use std::collections::{HashMap, HashSet};

pub(crate) fn suggest(
    program: &mut hir::Program,
    symbols: &Interner,
    diagnostics: &mut [Diagnostic],
) {
    let wanted = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == "E-MOVE-EXPLICIT")
        .map(|diagnostic| diagnostic.primary)
        .collect::<HashSet<_>>();
    if wanted.is_empty() {
        return;
    }
    let candidates = local_candidates(program, symbols, &wanted);
    let role = program
        .traits
        .iter()
        .find(|item| item.language_item == Some(hir::traits::LanguageItem::Copy))
        .map(|item| {
            symbols
                .get(program.definitions[item.definition].name)
                .to_owned()
        });
    let mut eligible = HashMap::<TyId, bool>::new();
    for diagnostic in diagnostics
        .iter_mut()
        .filter(|diagnostic| diagnostic.code == "E-MOVE-EXPLICIT")
    {
        let Some(&(ty, definition)) = candidates.get(&diagnostic.primary) else {
            continue;
        };
        if !*eligible
            .entry(ty)
            .or_insert_with(|| hir::traits::copy_eligibility(program, ty).is_ok())
        {
            continue;
        }
        let definition = &program.definitions[definition];
        let name = symbols.get(definition.name);
        let help = match &role {
            Some(role) if definition.generic_parameter_kinds.is_empty() => format!(
                "if duplicating `{name}` is intended, add `impl {role} for {name} {{}}` beside its declaration"
            ),
            Some(role) => format!(
                "if duplicating `{name}` is intended, add an explicit `{role}` impl whose bounds make every field Copy"
            ),
            None => format!(
                "if duplicating `{name}` is intended, bring the language Copy trait into scope and explicitly opt the type in"
            ),
        };
        if !diagnostic.helps.contains(&help) {
            diagnostic.helps.push(help);
        }
    }
}

fn local_candidates(
    program: &hir::Program,
    symbols: &Interner,
    wanted: &HashSet<crate::source::Span>,
) -> HashMap<crate::source::Span, (TyId, hir::DefId)> {
    let mut candidates = HashMap::new();
    for function in &program.functions {
        for expression in &function.expressions {
            if wanted.contains(&expression.span)
                && let Ty::Named { definition, .. } = program.types.get(expression.ty)
                && hir::traits::copy_implementations(program, *definition)
                    .next()
                    .is_none()
                && super::super::package_identity(
                    program,
                    symbols,
                    program.definitions[*definition].module,
                ) == super::super::package_identity(
                    program,
                    symbols,
                    program.definitions[function.definition].module,
                )
            {
                candidates
                    .entry(expression.span)
                    .or_insert((expression.ty, *definition));
            }
        }
    }
    candidates
}
