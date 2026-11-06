use super::*;
use crate::{
    hir::{ClosureKind, Program},
    types::Ty,
};

fn role_kind(role: Option<LanguageItem>) -> Option<ClosureKind> {
    match role {
        Some(LanguageItem::Fn) => Some(ClosureKind::Fn),
        Some(LanguageItem::FnMut) => Some(ClosureKind::FnMut),
        Some(LanguageItem::FnOnce) => Some(ClosureKind::FnOnce),
        _ => None,
    }
}

pub(crate) fn closure_selection(
    program: &Program,
    target: TyId,
    reference: &TraitRef,
) -> Option<MethodSelection> {
    let trait_ = program
        .traits
        .iter()
        .find(|trait_| trait_.definition == reference.definition)?;
    let required = role_kind(trait_.language_item)?;
    let Ty::Named {
        definition,
        arguments,
    } = program.types.get(target)
    else {
        return None;
    };
    let closure = program
        .closures
        .iter()
        .find(|closure| closure.environment == *definition)?;
    if !closure.kind.supports(required) {
        return None;
    }
    let definition = if closure.kind == required {
        closure.function
    } else {
        closure
            .adapters
            .iter()
            .find(|(kind, _)| *kind == required)?
            .1
    };
    Some(MethodSelection {
        definition,
        type_arguments: arguments.clone(),
    })
}

pub(crate) fn validate_closure_trait(
    program: &mut Program,
    target: TyId,
    reference: &TraitRef,
) -> Result<bool, SelectionError> {
    let Some(selected) = closure_selection(program, target, reference) else {
        return Ok(false);
    };
    let trait_ = program
        .traits
        .iter()
        .find(|trait_| trait_.definition == reference.definition)
        .expect("selection retained trait");
    let Some(method) = trait_.methods.first() else {
        return Err(error("callable trait has no call method"));
    };
    let declaration = method.definition;
    check_signature(program, target, reference, declaration, &selected)?;
    if !program.definitions[declaration.0 as usize]
        .declaration_clauses
        .is_empty()
    {
        return Err(error(
            "closure has no established refinement of the callable trait contract",
        ));
    }
    // These are obligations, not evidence: the effect pass checks the actual
    // generated function against every declared upper bound after lowering.
    let attributes = program.definitions[declaration.0 as usize]
        .attributes
        .clone();
    for attribute in attributes {
        if !program.definitions[selected.definition.0 as usize]
            .attributes
            .iter()
            .any(|found| found.name == attribute.name && found.arguments == attribute.arguments)
        {
            program.definitions[selected.definition.0 as usize]
                .attributes
                .push(attribute);
        }
    }
    Ok(true)
}

fn check_signature(
    program: &mut Program,
    target: TyId,
    reference: &TraitRef,
    declaration: DefId,
    selected: &MethodSelection,
) -> Result<(), SelectionError> {
    let mut arguments = vec![GenericArg::Type(target)];
    arguments.extend_from_slice(&reference.arguments);
    let expected = program
        .types
        .substitute_generics(
            program.definitions[declaration.0 as usize].ty,
            declaration,
            &arguments,
        )
        .map_err(|problem| error(&problem.to_string()))?;
    let actual = program
        .types
        .substitute_generics(
            program.definitions[selected.definition.0 as usize].ty,
            selected.definition,
            &selected.type_arguments,
        )
        .map_err(|problem| error(&problem.to_string()))?;
    let expected = program
        .types
        .generalize_callable(expected, declaration)
        .ok_or_else(|| error("callable trait lifetime limit exceeded"))?;
    let actual = program
        .types
        .generalize_callable(actual, selected.definition)
        .ok_or_else(|| error("closure lifetime limit exceeded"))?;
    if !program.types.compatible(actual, expected) {
        return Err(error(
            "closure signature does not satisfy its callable trait",
        ));
    }
    Ok(())
}

fn error(message: &str) -> SelectionError {
    SelectionError(message.into())
}
