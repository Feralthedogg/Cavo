//! Declaring Copy grants permission; eligibility is checked independently of
//! that declaration, so the impl under validation cannot prove itself valid.
use super::*;
use crate::{
    hir::{DefinitionKind, Program},
    source::Span,
    types::Ty,
};

pub(crate) fn implementations(program: &Program, definition: DefId) -> impl Iterator<Item = &Impl> {
    let role = program
        .traits
        .iter()
        .find(|item| item.language_item == Some(LanguageItem::Copy))
        .map(|item| item.definition);
    program.implementations.iter().filter(move |implementation|
        implementation.trait_ref.as_ref().is_some_and(|reference|Some(reference.definition)==role)
            && matches!(program.types.get(implementation.target),Ty::Named {definition:target,..} if *target==definition))
}

pub(crate) struct Ineligible {
    pub reason: &'static str,
    pub fields: Vec<Span>,
    pub destructor: Option<Span>,
}

pub(crate) fn eligibility(program: &mut Program, target: TyId) -> Result<(), Ineligible> {
    let Ty::Named {
        definition,
        arguments,
    } = program.types.get(target).clone()
    else {
        return Err(Ineligible {
            reason: "only a nominal struct, enum or union may declare Copy; built-in copy rules cannot be overridden",
            fields: Vec::new(),
            destructor: None,
        });
    };
    if crate::tasks::task_arguments(program, target).is_some() {
        return Err(Ineligible {
            reason: "task observation handles belong to one owning task and cannot implement Copy",
            fields: Vec::new(),
            destructor: None,
        });
    }
    match select_drop(program, target) {
        Ok(Some(method)) => {
            return Err(Ineligible {
                reason: "a type with user Drop cannot also implement Copy",
                fields: Vec::new(),
                destructor: Some(program.definitions[method.definition].span),
            });
        }
        Err(_) => {
            return Err(Ineligible {
                reason: "Copy requires an established absence of user Drop",
                fields: Vec::new(),
                destructor: None,
            });
        }
        Ok(None) => {}
    }
    let declarations = fields(program, definition).ok_or(Ineligible {
        reason: "Copy requires a checked struct, enum or union declaration",
        fields: Vec::new(),
        destructor: None,
    })?;
    let mut failures = Vec::new();
    for (ty, span) in declarations {
        let ty = program
            .types
            .substitute_generics(ty, definition, &arguments);
        if !ty.is_ok_and(|ty| is_copy(program, ty)) {
            failures.push(span);
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(Ineligible {
            reason: "every field must be Copy under this impl's bounds",
            fields: failures,
            destructor: None,
        })
    }
}

fn fields(program: &Program, definition: DefId) -> Option<Vec<(TyId, Span)>> {
    match program.definitions[definition].kind {
        DefinitionKind::Record | DefinitionKind::Union => Some(
            program
                .records
                .iter()
                .find(|record| record.definition == definition)?
                .fields
                .iter()
                .map(|field| (field.ty, field.span))
                .collect(),
        ),
        DefinitionKind::Enum => Some(
            program
                .enums
                .iter()
                .find(|item| item.definition == definition)?
                .variants
                .iter()
                .flat_map(|id| {
                    let definition = &program.definitions[*id];
                    let parameters = match program.types.get(definition.ty) {
                        Ty::Function { parameters, .. } => parameters.as_slice(),
                        _ => &[],
                    };
                    parameters.iter().map(|&ty| (ty, definition.span))
                })
                .collect(),
        ),
        _ => None,
    }
}
