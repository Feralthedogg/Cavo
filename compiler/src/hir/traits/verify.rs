use super::*;
use crate::{
    hir::{DefinitionKind, InvariantError, Program},
    types::{GenericParamKind, Ty},
};
use std::collections::HashSet;

pub(crate) fn validate(program: &Program) -> Result<(), InvariantError> {
    let mut traits = HashSet::new();
    let mut methods = HashSet::new();
    let mut roles = HashSet::new();
    for trait_ in &program.traits {
        require(traits.insert(trait_.definition), "duplicate trait metadata")?;
        require(
            definition(program, trait_.definition)?.kind == DefinitionKind::Trait,
            "trait metadata points to a non-trait declaration",
        )?;
        if let Some(role) = trait_.language_item {
            require(roles.insert(role), "duplicate language trait role")?;
        }
        for parent in &trait_.supertraits {
            reference(program, parent)?;
        }
        for method in &trait_.methods {
            require(
                methods.insert(method.definition),
                "trait method has multiple declaring traits",
            )?;
            let declaration = definition(program, method.definition)?;
            require(
                declaration.kind == DefinitionKind::Function
                    && matches!(program.types.get(declaration.ty), Ty::Function { .. }),
                "trait method is not a function",
            )?;
            let inherited = method.inherited_parameters as usize;
            require(
                inherited
                    == definition(program, trait_.definition)?
                        .generic_parameter_kinds
                        .len()
                        + 1
                    && declaration.generic_parameter_kinds.len() >= inherited
                    && declaration.generic_parameter_kinds.first() == Some(&GenericParamKind::Type),
                "trait method has an invalid Self/generic prefix",
            )?;
        }
        language_shape(program, trait_)?;
    }
    validate_impls(program)?;
    for declaration in &program.definitions {
        for bound in &declaration.bounds {
            require(
                declaration
                    .generic_parameter_kinds
                    .get(bound.parameter as usize)
                    == Some(&GenericParamKind::Type),
                "trait bound does not constrain a type parameter",
            )?;
            reference(program, &bound.trait_ref)?;
        }
    }
    for table in &program.vtables {
        validate_table(program, table)?;
    }
    Ok(())
}

fn validate_impls(program: &Program) -> Result<(), InvariantError> {
    let mut owners = HashSet::new();
    for implementation in &program.implementations {
        require(
            owners.insert(implementation.definition),
            "duplicate impl metadata",
        )?;
        require(
            definition(program, implementation.definition)?.kind == DefinitionKind::Impl,
            "impl metadata points to a non-impl declaration",
        )?;
        valid_type(program, implementation.target)?;
        if let Some(trait_ref) = &implementation.trait_ref {
            reference(program, trait_ref)?;
        }
        let mut declarations = HashSet::new();
        let mut bodies = HashSet::new();
        for method in &implementation.methods {
            require(
                bodies.insert(method.implementation),
                "duplicate impl method",
            )?;
            require(
                definition(program, method.implementation)?.kind == DefinitionKind::Function,
                "impl method is not a function",
            )?;
            if let Some(declaration) = method.declaration {
                require(
                    declarations.insert(declaration),
                    "duplicate trait method witness",
                )?;
                let reference = implementation
                    .trait_ref
                    .as_ref()
                    .ok_or_else(|| error("inherent impl claims a trait method"))?;
                require(
                    program.traits.iter().any(|trait_| {
                        trait_.definition == reference.definition
                            && trait_
                                .methods
                                .iter()
                                .any(|method| method.definition == declaration)
                    }),
                    "impl method belongs to another trait",
                )?;
            }
        }
        if let Some(reference) = &implementation.trait_ref {
            let trait_ = program
                .traits
                .iter()
                .find(|trait_| trait_.definition == reference.definition)
                .ok_or_else(|| error("impl trait metadata is absent"))?;
            require(
                declarations.len() == trait_.methods.len(),
                "impl has no witness for every required trait method",
            )?;
        }
    }
    Ok(())
}

fn validate_table(program: &Program, table: &Vtable) -> Result<(), InvariantError> {
    reference(program, &table.trait_ref)?;
    valid_type(program, table.concrete)?;
    let mut methods = HashSet::new();
    let expected = table_methods(program, table.trait_ref.definition)?;
    require(
        expected.len() == table.slots.len(),
        "vtable does not cover its trait methods",
    )?;
    for slot in &table.slots {
        require(
            methods.insert(slot.declaration),
            "duplicate vtable method slot",
        )?;
        require(
            expected.contains(&slot.declaration),
            "vtable method is outside its trait interface",
        )?;
        require(
            definition(program, slot.declaration)?.kind == DefinitionKind::Function
                && definition(program, slot.implementation)?.kind == DefinitionKind::Function,
            "vtable contains a non-function slot",
        )?;
        valid_type(program, slot.signature)?;
        let implementation = definition(program, slot.implementation)?;
        require(
            implementation.generic_parameter_kinds.len() == slot.type_arguments.len(),
            "vtable implementation generic arity mismatch",
        )?;
        for (kind, argument) in implementation
            .generic_parameter_kinds
            .iter()
            .zip(&slot.type_arguments)
        {
            require(
                *kind == argument.kind(),
                "vtable implementation generic argument kind mismatch",
            )?;
            valid_argument(program, *argument)?;
        }
        let mut matcher =
            Matcher::with_arguments(program, slot.implementation, &slot.type_arguments);
        require(
            matcher
                .ty(implementation.ty, slot.signature, 0)
                .map_err(|problem| error(&problem.to_string()))?,
            "vtable signature differs from its implementation",
        )?;
        validate_direct_witness(program, table, slot)?;
    }
    Ok(())
}

fn table_methods(program: &Program, principal: DefId) -> Result<HashSet<DefId>, InvariantError> {
    let mut seen = HashSet::new();
    let mut methods = HashSet::new();
    let mut pending = vec![principal];
    while let Some(definition) = pending.pop() {
        if !seen.insert(definition) {
            continue;
        }
        require(seen.len() <= 4096, "vtable supertrait limit exceeded")?;
        let trait_ = program
            .traits
            .iter()
            .find(|trait_| trait_.definition == definition)
            .ok_or_else(|| error("vtable trait metadata is absent"))?;
        methods.extend(trait_.methods.iter().map(|method| method.definition));
        pending.extend(trait_.supertraits.iter().map(|parent| parent.definition));
    }
    Ok(methods)
}

fn validate_direct_witness(
    program: &Program,
    table: &Vtable,
    slot: &VtableSlot,
) -> Result<(), InvariantError> {
    let trait_ = program
        .traits
        .iter()
        .find(|trait_| trait_.definition == table.trait_ref.definition)
        .ok_or_else(|| error("vtable trait metadata is absent"))?;
    let Some(method) = trait_
        .methods
        .iter()
        .find(|method| method.definition == slot.declaration)
    else {
        return Ok(());
    };
    let own = definition(program, method.definition)?
        .generic_parameter_kinds
        .len()
        - method.inherited_parameters as usize;
    require(
        slot.type_arguments.len() >= own,
        "vtable omitted method lifetime arguments",
    )?;
    let mut arguments = vec![GenericArg::Type(table.concrete)];
    arguments.extend_from_slice(&table.trait_ref.arguments);
    arguments.extend_from_slice(&slot.type_arguments[slot.type_arguments.len() - own..]);
    let expected = select_method(program, method.definition, &arguments)
        .map_err(|problem| error(&problem.to_string()))?
        .ok_or_else(|| error("vtable has no implementation witness"))?;
    require(
        expected.definition == slot.implementation
            && expected.type_arguments == slot.type_arguments,
        "vtable points to a different implementation witness",
    )
}

fn language_shape(program: &Program, trait_: &Trait) -> Result<(), InvariantError> {
    let Some(role) = trait_.language_item else {
        return Ok(());
    };
    if matches!(
        role,
        LanguageItem::Copy
            | LanguageItem::Send
            | LanguageItem::Sync
            | LanguageItem::TaskTransfer
            | LanguageItem::SuspendSafe
    ) {
        return require(
            trait_.methods.is_empty()
                && (role != LanguageItem::Copy || trait_.supertraits.is_empty())
                && definition(program, trait_.definition)?
                    .generic_parameter_kinds
                    .is_empty(),
            "auto marker language trait has invalid shape",
        );
    }
    require(
        trait_.methods.len() == 1,
        "language trait requires exactly one method",
    )?;
    language_method_shape(program, &trait_.methods[0], role)
}

fn language_method_shape(
    program: &Program,
    method: &TraitMethod,
    role: LanguageItem,
) -> Result<(), InvariantError> {
    let declaration = definition(program, method.definition)?;
    if matches!(
        role,
        LanguageItem::Fn | LanguageItem::FnMut | LanguageItem::FnOnce
    ) {
        require(
            declaration.declaration_clauses.is_empty(),
            "callable language protocols cannot add source contract obligations",
        )?;
    }
    let Ty::Function { parameters, result } = program.types.get(declaration.ty) else {
        return Err(error("language trait method is not callable"));
    };
    let is_self = |ty: TyId| matches!(program.types.get(ty), Ty::Parameter { owner, index: 0 } if *owner == method.definition);
    let receiver = parameters
        .first()
        .and_then(|ty| match program.types.get(*ty) {
            Ty::Reference { mutable, inner, .. } if is_self(*inner) => Some(*mutable),
            _ => None,
        });
    let valid = match role {
        LanguageItem::Copy
        | LanguageItem::Send
        | LanguageItem::Sync
        | LanguageItem::TaskTransfer
        | LanguageItem::SuspendSafe => unreachable!("handled above"),
        LanguageItem::Drop => {
            method.inherited_parameters == 1
                && declaration.generic_parameter_kinds.len() == 1
                && parameters.len() == 1
                && *result == TyId::VOID
                && receiver == Some(true)
                && declaration.declaration_clauses.is_empty()
        }
        LanguageItem::From => {
            method.inherited_parameters == 2
                && declaration.generic_parameter_kinds
                    == [GenericParamKind::Type, GenericParamKind::Type]
                && parameters.len() == 1
                && is_self(*result)
                && matches!(program.types.get(parameters[0]), Ty::Parameter { owner, index: 1 } if *owner == method.definition)
        }
        LanguageItem::Fn => receiver == Some(false),
        LanguageItem::FnMut => receiver == Some(true),
        LanguageItem::FnOnce => parameters.first().is_some_and(|ty| is_self(*ty)),
    };
    require(valid, "invalid language trait method signature")
}

fn reference(program: &Program, reference: &TraitRef) -> Result<(), InvariantError> {
    let declaration = definition(program, reference.definition)?;
    require(
        declaration.kind == DefinitionKind::Trait,
        "trait reference names a non-trait",
    )?;
    require(
        declaration.generic_parameter_kinds.len() == reference.arguments.len(),
        "trait reference generic arity mismatch",
    )?;
    for (kind, argument) in declaration
        .generic_parameter_kinds
        .iter()
        .zip(&reference.arguments)
    {
        require(
            *kind == argument.kind(),
            "trait reference generic kind mismatch",
        )?;
        valid_argument(program, *argument)?;
    }
    Ok(())
}

fn valid_argument(program: &Program, argument: GenericArg) -> Result<(), InvariantError> {
    match argument {
        GenericArg::Type(ty) => valid_type(program, ty),
        GenericArg::Const(value) => require(
            (value.0 as usize) < program.types.constant_terms().len(),
            "invalid const argument in trait metadata",
        ),
        GenericArg::Lifetime(crate::types::Region::Named { owner, name }) => require(
            definition(program, owner)?
                .lifetime_parameters
                .contains(&name),
            "invalid named lifetime in trait metadata",
        ),
        GenericArg::Lifetime(_) => Ok(()),
    }
}
fn valid_type(program: &Program, ty: TyId) -> Result<(), InvariantError> {
    require(
        ty != TyId::ERROR && (ty.0 as usize) < program.types.values().len(),
        "invalid type in trait metadata",
    )
}
fn definition(program: &Program, id: DefId) -> Result<&crate::hir::Definition, InvariantError> {
    program
        .definitions
        .get(id.0 as usize)
        .ok_or_else(|| error("invalid trait definition identity"))
}
fn require(valid: bool, message: &str) -> Result<(), InvariantError> {
    if valid { Ok(()) } else { Err(error(message)) }
}
fn error(message: &str) -> InvariantError {
    InvariantError(message.into())
}
