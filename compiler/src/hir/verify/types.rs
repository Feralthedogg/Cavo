use super::{InvariantError, Program, Ty, TyId, require, validate_graph};
use crate::{
    hir::DefId,
    types::{ConstKind, GenericArg, GenericParamKind, Region},
};

pub(super) fn validate(program: &Program) -> Result<(), InvariantError> {
    let types = program.types.values();
    let constants = program.types.constant_terms();
    require(
        types.len().saturating_add(constants.len()) <= 500_000,
        "HIR type/constant graph limit exceeded",
    )?;
    for (index, ty) in types.iter().enumerate() {
        validate_type(program, index, ty)?;
    }
    for (index, term) in constants.iter().enumerate() {
        validate_constant(program, index, term)?;
    }
    // Two individually acyclic arenas can still form a cycle through a
    // symbolic array length and a constant call's type argument.
    validate_graph(
        types.len() + constants.len(),
        "type/constant",
        |node, visit| {
            if node < types.len() {
                type_children(&types[node], types.len(), visit);
            } else {
                constant_children(&constants[node - types.len()], types.len(), visit);
            }
        },
    )
}

fn validate_type(program: &Program, index: usize, ty: &Ty) -> Result<(), InvariantError> {
    let mut invalid = false;
    type_ids(ty, &mut |child| invalid |= child.0 as usize >= index);
    require(!invalid, "type has a non-earlier structural child ID")?;
    match ty {
        Ty::Named {
            definition,
            arguments,
        } => arguments_for(program, *definition, arguments)?,
        Ty::Dynamic {
            trait_definition,
            arguments,
        } => {
            arguments_for(program, *trait_definition, arguments)?;
            require(
                program.definitions[trait_definition].kind == crate::hir::DefinitionKind::Trait,
                "dynamic type must name a trait",
            )?;
        }
        Ty::Parameter { owner, index } => {
            parameter(program, *owner, *index, GenericParamKind::Type)?
        }
        Ty::Reference { region, .. } => region_valid(program, *region)?,
        Ty::SymbolicArray { length, .. } => {
            let term = program
                .types
                .constant_terms()
                .get(length.0 as usize)
                .ok_or_else(|| {
                    InvariantError("symbolic array has an invalid constant ID".into())
                })?;
            require(
                matches!(
                    program.types.get(term.ty),
                    Ty::Integer {
                        signed: false,
                        bits: 0
                    }
                ),
                "array length must have usize type",
            )?;
        }
        Ty::ForAll { parameters, inner } => require(
            *parameters > 0
                && *parameters <= 64
                && matches!(
                    program.types.values().get(inner.0 as usize),
                    Some(Ty::Function { .. })
                ),
            "invalid callable binder",
        )?,
        _ => {}
    }
    Ok(())
}

pub(super) fn argument(program: &Program, argument: GenericArg) -> Result<(), InvariantError> {
    program
        .types
        .validate_generic_arg(argument)
        .map_err(|error| InvariantError(error.to_string()))?;
    match argument {
        GenericArg::Type(ty) => require(
            ty != TyId::ERROR && program.types.valid_region_scope(ty),
            "generic type argument has an error or escaping bound region",
        ),
        GenericArg::Const(_) => Ok(()),
        GenericArg::Lifetime(region) => region_valid(program, region),
    }
}

fn arguments_for(
    program: &Program,
    owner: DefId,
    args: &[GenericArg],
) -> Result<(), InvariantError> {
    let definition = program
        .definitions
        .get(owner.0 as usize)
        .ok_or_else(|| InvariantError("invalid nominal definition ID".into()))?;
    require(
        definition.generic_parameter_kinds.len() == args.len(),
        "generic argument count mismatch",
    )?;
    for (&value, &kind) in args.iter().zip(&definition.generic_parameter_kinds) {
        require(value.kind() == kind, "generic argument kind mismatch")?;
        // An arena node may be the body of an enclosing ForAll. Its bound
        // regions are checked at complete type roots, not as isolated children.
        program
            .types
            .validate_generic_arg(value)
            .map_err(|error| InvariantError(error.to_string()))?;
        if let GenericArg::Type(ty) = value {
            require(ty != TyId::ERROR, "generic argument is an error type")?;
        }
        if let GenericArg::Lifetime(region) = value {
            region_valid(program, region)?;
        }
    }
    Ok(())
}

fn parameter(
    program: &Program,
    owner: DefId,
    index: u32,
    kind: GenericParamKind,
) -> Result<(), InvariantError> {
    require(
        program
            .definitions
            .get(owner.0 as usize)
            .and_then(|definition| definition.generic_parameter_kinds.get(index as usize))
            == Some(&kind),
        "generic parameter has an invalid owner, slot or kind",
    )
}

fn region_valid(program: &Program, region: Region) -> Result<(), InvariantError> {
    if let Region::Named { owner, name } = region {
        require(
            program
                .definitions
                .get(owner.0 as usize)
                .is_some_and(|definition| definition.lifetime_parameters.contains(&name)),
            "named region has an invalid binder",
        )?;
    }
    Ok(())
}

fn validate_constant(
    program: &Program,
    index: usize,
    term: &crate::types::ConstTerm,
) -> Result<(), InvariantError> {
    require(
        term.ty != TyId::ERROR && (term.ty.0 as usize) < program.types.values().len(),
        "constant term has an invalid type",
    )?;
    let mut invalid = false;
    constant_children(term, program.types.values().len(), &mut |child| {
        if child >= program.types.values().len() && child - program.types.values().len() >= index {
            invalid = true;
        }
    });
    require(!invalid, "constant term has a non-earlier constant child")?;
    match &term.kind {
        ConstKind::Global(id) => {
            require(
                program
                    .definitions
                    .get(id.0 as usize)
                    .is_some_and(|definition| {
                        definition.kind == crate::hir::DefinitionKind::Global
                    }),
                "invalid global constant definition",
            )?;
        }
        ConstKind::Parameter { owner, index } => {
            parameter(program, *owner, *index, GenericParamKind::Const)?
        }
        ConstKind::Call {
            definition,
            type_arguments,
            ..
        } => {
            arguments_for(program, *definition, type_arguments)?;
            require(
                program.definitions[definition].kind == crate::hir::DefinitionKind::Function,
                "constant call must target a function",
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn generic_children(args: &[GenericArg], offset: usize, visit: &mut dyn FnMut(usize)) {
    for argument in args {
        match argument {
            GenericArg::Type(ty) => visit(ty.0 as usize),
            GenericArg::Const(id) => visit(offset + id.0 as usize),
            GenericArg::Lifetime(_) => {}
        }
    }
}

fn type_children(ty: &Ty, offset: usize, visit: &mut dyn FnMut(usize)) {
    type_ids(ty, &mut |id| visit(id.0 as usize));
    match ty {
        Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
            for argument in arguments {
                if let GenericArg::Const(id) = argument {
                    visit(offset + id.0 as usize);
                }
            }
        }
        Ty::SymbolicArray { length, .. } => visit(offset + length.0 as usize),
        _ => {}
    }
}

fn type_ids(ty: &Ty, visit: &mut dyn FnMut(TyId)) {
    match ty {
        Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
            for ty in arguments.iter().filter_map(|argument| argument.ty()) {
                visit(ty);
            }
        }
        Ty::Reference { inner, .. }
        | Ty::Pointer { inner, .. }
        | Ty::Array { inner, .. }
        | Ty::SymbolicArray { inner, .. }
        | Ty::Slice(inner)
        | Ty::ForAll { inner, .. } => visit(*inner),
        Ty::Function { parameters, result } => {
            for ty in parameters {
                visit(*ty);
            }
            visit(*result);
        }
        _ => {}
    }
}

fn constant_children(term: &crate::types::ConstTerm, offset: usize, visit: &mut dyn FnMut(usize)) {
    visit(term.ty.0 as usize);
    match &term.kind {
        ConstKind::Unary { operand, .. } => visit(offset + operand.0 as usize),
        ConstKind::Binary { left, right, .. } => {
            visit(offset + left.0 as usize);
            visit(offset + right.0 as usize);
        }
        ConstKind::Call {
            type_arguments,
            arguments,
            ..
        } => {
            generic_children(type_arguments, offset, visit);
            for id in arguments {
                visit(offset + id.0 as usize);
            }
        }
        _ => {}
    }
}
