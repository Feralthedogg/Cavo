//! Structural task metadata checks at the HIR boundary. Flow-sensitive scope
//! ownership and drain ordering are checked again after lowering to MIR.
use super::*;
use crate::{
    arena::Access as _,
    hir::InvariantError,
    types::{GenericParamKind as Kind, Ty},
};
use std::collections::HashSet;

pub(crate) fn validate_hir(program: &hir::Program) -> Result<(), InvariantError> {
    providers(program)?;
    for (&id, &role) in &program.contracts.intrinsics {
        if matches!(
            role,
            crate::contracts::Intrinsic::TaskJoin
                | crate::contracts::Intrinsic::TaskCancel
                | crate::contracts::Intrinsic::TaskIgnore
        ) {
            require(
                intrinsic_shape(program, program.definitions[id].ty, role),
                "task intrinsic no longer preserves its handle or result identity",
            )?;
        }
    }
    let mut regions = HashSet::new();
    for scope in &program.tasks.scopes {
        require(
            program
                .definitions
                .get_id(scope.owner)
                .is_some_and(|d| d.kind == hir::DefinitionKind::Function),
            "task scope owner is invalid",
        )?;
        require(
            matches!(scope.region, Region::Infer(_)) && regions.insert(scope.region),
            "task scopes must have distinct lexical regions",
        )?;
    }
    let mut declared = HashSet::new();
    for function in &program.functions {
        for statement in &function.statements {
            if let hir::StmtKind::TaskScope { scope, .. } = statement.kind {
                require(
                    program
                        .tasks
                        .scopes
                        .get(scope as usize)
                        .is_some_and(|s| s.owner == function.definition)
                        && declared.insert(scope),
                    "task scope statement has an invalid or reused identity",
                )?;
            }
        }
        for expression in &function.expressions {
            spawn(program, function, expression)?;
        }
    }
    Ok(())
}

pub(crate) fn intrinsic_shape(
    program: &hir::Program,
    ty: TyId,
    role: crate::contracts::Intrinsic,
) -> bool {
    use crate::{contracts::Intrinsic, types::GenericArg};
    let Ty::Function { parameters, result } = program.types.get(ty) else {
        return false;
    };
    let [input] = parameters.as_slice() else {
        return false;
    };
    let input = if role == Intrinsic::TaskCancel {
        match program.types.get(*input) {
            Ty::Reference { inner, .. } => *inner,
            _ => return false,
        }
    } else {
        *input
    };
    let Some((_, value)) = super::task_arguments(program, input) else {
        return false;
    };
    if role != Intrinsic::TaskJoin {
        return *result == TyId::VOID;
    }
    let Ty::Named {
        definition,
        arguments,
    } = program.types.get(*result)
    else {
        return false;
    };
    if Some(*definition) != program.tasks.result {
        return false;
    }
    let [GenericArg::Type(output), GenericArg::Type(error)] = arguments.as_slice() else {
        return false;
    };
    *output == value
        && matches!(program.types.get(*error), Ty::Named { definition, arguments }
        if Some(*definition) == program.tasks.task_error && arguments.is_empty())
}

fn providers(program: &hir::Program) -> Result<(), InvariantError> {
    if let Some(id) = program.tasks.task {
        require(
            program.definitions.get_id(id).is_some_and(|d| {
                d.kind == hir::DefinitionKind::Record
                    && d.generic_parameter_kinds == [Kind::Lifetime, Kind::Type]
            }) && program
                .records
                .iter()
                .any(|r| r.definition == id && r.fields.is_empty()),
            "Task provider is not opaque scope-bound observation storage",
        )?;
    }
    if let Some(id) = program.tasks.spawn_error {
        require(program.definitions.get_id(id).is_some_and(|d|
            d.kind == hir::DefinitionKind::Record && d.generic_parameter_kinds == [Kind::Type])
            && program.records.iter().any(|r| r.definition == id && matches!(r.fields.as_slice(), [field]
                if matches!(program.types.get(field.ty), Ty::Parameter { owner, index: 0 } if *owner == id))),
            "admission error does not own its original capture")?;
    }
    if let Some(id) = program.tasks.task_error {
        require(
            program.definitions.get_id(id).is_some_and(|d| {
                matches!(
                    d.kind,
                    hir::DefinitionKind::Record | hir::DefinitionKind::Enum
                ) && d.generic_parameter_kinds.is_empty()
            }),
            "task error provider is invalid",
        )?;
    }
    Ok(())
}

fn spawn(
    program: &hir::Program,
    function: &hir::Function,
    expression: &hir::Expr,
) -> Result<(), InvariantError> {
    let hir::ExprKind::Spawn {
        scope,
        arguments,
        parameter_types,
        child_result,
        capture_type,
        ..
    } = &expression.kind
    else {
        return Ok(());
    };
    let scope = program
        .tasks
        .scopes
        .get(*scope as usize)
        .filter(|s| s.owner == function.definition)
        .ok_or_else(|| InvariantError("spawn names another function's task scope".into()))?;
    require(
        arguments.len() == parameter_types.len()
            && parameter_types
                .iter()
                .chain([child_result, capture_type])
                .all(|ty| {
                    (ty.0 as usize) < program.types.values().len()
                        && *ty != TyId::ERROR
                        && program.types.valid_region_scope(*ty)
                }),
        "task child signature has invalid types or arity",
    )?;
    require(
        super::admission_result(program, expression.ty, *child_result, *capture_type),
        "task admission loses the observation handle or failure capture",
    )?;
    let Ty::Named { arguments, .. } = program.types.get(expression.ty) else {
        unreachable!("checked admission")
    };
    require(
        arguments
            .first()
            .and_then(|argument| argument.ty())
            .and_then(|ty| super::task_arguments(program, ty))
            .is_some_and(|(region, _)| region == scope.region),
        "task observation has a different region from its owning scope",
    )?;
    require(
        matches!(program.types.get(*capture_type), Ty::Named { definition, .. }
        if program.tasks.captures.contains(definition)),
        "spawn capture is not a generated invocation environment",
    )
}

fn require(valid: bool, message: &str) -> Result<(), InvariantError> {
    if valid {
        Ok(())
    } else {
        Err(InvariantError(message.into()))
    }
}
