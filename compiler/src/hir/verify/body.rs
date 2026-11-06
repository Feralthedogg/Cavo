use super::*;

pub(super) fn const_origin(
    program: &Program,
    definition: &Definition,
) -> Result<(), InvariantError> {
    if let Some(origin) = definition.const_origin {
        require(
            definition.kind == DefinitionKind::Function
                && definition.foreign_abi.is_none()
                && program
                    .definitions
                    .get(origin.0 as usize)
                    .is_some_and(|source| source.kind == DefinitionKind::Function)
                && program.constants.functions.contains_key(&origin),
            "const origin does not name a checked const function",
        )?;
    }
    Ok(())
}

pub(super) fn clause_binding(
    program: &Program,
    function: &Function,
    clause: &Clause,
) -> Result<(), InvariantError> {
    if let Some(result) = clause.result_local {
        require(
            clause.kind == crate::syntax::ast::ClauseKind::Ensures
                && !function.parameters.contains(&result)
                && function.locals.get(result.0 as usize).is_some_and(|local| {
                    !local.mutable && program.types.compatible(local.ty, function.result)
                }),
            "contract result binding is invalid",
        )?;
    }
    Ok(())
}

pub(super) fn function_header(
    program: &Program,
    function: &Function,
) -> Result<(), InvariantError> {
    let definition = program
        .definitions
        .get(function.definition.0 as usize)
        .ok_or_else(|| InvariantError("function has an invalid definition".into()))?;
    let Ty::Function { parameters, result } = program.types.get(definition.ty) else {
        return Err(InvariantError(
            "function declaration is not callable".into(),
        ));
    };
    require(
        parameters.len() == function.parameters.len(),
        "function parameter count differs from its declaration",
    )?;
    require(
        program.types.compatible(function.result, *result)
            && program.types.region_invariant(function.result, *result),
        "function result differs from its declaration",
    )?;
    for (&id, &expected) in function.parameters.iter().zip(parameters) {
        let actual = function
            .locals
            .get(id.0 as usize)
            .ok_or_else(|| InvariantError("invalid function parameter local".into()))?
            .ty;
        require(
            program.types.compatible(actual, expected)
                && program.types.region_invariant(actual, expected),
            "function parameter type differs from its declaration",
        )?;
    }
    Ok(())
}

pub(super) fn expression(
    program: &Program,
    function: &Function,
    expression: &Expr,
) -> Result<(), InvariantError> {
    match &expression.kind {
        ExprKind::Local(id) => local(function, *id)?,
        ExprKind::Definition(id) | ExprKind::Record { definition: id, .. } => {
            definition(program, *id)?
        }
        ExprKind::ConstTerm(id) => constant(program, *id, expression.ty)?,
        ExprKind::RepeatConst { count, .. } => repeat_count(program, *count)?,
        ExprKind::Call {
            type_arguments,
            parameter_types,
            arguments,
            ..
        } => {
            for &argument in type_arguments {
                types::argument(program, argument)?;
            }
            parameters(program, parameter_types, arguments.len())?;
        }
        ExprKind::DynCall {
            trait_method,
            parameter_types,
            arguments,
            ..
        } => {
            definition(program, *trait_method)?;
            parameters(program, parameter_types, arguments.len())?;
        }
        ExprKind::DynCoerce { vtable, .. } => require(
            (*vtable as usize) < program.vtables.len(),
            "invalid dynamic vtable",
        )?,
        ExprKind::IsVariant { variant, .. } | ExprKind::VariantField { variant, .. } => {
            variant_definition(program, *variant)?
        }
        ExprKind::Match {
            temporary, arms, ..
        } => {
            local(function, *temporary)?;
            for arm in arms {
                pattern(program, function, &arm.pattern)?;
            }
        }
        ExprKind::Error => {
            return Err(InvariantError("error node escaped the type checker".into()));
        }
        _ => {}
    }
    Ok(())
}

fn repeat_count(program: &Program, count: crate::types::ConstId) -> Result<(), InvariantError> {
    let term = program
        .types
        .constant_terms()
        .get(count.0 as usize)
        .ok_or_else(|| InvariantError("repeat has an invalid constant ID".into()))?;
    require(
        matches!(
            program.types.get(term.ty),
            Ty::Integer {
                signed: false,
                bits: 0
            }
        ),
        "repeat count is not usize",
    )
}

fn parameters(program: &Program, types: &[TyId], count: usize) -> Result<(), InvariantError> {
    require(
        types.len() == count,
        "call parameter dimensions do not match",
    )?;
    for &ty in types {
        require(
            ty != TyId::ERROR && (ty.0 as usize) < program.types.values().len(),
            "invalid call parameter type",
        )?;
        require(
            program.types.valid_region_scope(ty),
            "call parameter has an escaping bound region",
        )?;
    }
    Ok(())
}

fn constant(program: &Program, id: crate::types::ConstId, ty: TyId) -> Result<(), InvariantError> {
    require(
        program
            .types
            .constant_terms()
            .get(id.0 as usize)
            .is_some_and(|term| term.ty == ty),
        "constant expression type/ID mismatch",
    )
}

fn definition(program: &Program, id: DefId) -> Result<(), InvariantError> {
    require(
        (id.0 as usize) < program.definitions.len(),
        "expression has an invalid definition ID",
    )
}
fn local(function: &Function, id: LocalId) -> Result<(), InvariantError> {
    require(
        (id.0 as usize) < function.locals.len(),
        "expression has an invalid local ID",
    )
}
fn variant_definition(program: &Program, id: DefId) -> Result<(), InvariantError> {
    definition(program, id)?;
    require(
        matches!(
            program.definitions[id.0 as usize].kind,
            DefinitionKind::Variant { .. }
        ),
        "expected an enum variant definition",
    )
}

fn pattern(program: &Program, function: &Function, root: &Pattern) -> Result<(), InvariantError> {
    let mut pending = vec![(root, 0)];
    let mut remaining = 200_000usize;
    while let Some((pattern, depth)) = pending.pop() {
        require(
            remaining > 0 && depth < 128,
            "pattern validation limit exceeded",
        )?;
        remaining -= 1;
        require(
            pattern.ty != TyId::ERROR && (pattern.ty.0 as usize) < program.types.values().len(),
            "pattern has an invalid type",
        )?;
        match &pattern.kind {
            PatternKind::Binding { local: id, .. } => local(function, *id)?,
            PatternKind::Variant { definition, fields } => {
                variant_definition(program, *definition)?;
                for field in fields {
                    pending.push((field, depth + 1));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub(super) fn expression_statements(kind: &ExprKind, visit: &mut dyn FnMut(StmtId)) {
    if let ExprKind::BlockValue { body, .. } = kind {
        for &statement in &body.statements {
            visit(statement);
        }
    }
}

pub(super) fn locals_and_clauses(
    program: &Program,
    function: &Function,
) -> Result<(), InvariantError> {
    let types = program.types.values().len();
    for local in &function.locals {
        require(
            local.ty != TyId::ERROR && (local.ty.0 as usize) < types,
            "local has an invalid type",
        )?;
        require(
            program.types.valid_region_scope(local.ty),
            "local has an escaping bound region",
        )?;
    }
    for parameter in &function.parameters {
        require(
            (parameter.0 as usize) < function.locals.len(),
            "parameter has an invalid local ID",
        )?;
    }
    for clause in &function.clauses {
        require(
            (clause.predicate.0 as usize) < function.expressions.len(),
            "clause has an invalid expression ID",
        )?;
        body::clause_binding(program, function, clause)?;
    }

    Ok(())
}

pub(super) fn statements(_program: &Program, function: &Function) -> Result<(), InvariantError> {
    for statement in &function.statements {
        let mut invalid = false;
        stmt_expressions(&statement.kind, &mut |id| {
            invalid |= id.0 as usize >= function.expressions.len()
        });
        require(!invalid, "statement has an invalid expression ID")?;
        match statement.kind {
            StmtKind::Declare { local, .. } | StmtKind::ForIn { local, .. } => require(
                (local.0 as usize) < function.locals.len(),
                "statement has an invalid local ID",
            )?,
            StmtKind::Error => {
                return Err(InvariantError(
                    "error statement escaped the type checker".into(),
                ));
            }
            StmtKind::Defer { ref captures, .. } => require(
                captures
                    .iter()
                    .all(|(local, _)| (local.0 as usize) < function.locals.len()),
                "defer capture has an invalid local ID",
            )?,
            _ => {}
        }
    }
    for statement in &function.body.statements {
        require(
            (statement.0 as usize) < function.statements.len(),
            "body has an invalid statement ID",
        )?;
    }

    Ok(())
}
