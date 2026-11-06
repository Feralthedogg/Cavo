use crate::{
    hir::{self, ExprKind as H, StmtKind as S},
    syntax::ast::UnaryOp,
    types::Ty,
};
use std::collections::HashSet;

pub(crate) fn eligible(program: &hir::Program, root: hir::DefId) -> bool {
    let mut pending = vec![root];
    let mut visited = HashSet::new();
    while let Some(definition) = pending.pop() {
        if !visited.insert(definition) {
            continue;
        }
        if visited.len() > 4096 {
            return false;
        }
        if let Some(intrinsic) = program.contracts.intrinsics.get(&definition) {
            if matches!(
                intrinsic,
                super::Intrinsic::Length | super::Intrinsic::Read | super::Intrinsic::ReadUnaligned
            ) {
                continue;
            }
            return false;
        }
        if let Some(contract) = program.modular.functions.get(&definition)
            && !program.constants.functions.contains_key(&definition)
        {
            if !contract.pure || !crate::modular::usable(program, definition) {
                return false;
            }
            continue;
        }
        let Some(body) = program
            .functions
            .iter()
            .find(|body| body.definition == definition)
        else {
            return false;
        };
        if !body_is_pure(program, body, &mut pending) {
            return false;
        }
    }
    true
}

fn body_is_pure(
    program: &hir::Program,
    body: &hir::Function,
    pending: &mut Vec<hir::DefId>,
) -> bool {
    if body
        .locals
        .iter()
        .any(|local| !trivial_drop(program, local.ty, 0))
    {
        return false;
    }
    for statement in &body.statements {
        if matches!(statement.kind, S::TaskScope { .. } | S::Assume(_)) {
            return false;
        }
        if let S::Assign { target, .. } = statement.kind
            && !owned_place(body, target)
        {
            return false;
        }
    }
    for expression in &body.expressions {
        match expression.kind {
            H::Call { callee, .. } => {
                let Some(target) = direct(body, callee) else {
                    return false;
                };
                pending.push(target);
            }
            H::DynCall { .. } | H::Spawn { .. } => return false,
            H::Unary {
                op: UnaryOp::Spawn, ..
            } => return false,
            _ => {}
        }
    }
    true
}

fn direct(body: &hir::Function, mut id: hir::ExprId) -> Option<hir::DefId> {
    for _ in 0..128 {
        match body.expressions[id].kind {
            H::Group(inner) => id = inner,
            H::Definition(definition) => return Some(definition),
            _ => return None,
        }
    }
    None
}

fn owned_place(body: &hir::Function, mut id: hir::ExprId) -> bool {
    for _ in 0..128 {
        match body.expressions[id].kind {
            H::Group(inner) | H::Field { base: inner, .. } | H::Index { base: inner, .. } => {
                id = inner
            }
            H::Local(_) => return true,
            _ => return false,
        }
    }
    false
}

fn trivial_drop(program: &hir::Program, ty: crate::types::TyId, depth: usize) -> bool {
    if depth >= 64 {
        return false;
    }
    match program.types.get(ty) {
        Ty::Void
        | Ty::Bool
        | Ty::Char
        | Ty::Integer { .. }
        | Ty::Float { .. }
        | Ty::Reference { .. }
        | Ty::Pointer { .. }
        | Ty::Function { .. }
        | Ty::ForAll { .. } => true,
        Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => {
            trivial_drop(program, *inner, depth + 1)
        }
        Ty::Parameter { owner, index } => hir::traits::parameter_has_role(
            program,
            *owner,
            *index,
            hir::traits::LanguageItem::Copy,
        ),
        Ty::Named { definition, .. } => {
            !hir::traits::has_drop(program, ty)
                && program
                    .records
                    .iter()
                    .find(|record| record.definition == *definition)
                    .is_some_and(|record| {
                        record
                            .fields
                            .iter()
                            .all(|field| trivial_drop(program, field.ty, depth + 1))
                    })
        }
        _ => false,
    }
}
