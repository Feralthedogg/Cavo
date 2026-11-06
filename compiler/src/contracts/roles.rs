//! Compiler roles are declarations of built-in semantics, never user function
//! names. The same structural checks run before registration and at HIR gates.
use super::*;
use crate::types::{Ty, TyId, TypeContext};

fn same(types: &TypeContext, left: TyId, right: TyId) -> bool {
    types.compatible(left, right) && types.region_invariant(left, right)
}

pub(crate) fn intrinsic_shape(types: &TypeContext, ty: TyId, role: Intrinsic) -> bool {
    let Ty::Function { parameters, result } = types.get(ty) else {
        return false;
    };
    let usize_ty = |ty| {
        matches!(
            types.get(ty),
            Ty::Integer {
                signed: false,
                bits: 0
            }
        )
    };
    let first = parameters.first().map(|&ty| types.get(ty));
    match role {
        Intrinsic::TaskJoin | Intrinsic::TaskIgnore => {
            parameters.len() == 1 && matches!(first, Some(Ty::Named { .. }))
        }
        Intrinsic::TaskCancel => {
            parameters.len() == 1
                && *result == TyId::VOID
                && matches!(first, Some(Ty::Reference { .. }))
        }
        Intrinsic::Length => {
            parameters.len() == 1
                && usize_ty(*result)
                && matches!(first, Some(Ty::Reference { inner, .. }) if matches!(types.get(*inner), Ty::Slice(_) | Ty::Array { .. } | Ty::SymbolicArray { .. } | Ty::Str))
        }
        Intrinsic::AsPtr | Intrinsic::AsMutPtr => {
            parameters.len() == 1
                && matches!((first, types.get(*result)),
            (Some(Ty::Reference { inner, mutable, .. }), Ty::Pointer { inner: out, constant })
            if same(types, *inner, *out) && (role == Intrinsic::AsPtr && *constant || role == Intrinsic::AsMutPtr && *mutable && !constant))
        }
        Intrinsic::Read | Intrinsic::ReadUnaligned | Intrinsic::Take => {
            parameters.len() == 1
                && matches!(first, Some(Ty::Pointer { inner, constant }) if same(types, *inner, *result) && (role != Intrinsic::Take || !constant))
        }
        Intrinsic::Initialize | Intrinsic::Replace | Intrinsic::WriteUnaligned => {
            parameters.len() == 2
                && *result == TyId::VOID
                && matches!(first, Some(Ty::Pointer { inner, constant: false }) if same(types, *inner, parameters[1]))
        }
        Intrinsic::Allocate => {
            parameters.len() == 1
                && usize_ty(parameters[0])
                && matches!(
                    types.get(*result),
                    Ty::Pointer {
                        constant: false,
                        ..
                    }
                )
        }
        Intrinsic::Deallocate => {
            parameters.len() == 1
                && *result == TyId::VOID
                && matches!(
                    first,
                    Some(Ty::Pointer {
                        constant: false,
                        ..
                    })
                )
        }
        Intrinsic::Offset => {
            parameters.len() == 2
                && usize_ty(parameters[1])
                && parameters[0] == *result
                && matches!(first, Some(Ty::Pointer { .. }))
        }
    }
}

pub(crate) fn predicate_shape(types: &TypeContext, ty: TyId, role: MemoryPredicate) -> bool {
    let Ty::Function { parameters, result } = types.get(ty) else {
        return false;
    };
    if *result != TyId::BOOL {
        return false;
    }
    let pointer = |index: usize| {
        parameters
            .get(index)
            .is_some_and(|&ty| matches!(types.get(ty), Ty::Pointer { .. }))
    };
    let count = |index: usize| {
        parameters.get(index).is_some_and(|&ty| {
            matches!(
                types.get(ty),
                Ty::Integer {
                    signed: false,
                    bits: 0
                }
            )
        })
    };
    match role {
        MemoryPredicate::Readable
        | MemoryPredicate::ReadableUnaligned
        | MemoryPredicate::Initialized
        | MemoryPredicate::ActiveUnion => parameters.len() == 2 && pointer(0) && count(1),
        MemoryPredicate::Writable | MemoryPredicate::WritableUnaligned => {
            parameters.len() == 2
                && count(1)
                && matches!(
                    types.get(parameters[0]),
                    Ty::Pointer {
                        constant: false,
                        ..
                    }
                )
        }
        MemoryPredicate::OwnedAllocation => {
            parameters.len() == 1
                && matches!(
                    types.get(parameters[0]),
                    Ty::Pointer {
                        constant: false,
                        ..
                    }
                )
        }
        MemoryPredicate::Disjoint => {
            parameters.len() == 4 && pointer(0) && count(1) && pointer(2) && count(3)
        }
        MemoryPredicate::BorrowedFrom => {
            parameters.len() == 2
                && pointer(0)
                && matches!(
                    types.get(parameters[1]),
                    Ty::Reference { .. } | Ty::Pointer { .. }
                )
        }
        MemoryPredicate::NoRetain | MemoryPredicate::NoCallback => {
            parameters.len() == 1
                && matches!(
                    types.get(parameters[0]),
                    Ty::Function { .. } | Ty::ForAll { .. }
                )
        }
        MemoryPredicate::Scalar => false,
    }
}

pub(crate) fn validate_hir(program: &hir::Program) -> Result<(), hir::InvariantError> {
    for (&id, &role) in &program.contracts.intrinsics {
        let definition = program
            .definitions
            .get(id.0 as usize)
            .ok_or_else(|| hir::InvariantError("intrinsic identity is out of range".into()))?;
        if definition.kind != hir::DefinitionKind::Function
            || definition.foreign_abi.is_some()
            || !definition.declaration_clauses.is_empty()
            || program.functions.iter().any(|f| f.definition == id)
            || !intrinsic_shape(&program.types, definition.ty, role)
        {
            return Err(hir::InvariantError(
                "intrinsic metadata no longer describes a bodyless compiler operation".into(),
            ));
        }
    }
    for (&id, predicate) in &program.contracts.predicates {
        let definition = program
            .definitions
            .get(id.0 as usize)
            .ok_or_else(|| hir::InvariantError("predicate identity is out of range".into()))?;
        if definition.kind != hir::DefinitionKind::Contract
            || predicate
                .memory
                .is_some_and(|role| !predicate_shape(&program.types, definition.ty, role))
        {
            return Err(hir::InvariantError(
                "logical predicate metadata has an incompatible declaration".into(),
            ));
        }
    }
    Ok(())
}
