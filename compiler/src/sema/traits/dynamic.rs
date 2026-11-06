//! Object-safety checks preserve the receiver ABI boundary. A dyn method may
//! erase only the receiver's concrete Self; other occurrences require a type
//! that the caller cannot recover from the vtable slot alone.

use crate::{
    hir::{self, DefId},
    source::Span,
    types::{GenericArg, GenericParamKind, Ty, TyId},
};
use std::collections::HashSet;

const TYPE_WORK_LIMIT: usize = 4096;

#[derive(Clone, Copy, Debug)]
pub(crate) struct ObjectMethod {
    pub definition: DefId,
    pub self_ty: TyId,
    /// Self plus the trait's parameters; method-owned generics cannot be erased.
    pub inherited_parameters: u32,
}

#[derive(Debug)]
pub(crate) struct DynamicError {
    pub span: Span,
    pub message: String,
}

pub(crate) fn object_safe_method(
    program: &hir::Program,
    method: ObjectMethod,
) -> Result<(), DynamicError> {
    let declaration = &program.definitions[method.definition.0 as usize];
    let span = declaration.span;
    if declaration.generic_parameter_kinds.len() > TYPE_WORK_LIMIT {
        return Err(error(
            span,
            "dyn method generic parameters exceed their resource limit",
        ));
    }
    let own = declaration
        .generic_parameter_kinds
        .get(method.inherited_parameters as usize..)
        .ok_or_else(|| error(span, "dyn method inherited parameters are invalid"))?;
    if own.iter().any(|kind| *kind != GenericParamKind::Lifetime) {
        return Err(error(
            span,
            "a dyn method cannot declare type or const parameters",
        ));
    }
    if declaration.foreign_abi.is_some() {
        return Err(error(span, "a dyn method requires the managed method ABI"));
    }
    let (parameters, result) = signature(program, declaration.ty, span)?;
    check_receiver(program, parameters.first().copied(), method.self_ty, span)?;
    for ty in parameters.iter().skip(1).copied().chain([result]) {
        if contains_self(program, ty, method.self_ty, span)? {
            return Err(error(
                span,
                "Self may only occur in the receiver of a dyn method",
            ));
        }
    }
    Ok(())
}

/// Slot order is declaration order. The retained declaration/implementation IDs
/// also retain the effect and contract identities; this does not invent an ABI
/// cast or treat an absent implementation body as a verified implementation.
pub(crate) fn plan_vtable(
    program: &mut hir::Program,
    trait_ref: &hir::traits::TraitRef,
    concrete: TyId,
) -> Result<hir::traits::Vtable, DynamicError> {
    hir::traits::require_trait(program, concrete, trait_ref).map_err(|problem| {
        error(
            program.definitions[trait_ref.definition.0 as usize].span,
            problem.to_string(),
        )
    })?;
    let references = hir::traits::supertraits(program, trait_ref).map_err(|problem| {
        error(
            program.definitions[trait_ref.definition.0 as usize].span,
            problem.to_string(),
        )
    })?;
    let mut slots = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for reference in references {
        let trait_ = program
            .traits
            .iter()
            .find(|trait_| trait_.definition == reference.definition)
            .ok_or_else(|| {
                error(
                    program.definitions[reference.definition.0 as usize].span,
                    "dyn requires a declared trait",
                )
            })?;
        let methods = trait_.methods.clone();
        for method in methods {
            if slots.len() >= TYPE_WORK_LIMIT || !seen.insert(method.definition) {
                return Err(error(
                    program.definitions[method.definition.0 as usize].span,
                    "dyn vtable has ambiguous or excessive inherited methods",
                ));
            }
            validate_slot_method(program, &method)?;
            slots.push(vtable_slot(
                program,
                &reference,
                concrete,
                method.definition,
                method.inherited_parameters,
            )?);
        }
    }
    Ok(hir::traits::Vtable {
        trait_ref: trait_ref.clone(),
        concrete,
        slots,
    })
}

fn validate_slot_method(
    program: &mut hir::Program,
    method: &hir::traits::TraitMethod,
) -> Result<(), DynamicError> {
    let self_ty = program.types.intern(Ty::Parameter {
        owner: method.definition,
        index: 0,
    });
    object_safe_method(
        program,
        ObjectMethod {
            definition: method.definition,
            self_ty,
            inherited_parameters: method.inherited_parameters,
        },
    )
}

fn vtable_slot(
    program: &mut hir::Program,
    trait_ref: &hir::traits::TraitRef,
    concrete: TyId,
    method: DefId,
    inherited_parameters: u32,
) -> Result<hir::traits::VtableSlot, DynamicError> {
    let span = program.definitions[method.0 as usize].span;
    let arguments = method_arguments(program, trait_ref, concrete, method, inherited_parameters)?;
    let selected = hir::traits::select_method(program, method, &arguments)
        .map_err(|_| {
            error(
                span,
                "dyn conversion could not select a unique implementation",
            )
        })?
        .ok_or_else(|| {
            error(
                span,
                "dyn conversion requires a matching trait implementation",
            )
        })?;
    let declaration = program.definitions[method.0 as usize].ty;
    hir::traits::check_bounds(program, selected.definition, &selected.type_arguments)
        .map_err(|problem| error(span, problem.to_string()))?;
    let signature = program.types.substitute(declaration, method, &arguments);
    check_slot_signature(program, method, signature, &selected, span)?;
    Ok(hir::traits::VtableSlot {
        declaration: method,
        implementation: selected.definition,
        signature,
        type_arguments: selected.type_arguments,
    })
}

fn method_arguments(
    program: &mut hir::Program,
    trait_ref: &hir::traits::TraitRef,
    concrete: TyId,
    method: DefId,
    inherited_parameters: u32,
) -> Result<Vec<GenericArg>, DynamicError> {
    let declaration = &program.definitions[method.0 as usize];
    if declaration.generic_parameter_kinds.len() > TYPE_WORK_LIMIT {
        return Err(error(
            declaration.span,
            "dyn method generic parameters exceed their resource limit",
        ));
    }
    if inherited_parameters as usize != trait_ref.arguments.len() + 1 {
        return Err(error(
            declaration.span,
            "dyn trait arguments do not match its method prefix",
        ));
    }
    let mut arguments = Vec::with_capacity(declaration.generic_parameter_kinds.len());
    arguments.push(GenericArg::Type(concrete));
    arguments.extend(&trait_ref.arguments);
    for kind in &declaration.generic_parameter_kinds[inherited_parameters as usize..] {
        if *kind != GenericParamKind::Lifetime {
            return Err(error(
                declaration.span,
                "a dyn method cannot declare type or const parameters",
            ));
        }
        arguments.push(GenericArg::Lifetime(program.types.fresh_region()));
    }
    Ok(arguments)
}

fn check_slot_signature(
    program: &mut hir::Program,
    method: DefId,
    declared: TyId,
    selected: &hir::traits::MethodSelection,
    span: Span,
) -> Result<(), DynamicError> {
    let implementation = &program.definitions[selected.definition.0 as usize];
    let actual = program.types.substitute(
        implementation.ty,
        selected.definition,
        &selected.type_arguments,
    );
    let declared = program
        .types
        .generalize_callable(declared, method)
        .ok_or_else(|| {
            error(
                span,
                "dyn declaration lifetime generalization exceeded its limit",
            )
        })?;
    let actual = program
        .types
        .generalize_callable(actual, selected.definition)
        .ok_or_else(|| {
            error(
                span,
                "dyn implementation lifetime generalization exceeded its limit",
            )
        })?;
    if !program.types.compatible(actual, declared) {
        return Err(error(
            span,
            "dyn implementation does not preserve its declared signature",
        ));
    }
    Ok(())
}

fn signature(
    program: &hir::Program,
    mut ty: TyId,
    span: Span,
) -> Result<(&[TyId], TyId), DynamicError> {
    if let Ty::ForAll { inner, .. } = program.types.get(ty) {
        ty = *inner;
    }
    match program.types.get(ty) {
        Ty::Function { parameters, result } => Ok((parameters, *result)),
        _ => Err(error(span, "a dyn method must have a function signature")),
    }
}

fn check_receiver(
    program: &hir::Program,
    receiver: Option<TyId>,
    self_ty: TyId,
    span: Span,
) -> Result<(), DynamicError> {
    let Some(receiver) = receiver else {
        return Err(error(
            span,
            "a dyn method requires a Self reference receiver",
        ));
    };
    match program.types.get(receiver) {
        Ty::Reference { inner, .. } if *inner == self_ty => Ok(()),
        _ => Err(error(span, "a dyn receiver must be &Self or &mut Self")),
    }
}

fn contains_self(
    program: &hir::Program,
    root: TyId,
    self_ty: TyId,
    span: Span,
) -> Result<bool, DynamicError> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    let mut remaining = TYPE_WORK_LIMIT;
    while let Some(ty) = pending.pop() {
        remaining = remaining
            .checked_sub(1)
            .ok_or_else(|| error(span, "dyn method type analysis exceeds its resource limit"))?;
        if ty == self_ty {
            return Ok(true);
        }
        if !seen.insert(ty) {
            continue;
        }
        type_children(program.types.get(ty), &mut pending, span)?;
    }
    Ok(false)
}

fn type_children(ty: &Ty, pending: &mut Vec<TyId>, span: Span) -> Result<(), DynamicError> {
    let mut push = |child| {
        if pending.len() >= TYPE_WORK_LIMIT {
            return Err(error(
                span,
                "dyn method type analysis exceeds its resource limit",
            ));
        }
        pending.push(child);
        Ok(())
    };
    match ty {
        Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
            for ty in arguments.iter().filter_map(|argument| argument.ty()) {
                push(ty)?;
            }
        }
        Ty::Reference { inner, .. }
        | Ty::Pointer { inner, .. }
        | Ty::Array { inner, .. }
        | Ty::SymbolicArray { inner, .. }
        | Ty::Slice(inner)
        | Ty::ForAll { inner, .. } => push(*inner)?,
        Ty::Function { parameters, result } => {
            for &parameter in parameters {
                push(parameter)?;
            }
            push(*result)?;
        }
        _ => {}
    }
    Ok(())
}

fn error(span: Span, message: impl Into<String>) -> DynamicError {
    DynamicError {
        span,
        message: message.into(),
    }
}
