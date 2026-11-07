use super::*;

pub(crate) fn dependencies(
    body: &Body,
    hir: &hir::Program,
    properties: &Properties,
) -> BTreeSet<hir::DefId> {
    let mut dependencies = BTreeSet::new();
    for block in &body.blocks {
        if let Terminator::Drop { place, .. } = &block.terminator
            && let Some(ty) = place_type(body, place, hir, properties)
            && let Some(methods) = methods(ty, hir, properties)
        {
            dependencies.extend(methods);
        }
    }
    dependencies
}

pub(in crate::mir::borrow) fn known(
    ty: TyId,
    context: &Context<'_>,
) -> Option<BTreeSet<crate::external::AssumptionId>> {
    let mut assumptions = BTreeSet::new();
    for method in methods(ty, context.hir, context.properties)? {
        let summary = context.summaries.functions[method.0 as usize].as_ref()?;
        if !summary.complete || summary.panic.is_some() || summary.cancel.is_some() {
            return None;
        }
        let normal = summary.normal.as_ref()?;
        if summary.accesses.iter().any(|access| {
            access.write
                && access.target.input != 0
                && !scalar_target(method, &access.target, context)
        }) || normal.writes.iter().any(|write| {
            write.target.input != 0 && !scalar_target(method, &write.target, context)
                || !write.value.fields.is_empty()
                || write.value.unknown
        }) {
            return None;
        }
        assumptions.extend(&summary.assumptions);
    }
    Some(assumptions)
}

fn scalar_target(method: hir::DefId, target: &Footprint, context: &Context<'_>) -> bool {
    let Some(frame) = context.summaries.frames[method.0 as usize].as_ref() else {
        return false;
    };
    let Some(input) = frame.inputs.get(target.input as usize) else {
        return false;
    };
    let Ty::Reference { inner, .. } = context.hir.types.get(input.ty) else {
        return false;
    };
    let mut ty = *inner;
    let mut variant = None;
    for step in &target.path {
        ty = match step {
            Step::Variant(selected) => {
                variant = Some(*selected);
                continue;
            }
            Step::Field(field) => {
                let fields = variant.take().map_or_else(
                    || context.properties.fields(ty),
                    |variant| context.properties.variant_fields(ty, variant),
                );
                let Some(&field) = fields.and_then(|fields| fields.get(*field as usize)) else {
                    return false;
                };
                field
            }
            Step::Element => match context.hir.types.get(ty) {
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    *inner
                }
                _ => return false,
            },
            Step::Deref => match context.hir.types.get(ty) {
                Ty::Reference { inner, .. } => *inner,
                _ => return false,
            },
        };
    }
    // Scalar data does not change loan, raw-pointer, callable or vtable identity.
    // Aggregate/reference stores still require full destructor summary replay.
    matches!(
        context.hir.types.get(ty),
        Ty::Bool | Ty::Char | Ty::Integer { .. } | Ty::Float { .. }
    )
}

fn methods(ty: TyId, hir: &hir::Program, properties: &Properties) -> Option<BTreeSet<hir::DefId>> {
    let mut methods = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) || !properties.get(ty).may_drop {
            continue;
        }
        if seen.len() > 4096 {
            return None;
        }
        if let Some(selection) = hir::traits::select_drop(hir, ty).ok()? {
            methods.insert(selection.definition);
        }
        match hir.types.get(ty) {
            Ty::Named { definition, .. } => {
                if let Some(fields) = properties.fields(ty) {
                    pending.extend(fields);
                } else {
                    let enumeration = hir
                        .enums
                        .iter()
                        .find(|value| value.definition == *definition)?;
                    for &variant in &enumeration.variants {
                        pending.extend(properties.variant_fields(ty, variant)?);
                    }
                }
            }
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => pending.push(*inner),
            _ => return None,
        }
    }
    Some(methods)
}

fn place_type(
    body: &Body,
    place: &Place,
    hir: &hir::Program,
    properties: &Properties,
) -> Option<TyId> {
    let local = body.local(place.local);
    let mut ty = local.ty;
    let mut variant = None;
    for (index, projection) in place.projection.iter().enumerate() {
        ty = match projection {
            Projection::Deref if index == 0 && local.kind == LocalKind::Address => ty,
            Projection::Deref => match hir.types.get(ty) {
                Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                _ => return None,
            },
            Projection::Downcast(_) => ty,
            Projection::Field(field) => *variant
                .map_or_else(
                    || properties.fields(ty),
                    |variant| properties.variant_fields(ty, variant),
                )?
                .get(*field as usize)?,
            Projection::Index(_) => match hir.types.get(ty) {
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    *inner
                }
                _ => return None,
            },
        };
        variant = if let Projection::Downcast(variant) = projection {
            Some(*variant)
        } else {
            None
        };
    }
    Some(ty)
}
