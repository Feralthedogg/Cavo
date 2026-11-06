use super::*;

pub(super) fn captures(core: &super::super::Body) -> Result<Vec<Option<Place>>, Error> {
    let mut captures = vec![None; core.locals.len()];
    for block in &core.blocks {
        for statement in &block.statements {
            if let super::super::StatementKind::Assign {
                destination,
                value: Rvalue::AddressOf(place),
            } = &statement.kind
            {
                let target = &mut captures[destination.local.0 as usize];
                if target.as_ref().is_some_and(|old| old != place) {
                    return Err(Error(
                        "drop elaboration needs a unique captured assignment place".into(),
                    ));
                }
                *target = Some(place.clone());
            }
        }
    }
    Ok(captures)
}

pub(super) fn droppable_places(
    core: &super::super::Body,
    glue: &Glues<'_>,
) -> Result<HashSet<Place>, Error> {
    let mut places = HashSet::new();
    let mut record = |place: &Place| {
        if glue.properties.get(place_type(place, core, glue)?).may_drop {
            places.insert(place.clone());
            if places.len() >= LIMIT {
                return Err(Error("drop place limit exceeded".into()));
            }
        }
        Ok(())
    };
    for (index, local) in core.locals.iter().enumerate() {
        if local.kind != LocalKind::Address {
            record(&Place::local(super::super::LocalId(index as u32)))?;
        }
    }
    for block in &core.blocks {
        for statement in &block.statements {
            if let super::super::StatementKind::Assign { destination, value } = &statement.kind
                && !matches!(value, Rvalue::AddressOf(_))
            {
                record(destination)?;
                visit_moves(value, &mut record)?;
            }
            if let super::super::StatementKind::IteratorStart { value, iterator } = &statement.kind
            {
                visit_move(value, &mut record)?;
                record(&Place::local(*iterator))?;
            }
        }
        visit_exit(&block.terminator, &mut record)?;
    }
    Ok(places)
}

fn place_type(place: &Place, core: &super::super::Body, glue: &Glues<'_>) -> Result<TyId, Error> {
    let local = &core.locals[place.local];
    let mut ty = local.ty;
    let mut variant = None;
    for (index, projection) in place.projection.iter().enumerate() {
        ty = match projection {
            Projection::Deref if index == 0 && local.kind == LocalKind::Address => ty,
            Projection::Deref => match glue.hir.types.get(ty) {
                Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                _ => return Err(Error("invalid drop dereference".into())),
            },
            Projection::Downcast(selected) => {
                if glue.properties.variant_fields(ty, *selected).is_none() {
                    return Err(Error("invalid enum drop projection".into()));
                }
                variant = Some(*selected);
                ty
            }
            Projection::Field(index) => variant
                .take()
                .map_or_else(
                    || glue.properties.fields(ty),
                    |variant| glue.properties.variant_fields(ty, variant),
                )
                .and_then(|fields| fields.get(*index as usize))
                .copied()
                .ok_or_else(|| Error("invalid drop field".into()))?,
            Projection::Index(_) => match glue.hir.types.get(ty) {
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    *inner
                }
                _ => return Err(Error("invalid drop index".into())),
            },
        };
    }
    Ok(ty)
}

fn visit_move(
    value: &Operand,
    visit: &mut impl FnMut(&Place) -> Result<(), Error>,
) -> Result<(), Error> {
    if let Operand::Move(place) = value {
        visit(place)?;
    }
    Ok(())
}
pub(super) fn visit_moves(
    value: &Rvalue,
    visit: &mut impl FnMut(&Place) -> Result<(), Error>,
) -> Result<(), Error> {
    match value {
        Rvalue::Use(value)
        | Rvalue::Unary { operand: value, .. }
        | Rvalue::Repeat { value, .. }
        | Rvalue::RepeatConst { value, .. }
        | Rvalue::DynCoerce { value, .. }
        | Rvalue::ArrayToSlice(value) => visit_move(value, visit)?,
        Rvalue::Binary { left, right, .. } => {
            visit_move(left, visit)?;
            visit_move(right, visit)?;
        }
        Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
            for value in values {
                visit_move(value, visit)?;
            }
        }
        Rvalue::Record { fields, .. } => {
            for (_, value) in fields {
                visit_move(value, visit)?;
            }
        }
        Rvalue::Borrow { .. }
        | Rvalue::AddressOf(_)
        | Rvalue::Length(_)
        | Rvalue::IsVariant { .. } => {}
    }
    Ok(())
}
fn visit_exit(
    exit: &super::super::Terminator,
    visit: &mut impl FnMut(&Place) -> Result<(), Error>,
) -> Result<(), Error> {
    use super::super::Terminator as T;
    match exit {
        T::Call {
            callee,
            arguments,
            destination,
            ..
        }
        | T::Spawn {
            callee,
            arguments,
            destination,
            ..
        } => {
            visit_move(callee, visit)?;
            for value in arguments {
                visit_move(value, visit)?;
            }
            visit(destination)?;
        }
        T::DynCall {
            receiver,
            arguments,
            destination,
            ..
        } => {
            visit_move(receiver, visit)?;
            for value in arguments {
                visit_move(value, visit)?;
            }
            visit(destination)?;
        }
        T::IteratorNext { destination, .. } => visit(destination)?,
        T::Checked {
            value, destination, ..
        } => {
            visit_moves(value, visit)?;
            visit(destination)?;
        }
        T::Drop { place, .. } => visit(place)?,
        T::Switch { condition, .. } => visit_move(condition, visit)?,
        T::Goto(_)
        | T::TaskDrain { .. }
        | T::Bounds { .. }
        | T::Return
        | T::Resume(_)
        | T::Abort
        | T::Unreachable => {}
    }
    Ok(())
}
