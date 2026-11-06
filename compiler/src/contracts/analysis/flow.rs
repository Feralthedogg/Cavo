use super::*;

impl Engine<'_> {
    pub(super) fn operand(&self, operand: &Operand, state: &State) -> Value {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => state.read(place),
            Operand::Constant { value, .. } => scalar(value),
            Operand::ConstTerm { value, .. } => Value {
                integer: self.context.hir.types.const_usize(*value),
                ..Value::default()
            },
            Operand::Function { definition, .. } => Value {
                trust: self
                    .context
                    .dependencies
                    .get(definition)
                    .cloned()
                    .unwrap_or_default(),
                function: Some(*definition),
                ..Value::default()
            },
            _ => Value::default(),
        }
    }

    pub(super) fn statement(&self, statement: &StatementKind, span: Span, state: &mut State) {
        match statement {
            StatementKind::RegistryStart(local) => *state.local_mut(*local) = Value::default(),
            StatementKind::StorageLive(local) => self.storage_live(*local, span, state),
            StatementKind::StorageDead(local) => {
                state.expire(AllocationId::Local(local.0), self.basis(span))
            }
            StatementKind::Argument(local) => self.argument(*local, span, state),
            StatementKind::Assign { destination, value } => {
                self.assignment(destination, value, span, state)
            }
            StatementKind::Contract(contract) => self.contract(contract, span, state),
            StatementKind::IteratorStart { iterator, value } => {
                let value = self.operand(value, state);
                self.store(&Place::local(*iterator), value, span, state);
            }
            StatementKind::EnterScope(scope) => state.scopes.push(*scope),
            StatementKind::ExitScope(scope) => {
                state.assumptions.retain(|fact| fact.scope != *scope);
                state.scopes.pop();
            }
        }
    }

    fn storage_live(&self, local: LocalId, span: Span, state: &mut State) {
        let id = AllocationId::Local(local.0);
        state.expire(id, self.basis(span));
        let size = self.size(self.context.body.local(local).ty);
        state.allocations.insert(
            id,
            Allocation {
                initialized_type: None,
                raw_touched: false,
                live: Truth::Yes,
                initialized: Truth::No,
                initialized_ranges: BTreeSet::new(),
                uninitialized_ranges: BTreeSet::new(),
                extent: size.map(|size| size.bytes),
                alignment: size.map_or(0, |size| size.alignment),
                owned: Truth::No,
                basis: self.basis(span),
                invalidation: None,
                active_union: None,
            },
        );
        *state.local_mut(local) = Value::default();
    }

    fn assignment(&self, destination: &Place, source: &Rvalue, span: Span, state: &mut State) {
        if let Rvalue::AddressOf(place) = source {
            state.places[destination.local.0 as usize] = self.capture_place(place, state);
            return;
        }
        if let Rvalue::Borrow { place, .. } = source
            && place.projection.is_empty()
            && let Some(allocation) = state
                .allocations
                .get_mut(&AllocationId::Local(place.local.0))
            && !allocation.raw_touched
        {
            allocation.initialized = Truth::Yes;
            allocation.initialized_type = Some(self.place_type(place));
        }
        let value = self.evaluate_value(source, span, state);
        self.consume_moves(source, state);
        self.store(destination, value, span, state);
        if matches!(source, Rvalue::Borrow { .. }) {
            state.new_reference();
        }
    }

    fn consume_moves(&self, value: &Rvalue, state: &mut State) {
        let mut consume = |operand: &Operand| {
            if let Operand::Move(place) = operand
                && place.projection.is_empty()
            {
                // Moving a whole value leaves storage live but uninitialized.
                // Projected moves retain conservative partial-drop effects.
                let (slot, allocation) = state.local_storage(place.local);
                *slot = Value::default();
                if let Some(allocation) = allocation {
                    allocation.initialized = Truth::No;
                    allocation.initialized_type = None;
                    allocation.initialized_ranges.clear();
                    allocation.active_union = None;
                }
            }
        };
        match value {
            Rvalue::Use(value)
            | Rvalue::Unary { operand: value, .. }
            | Rvalue::Repeat { value, .. }
            | Rvalue::RepeatConst { value, .. }
            | Rvalue::ArrayToSlice(value)
            | Rvalue::DynCoerce { value, .. } => consume(value),
            Rvalue::Binary { left, right, .. } => {
                consume(left);
                consume(right);
            }
            Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
                for value in values {
                    consume(value);
                }
            }
            Rvalue::Record { fields, .. } => {
                for (_, value) in fields {
                    consume(value);
                }
            }
            _ => {}
        }
    }

    fn argument(&self, local: LocalId, span: Span, state: &mut State) {
        let ty = self.context.body.local(local).ty;
        state.local_mut(local).opaque_references = self.context.properties.get(ty).references;
        let (inner, mutable, valid) = match self.context.hir.types.get(ty) {
            Ty::Reference { inner, mutable, .. } => (*inner, *mutable, true),
            Ty::Pointer { inner, .. } => (*inner, false, false),
            _ => {
                if let Some(a) = state.allocations.get_mut(&AllocationId::Local(local.0)) {
                    a.initialized = Truth::Yes;
                    a.initialized_type = Some(ty);
                }
                return;
            }
        };
        let basis = self.basis(span);
        let id = AllocationId::Input(local.0);
        let size = self.size(inner);
        state.allocations.insert(
            id,
            Allocation {
                initialized_type: valid.then_some(inner),
                raw_touched: false,
                live: if valid { Truth::Yes } else { Truth::Unknown },
                initialized_ranges: BTreeSet::new(),
                uninitialized_ranges: BTreeSet::new(),
                initialized: if valid { Truth::Yes } else { Truth::Unknown },
                extent: size.filter(|_| valid).map(|size| size.bytes),
                alignment: size.filter(|_| valid).map_or(0, |size| size.alignment),
                owned: if valid { Truth::No } else { Truth::Unknown },
                basis: basis.clone(),
                invalidation: None,
                active_union: None,
            },
        );
        state.local_mut(local).opaque_references = false;
        state.local_mut(local).pointer = Some(Pointer {
            owned: if valid { Truth::No } else { Truth::Unknown },
            ancestors: BTreeSet::new(),
            allocation: id,
            offset: Some(0),
            raw: !valid,
            readable: if valid { Truth::Yes } else { Truth::Unknown },
            writable: if valid {
                if mutable { Truth::Yes } else { Truth::No }
            } else {
                Truth::Unknown
            },
            unaligned: false,
            expired: false,
            basis,
        });
        if let Some(a) = state.allocations.get_mut(&AllocationId::Local(local.0)) {
            a.initialized = Truth::Yes;
            a.initialized_type = Some(ty);
        }
    }

    pub(super) fn evaluate_value(&self, value: &Rvalue, span: Span, state: &State) -> Value {
        match value {
            Rvalue::Use(value) | Rvalue::ArrayToSlice(value) | Rvalue::DynCoerce { value, .. } => {
                self.operand(value, state)
            }
            Rvalue::Borrow { mutable, place } => self.borrow_value(place, *mutable, span, state),
            Rvalue::AddressOf(_) => Value::default(),
            Rvalue::Binary { op, left, right } => {
                binary(*op, self.operand(left, state), self.operand(right, state))
            }
            Rvalue::Unary { op, operand } => unary(*op, self.operand(operand, state)),
            Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => Value::aggregate(
                values
                    .iter()
                    .enumerate()
                    .map(|(index, value)| (vec![index as u32], self.operand(value, state)))
                    .collect(),
                None,
            ),
            Rvalue::Record { definition, fields } => {
                let active = (self.context.hir.definitions[definition].kind
                    == hir::DefinitionKind::Union)
                    .then(|| fields.first().map(|(index, _)| *index))
                    .flatten();
                Value::aggregate(
                    fields
                        .iter()
                        .map(|(index, value)| (vec![*index], self.operand(value, state)))
                        .collect(),
                    active,
                )
            }
            Rvalue::Repeat { value, .. } | Rvalue::RepeatConst { value, .. } => Value::aggregate(
                std::collections::BTreeMap::from([(vec![0], self.operand(value, state))]),
                None,
            ),
            Rvalue::Length(place) => Value {
                integer: match self.context.hir.types.get(self.place_type(place)) {
                    Ty::Array { length, .. } => Some(*length),
                    _ => None,
                },
                ..Value::default()
            },
            _ => Value::default(),
        }
    }

    fn borrow_value(&self, place: &Place, mutable: bool, span: Span, state: &State) -> Value {
        let mut pointer = self.address(place, state).unwrap_or(Pointer {
            raw: false,
            owned: Truth::No,
            ancestors: BTreeSet::new(),
            allocation: AllocationId::Local(place.local.0),
            offset: self.place_offset(place),
            readable: Truth::Yes,
            writable: Truth::Yes,
            unaligned: false,
            expired: false,
            basis: self.basis(span),
        });
        if pointer.basis.event != self.basis(span).event {
            pointer.ancestors.insert(pointer.basis.event);
        }
        pointer.raw = false;
        pointer.owned = Truth::No;
        pointer.basis = self.basis(span);
        if let Some(allocation) = state.allocations.get(&pointer.allocation) {
            pointer
                .basis
                .trust
                .extend(allocation.basis.trust.iter().cloned());
        }
        if !mutable {
            pointer.writable = Truth::No;
        }
        Value {
            trust: pointer.basis.trust.clone(),
            pointer: Some(pointer),
            ..Value::default()
        }
    }

    pub(super) fn store(&self, place: &Place, value: Value, span: Span, state: &mut State) {
        if place.projection.first() == Some(&Projection::Deref)
            && self.context.body.local(place.local).kind == LocalKind::Address
        {
            let captured = state.places[place.local.0 as usize].clone();
            if let Some(captured) = captured {
                self.store_capture(&captured, value, state);
            } else {
                self.invalidate_unknown(state);
            }
            return;
        }
        if place.projection.is_empty() {
            let (slot, allocation) = state.local_storage(place.local);
            *slot = value;
            if let Some(allocation) = allocation {
                allocation.initialized = Truth::Yes;
                allocation.initialized_type = Some(self.place_type(place));
                allocation.uninitialized_ranges.clear();
                allocation.active_union = slot.active_union;
                allocation.basis.trust.extend(slot.trust.iter().cloned());
            }
        } else if !place.projection.contains(&Projection::Deref) {
            self.store_projected(place, value, state);
        } else if let Some(pointer) = self.address(place, state) {
            if let Some(allocation) = state.allocations.get_mut(&pointer.allocation)
                && let (Some(0), Some(size)) = (pointer.offset, self.size(self.place_type(place)))
                && allocation.extent == Some(size.bytes)
            {
                allocation.initialized = Truth::Yes;
                allocation.initialized_type = Some(self.place_type(place));
            }
            if let AllocationId::Local(local) = pointer.allocation {
                state.values[local as usize] = value;
            } else if let Some(offset) = pointer.offset {
                state.contents.insert((pointer.allocation, offset), value);
            }
            state.assumptions.retain(|fact| {
                fact.value
                    .pointer
                    .as_ref()
                    .is_none_or(|p| p.allocation != pointer.allocation)
            });
        }
        let _ = span;
    }

    fn store_projected(&self, place: &Place, value: Value, state: &mut State) {
        let mut steps = Vec::new();
        for (index, projection) in place.projection.iter().enumerate() {
            let field = match projection {
                Projection::Field(field) => Some(*field),
                Projection::Index(local) => state
                    .local(*local)
                    .integer
                    .and_then(|index| index.try_into().ok()),
                Projection::Downcast(_) => continue,
                Projection::Deref => unreachable!("direct aggregate projection"),
            };
            let Some(field) = field else {
                state.local_mut(place.local).havoc();
                return;
            };
            let parent = Place {
                local: place.local,
                projection: place.projection[..index].to_vec(),
            };
            steps.push(if self.context.properties.union(self.place_type(&parent)) {
                FieldStep::UnionField(field)
            } else {
                FieldStep::Field(field)
            });
        }
        let (root, allocation) = state.local_storage(place.local);
        update_fields(root, &steps, value);
        if let Some(allocation) = allocation {
            // A partial assignment can enable drop glue even when the whole
            // allocation has never held a complete initialized value.
            if allocation.initialized == Truth::No {
                allocation.initialized = Truth::Unknown;
            }
            allocation.active_union = root.active_union;
            allocation.basis.trust.extend(root.trust.iter().cloned());
        }
    }

    fn capture_place(&self, place: &Place, state: &State) -> Option<CapturedPlace> {
        let mut captured = CapturedPlace::Local {
            local: place.local,
            steps: Vec::new(),
        };
        for (index, projection) in place.projection.iter().enumerate() {
            let prefix = Place {
                local: place.local,
                projection: place.projection[..index].to_vec(),
            };
            if *projection == Projection::Deref {
                captured = if index == 0
                    && self.context.body.local(place.local).kind == LocalKind::Address
                {
                    state.places[place.local.0 as usize].clone()?
                } else {
                    CapturedPlace::Indirect {
                        pointer: state.read(&prefix).pointer?,
                        steps: Vec::new(),
                    }
                };
                continue;
            }
            let field = match projection {
                Projection::Field(field) => *field,
                Projection::Index(local) => state.local(*local).integer?.try_into().ok()?,
                Projection::Downcast(_) => continue,
                Projection::Deref => unreachable!(),
            };
            let step = if self.context.properties.union(self.place_type(&prefix)) {
                FieldStep::UnionField(field)
            } else {
                FieldStep::Field(field)
            };
            match &mut captured {
                CapturedPlace::Local { steps, .. } | CapturedPlace::Indirect { steps, .. } => {
                    steps.push(step)
                }
            }
        }
        Some(captured)
    }

    fn store_capture(&self, capture: &CapturedPlace, value: Value, state: &mut State) {
        match capture {
            CapturedPlace::Local { local, steps } => {
                let (root, allocation) = state.local_storage(*local);
                update_fields(root, steps, value);
                if let Some(allocation) = allocation {
                    if allocation.initialized == Truth::No {
                        allocation.initialized = Truth::Unknown;
                    }
                    allocation.active_union = root.active_union;
                    allocation.basis.trust.extend(root.trust.iter().cloned());
                }
            }
            CapturedPlace::Indirect { pointer, steps } => {
                let Some(offset) = pointer.offset else {
                    self.invalidate_unknown(state);
                    return;
                };
                let target = match pointer.allocation {
                    AllocationId::Local(local) if offset == 0 => &mut state.values[local as usize],
                    _ => state
                        .contents
                        .entry((pointer.allocation, offset))
                        .or_default(),
                };
                update_fields(target, steps, value);
                state.memory_write();
            }
        }
    }

    pub(super) fn address(&self, place: &Place, state: &State) -> Option<Pointer> {
        if place.projection.first() == Some(&Projection::Deref)
            && self.context.body.local(place.local).kind == LocalKind::Address
        {
            return match state.places[place.local.0 as usize].as_ref()? {
                CapturedPlace::Local { .. } => None,
                CapturedPlace::Indirect { pointer, steps } => {
                    let mut pointer = pointer.clone();
                    if !steps.is_empty() || place.projection.len() > 1 {
                        pointer.offset = None;
                    }
                    Some(pointer)
                }
            };
        }
        let index = place
            .projection
            .iter()
            .position(|p| *p == Projection::Deref)?;
        let base = Place {
            local: place.local,
            projection: place.projection[..index].to_vec(),
        };
        let mut pointer = state.read(&base).pointer?;
        if index + 1 != place.projection.len() {
            pointer.offset = None;
        }
        Some(pointer)
    }

    fn place_offset(&self, place: &Place) -> Option<u64> {
        place.projection.is_empty().then_some(0)
    }

    fn contract(&self, contract: &crate::contracts::Statement, span: Span, state: &mut State) {
        if !matches!(
            contract.action,
            Action::Precondition | Action::Assume { .. }
        ) {
            return;
        }
        let Some(argument) = contract.atom.arguments.first() else {
            return;
        };
        let value = self.operand(argument, state);
        let count = contract
            .atom
            .arguments
            .get(1)
            .and_then(|value| self.operand(value, state).integer);
        let ty = match self.context.hir.types.get(self.operand_type(argument)) {
            Ty::Pointer { inner, .. } | Ty::Reference { inner, .. } => *inner,
            _ => TyId::VOID,
        };
        let mut basis = self.basis(span);
        if let Action::Assume { reason } = &contract.action {
            basis.trust.insert(Trust::Source {
                file: span.file.0,
                start: span.start,
                reason: reason.clone(),
            });
        }
        let Some(&scope) = state.scopes.last() else {
            return;
        };
        let fact = Fact {
            permissions: Freshness::Current,
            contents: Freshness::Current,
            scope,
            predicate: contract.atom.predicate,
            value,
            count,
            ty,
            basis,
            operands: contract
                .atom
                .arguments
                .iter()
                .map(|argument| self.operand(argument, state))
                .collect(),
        };
        if state.assumptions.len() < 1024 && !state.assumptions.contains(&fact) {
            state.assumptions.push(fact);
        }
    }
}

fn scalar(value: &hir::Constant) -> Value {
    match value {
        hir::Constant::Integer {
            magnitude,
            negative: false,
        } => Value {
            integer: (*magnitude).try_into().ok(),
            ..Value::default()
        },
        hir::Constant::Bool(value) => Value {
            boolean: Some(*value),
            ..Value::default()
        },
        _ => Value::default(),
    }
}

fn binary(op: crate::syntax::ast::BinaryOp, left: Value, right: Value) -> Value {
    use crate::syntax::ast::BinaryOp as B;
    let mut value = Value::default();
    value.trust.extend(left.trust.iter().cloned());
    value.trust.extend(right.trust.iter().cloned());
    if let (Some(left), Some(right)) = (left.integer, right.integer) {
        value.integer = match op {
            B::Add => left.checked_add(right),
            B::Subtract => left.checked_sub(right),
            B::Multiply => left.checked_mul(right),
            B::Divide => left.checked_div(right),
            B::Remainder => left.checked_rem(right),
            B::BitAnd => Some(left & right),
            B::BitOr => Some(left | right),
            B::BitXor => Some(left ^ right),
            B::ShiftLeft => u32::try_from(right)
                .ok()
                .and_then(|right| left.checked_shl(right)),
            B::ShiftRight => u32::try_from(right)
                .ok()
                .and_then(|right| left.checked_shr(right)),
            _ => None,
        };
        value.boolean = match op {
            B::Equal => Some(left == right),
            B::NotEqual => Some(left != right),
            B::Less => Some(left < right),
            B::LessEqual => Some(left <= right),
            B::Greater => Some(left > right),
            B::GreaterEqual => Some(left >= right),
            _ => None,
        };
    }
    if let (Some(left), Some(right)) = (left.boolean, right.boolean) {
        value.boolean = match op {
            B::And => Some(left && right),
            B::Or => Some(left || right),
            B::Equal => Some(left == right),
            B::NotEqual => Some(left != right),
            _ => None,
        };
    }
    value
}

fn unary(op: crate::syntax::ast::UnaryOp, value: Value) -> Value {
    use crate::syntax::ast::UnaryOp as U;
    match op {
        U::Positive => value,
        U::Not => Value {
            boolean: value.boolean.map(|v| !v),
            trust: value.trust,
            ..Value::default()
        },
        _ => Value {
            trust: value.trust,
            ..Value::default()
        },
    }
}

fn update_fields(target: &mut Value, steps: &[FieldStep], value: Value) {
    let Some((step, rest)) = steps.split_first() else {
        *target = value;
        return;
    };
    let (FieldStep::Field(field) | FieldStep::UnionField(field)) = step;
    if matches!(step, FieldStep::UnionField(_)) {
        target.fields.clear();
        target.active_union = Some(*field);
    }
    target.trust.extend(value.trust.iter().cloned());
    update_fields(target.fields.entry(vec![*field]).or_default(), rest, value);
}
