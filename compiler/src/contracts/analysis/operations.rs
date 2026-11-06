use super::*;

impl Engine<'_> {
    pub(super) fn edges(&self, exit: &Terminator, mut state: State) -> Vec<(BlockId, State)> {
        match exit {
            Terminator::Spawn { .. } => self.spawn_edges(exit, state),
            Terminator::Call { .. } | Terminator::DynCall { .. } => self.call_edges(exit, state),
            Terminator::TaskDrain {
                registry,
                next,
                abort,
                ..
            } => {
                state.values[registry.0 as usize] = Value::default();
                self.invalidate_unknown(&mut state);
                vec![(*next, state.clone()), (*abort, state)]
            }
            Terminator::Checked {
                value,
                destination,
                normal,
                trap,
            } => {
                let failure = state.clone();
                let span = self.context.body.blocks[self.block].span;
                let value = self.evaluate_value(value, span, &state);
                self.store(destination, value, span, &mut state);
                vec![(*normal, state), (*trap, failure)]
            }
            Terminator::Switch { condition, yes, no } => {
                match self.operand(condition, &state).boolean {
                    Some(value) => vec![(if value { *yes } else { *no }, state)],
                    None => vec![(*yes, state.clone()), (*no, state)],
                }
            }
            Terminator::Drop {
                place,
                next,
                unwind,
            } => {
                // User Drop runs before storage dies. Its unknown heap effects
                // must not leave a pre-drop allocation/initialization witness.
                let uninitialized = place.projection.is_empty()
                    && state
                        .allocations
                        .get(&AllocationId::Local(place.local.0))
                        .is_some_and(|allocation| {
                            allocation.initialized == Truth::No
                                && allocation.initialized_ranges.is_empty()
                        });
                // MIR Drop is conditional. A definitely uninitialized local
                // cannot execute user code; all other cases retain havoc.
                if !uninitialized && self.context.properties.get(self.place_type(place)).may_drop {
                    self.invalidate_unknown(&mut state);
                }
                let id = self
                    .address(place, &state)
                    .map_or(AllocationId::Local(place.local.0), |p| p.allocation);
                if let Some(allocation) = state.allocations.get_mut(&id) {
                    allocation.initialized = Truth::No;
                }
                vec![(*next, state.clone()), (*unwind, state)]
            }
            _ => crate::mir::borrow::successors(exit)
                .into_iter()
                .map(|next| (next, state.clone()))
                .collect(),
        }
    }

    fn spawn_edges(&self, exit: &Terminator, mut state: State) -> Vec<(BlockId, State)> {
        let Terminator::Spawn {
            destination,
            registry,
            normal,
            panic,
            cancel,
            arguments,
            ..
        } = exit
        else {
            unreachable!("spawn transfer");
        };
        let captured = Value {
            fields: arguments
                .iter()
                .enumerate()
                .map(|(index, arg)| (vec![index as u32], self.operand(arg, &state)))
                .collect(),
            ..Value::default()
        };
        let mut lease = captured.clone();
        retain_child(
            &mut lease,
            self.basis(self.context.body.blocks[self.block].span),
        );
        state.values[registry.0 as usize]
            .fields
            .insert(vec![self.block as u32], lease);
        let failure = state.clone();
        self.store(
            destination,
            captured,
            self.context.body.blocks[self.block].span,
            &mut state,
        );
        self.invalidate_unknown(&mut state);
        vec![
            (*normal, state),
            (*panic, failure.clone()),
            (*cancel, failure),
        ]
    }

    fn call_edges(&self, exit: &Terminator, mut state: State) -> Vec<(BlockId, State)> {
        let dependency = match exit {
            Terminator::Call { callee, .. } => self.operand(callee, &state).function,
            Terminator::DynCall { trait_method, .. } => Some(*trait_method),
            _ => None,
        };
        let (destination, normal, panic, cancel) = match exit {
            Terminator::Call {
                callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => {
                let definition = self.operand(callee, &state).function;
                if let Some(role) = definition
                    .and_then(|d| self.context.hir.contracts.intrinsics.get(&d))
                    .copied()
                {
                    self.intrinsic(role, arguments, destination, &mut state);
                    return vec![(*normal, state)];
                }
                (destination, normal, panic, cancel)
            }
            Terminator::DynCall {
                destination,
                normal,
                panic,
                cancel,
                ..
            } => (destination, normal, panic, cancel),
            _ => unreachable!("call transfer"),
        };
        self.ordinary_call(
            exit,
            dependency,
            destination,
            [*normal, *panic, *cancel],
            state,
        )
    }

    fn ordinary_call(
        &self,
        exit: &Terminator,
        dependency: Option<hir::DefId>,
        destination: &Place,
        exits: [BlockId; 3],
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let mut argument_trust = BTreeSet::new();
        if let Terminator::Call { arguments, .. } | Terminator::DynCall { arguments, .. } = exit {
            for argument in arguments {
                argument_trust.extend(self.operand(argument, &state).trust);
            }
        }
        if let Terminator::DynCall { receiver, .. } = exit {
            argument_trust.extend(self.operand(receiver, &state).trust);
        }
        if !dependency.is_some_and(|definition| {
            crate::contracts::purity::eligible(self.context.hir, definition)
        }) {
            self.invalidate_unknown(&mut state);
        }
        let failure = state.clone();
        let mut result = Value {
            opaque_references: self
                .context
                .properties
                .get(self.place_type(destination))
                .references,
            trust: dependency
                .and_then(|definition| self.context.dependencies.get(&definition))
                .cloned()
                .unwrap_or_default(),
            ..Value::default()
        };
        result.trust.extend(argument_trust);
        if result.opaque_references {
            state.new_reference();
        }
        self.store(
            destination,
            result,
            self.context.body.blocks[self.block].span,
            &mut state,
        );
        vec![
            (exits[0], state),
            (exits[1], failure.clone()),
            (exits[2], failure),
        ]
    }

    pub(super) fn invalidate_unknown(&self, state: &mut State) {
        for allocation in state.allocations.values_mut() {
            if allocation.live != Truth::No {
                allocation.live = Truth::Unknown;
                allocation.initialized = Truth::Unknown;
                allocation.invalidation = None;
                allocation.active_union = None;
            }
            allocation.owned = allocation.owned.join(Truth::Unknown);
            allocation.initialized_ranges.clear();
            allocation.uninitialized_ranges.clear();
        }
        for value in &mut state.values {
            value.havoc();
        }
        state.assumptions.clear();
        state.contents.clear();
    }

    fn intrinsic(
        &self,
        role: Intrinsic,
        arguments: &[Operand],
        destination: &Place,
        state: &mut State,
    ) {
        let span = self.context.body.blocks[self.block].span;
        let values: Vec<_> = arguments
            .iter()
            .map(|value| self.operand(value, state))
            .collect();
        let first = values.first().cloned().unwrap_or_default();
        let mut result = self.intrinsic_value(role, arguments, &values, destination, state);
        if let Some(pointer) = &first.pointer {
            for fact in &state.assumptions {
                if fact
                    .value
                    .pointer
                    .as_ref()
                    .is_some_and(|p| p.allocation == pointer.allocation)
                {
                    result.trust.extend(fact.basis.trust.iter().cloned());
                }
            }
        }
        let result_type = self.place_type(destination);
        if self.context.properties.get(result_type).references
            && result.pointer.is_none()
            && result.fields.is_empty()
        {
            result.opaque_references = true;
        }
        if self.context.properties.get(result_type).references {
            state.new_reference();
        }
        self.store(destination, result, span, state);
    }

    fn intrinsic_value(
        &self,
        role: Intrinsic,
        arguments: &[Operand],
        values: &[Value],
        destination: &Place,
        state: &mut State,
    ) -> Value {
        let first = values.first().cloned().unwrap_or_default();
        match role {
            Intrinsic::TaskJoin => {
                self.invalidate_unknown(state);
                Value::default()
            }
            Intrinsic::TaskIgnore | Intrinsic::TaskCancel => Value::default(),
            Intrinsic::AsPtr | Intrinsic::AsMutPtr => {
                let mut value = first;
                if let Some(pointer) = &mut value.pointer {
                    pointer.raw = true;
                }
                value
            }
            Intrinsic::Allocate => {
                self.allocate(self.place_type(destination), first.integer, state)
            }
            Intrinsic::Deallocate => {
                if let Some(pointer) = first.pointer {
                    self.deallocate(&pointer, state);
                }
                Value::default()
            }
            Intrinsic::Initialize | Intrinsic::Replace | Intrinsic::WriteUnaligned => {
                if let Some(pointer) = first.pointer {
                    self.initialize_range(
                        &pointer,
                        self.operand_type(&arguments[1]),
                        values[1].clone(),
                        state,
                    );
                }
                Value::default()
            }
            Intrinsic::Take => first.pointer.map_or_else(Value::default, |pointer| {
                self.take(&pointer, self.place_type(destination), state)
            }),
            Intrinsic::Offset => self.offset(
                first,
                values.get(1).and_then(|v| v.integer),
                self.operand_type(&arguments[0]),
            ),
            Intrinsic::Length => Value {
                integer: self.length(self.operand_type(&arguments[0])),
                ..Value::default()
            },
            Intrinsic::Read | Intrinsic::ReadUnaligned => first
                .pointer
                .map_or_else(Value::default, |pointer| read_pointer(&pointer, state)),
        }
    }

    fn allocate(&self, ty: TyId, count: Option<u64>, state: &mut State) -> Value {
        let span = self.context.body.blocks[self.block].span;
        let id =
            AllocationId::Heap((self.context.events[self.block] + self.statement as u64) as u32);
        let inner = match self.context.hir.types.get(ty) {
            Ty::Pointer { inner, .. } => *inner,
            _ => TyId::ERROR,
        };
        let size = self.size(inner);
        state.expire(id, self.basis(span));
        state.allocations.insert(
            id,
            Allocation {
                initialized_type: None,
                raw_touched: false,
                live: Truth::Yes,
                initialized: Truth::No,
                initialized_ranges: BTreeSet::new(),
                uninitialized_ranges: BTreeSet::new(),
                extent: size.and_then(|size| count.and_then(|count| count.checked_mul(size.bytes))),
                alignment: size.map_or(0, |size| size.alignment),
                owned: Truth::Yes,
                basis: self.basis(span),
                invalidation: None,
                active_union: None,
            },
        );
        Value {
            pointer: Some(Pointer {
                owned: Truth::Yes,
                ancestors: BTreeSet::new(),
                allocation: id,
                offset: Some(0),
                readable: Truth::Yes,
                raw: true,
                writable: Truth::Yes,
                unaligned: false,
                expired: false,
                basis: self.basis(span),
            }),
            ..Value::default()
        }
    }

    fn deallocate(&self, pointer: &Pointer, state: &mut State) {
        let mut basis = self.basis(self.context.body.blocks[self.block].span);
        for fact in &state.assumptions {
            if fact
                .value
                .pointer
                .as_ref()
                .is_some_and(|p| p.allocation == pointer.allocation)
            {
                basis.trust.extend(fact.basis.trust.iter().cloned());
            }
        }
        state.memory_free();
        state.expire(pointer.allocation, basis);
    }

    fn take(&self, pointer: &Pointer, ty: TyId, state: &mut State) -> Value {
        let Some(offset) = pointer.offset else {
            return Value::default();
        };
        state.memory_write();
        let value = read_pointer(pointer, state);
        if let AllocationId::Local(local) = pointer.allocation {
            state.values[local as usize] = Value::default();
        } else {
            state.contents.remove(&(pointer.allocation, offset));
        }
        let size = self.size(ty);
        if let Some(allocation) = state.allocations.get_mut(&pointer.allocation) {
            allocation.initialized = if offset == 0 && size.is_none() {
                Truth::No
            } else {
                Truth::Unknown
            };
            allocation.raw_touched = true;
            if let Some(size) = size {
                allocation.initialized_ranges.retain(|&(start, bytes, _)| {
                    start.saturating_add(bytes) <= offset
                        || start >= offset.saturating_add(size.bytes)
                });
                allocation.uninitialized_ranges.insert((offset, size.bytes));
            } else {
                allocation.initialized_ranges.clear();
            }
        }
        value
    }

    fn offset(&self, mut value: Value, count: Option<u64>, ty: TyId) -> Value {
        let inner = match self.context.hir.types.get(ty) {
            Ty::Pointer { inner, .. } => *inner,
            _ => TyId::ERROR,
        };
        let bytes = self
            .size(inner)
            .and_then(|size| count.and_then(|count| count.checked_mul(size.bytes)));
        if let Some(pointer) = &mut value.pointer {
            pointer.offset = pointer
                .offset
                .zip(bytes)
                .and_then(|(offset, bytes)| offset.checked_add(bytes));
        }
        value
    }

    fn length(&self, ty: TyId) -> Option<u64> {
        let Ty::Reference { inner, .. } = self.context.hir.types.get(ty) else {
            return None;
        };
        match self.context.hir.types.get(*inner) {
            Ty::Array { length, .. } => Some(*length),
            _ => None,
        }
    }

    fn initialize_range(&self, pointer: &Pointer, ty: TyId, value: Value, state: &mut State) {
        state.memory_write();
        let Some(offset) = pointer.offset else {
            return;
        };
        let Some(size) = self.size(ty) else {
            if let Some(allocation) = state.allocations.get_mut(&pointer.allocation) {
                allocation.initialized = if offset == 0 {
                    Truth::Yes
                } else {
                    Truth::Unknown
                };
                allocation.initialized_type = Some(ty);
                allocation.raw_touched = true;
                allocation.active_union = value.active_union;
                allocation.basis.trust.extend(value.trust.iter().cloned());
            }
            state.contents.insert((pointer.allocation, offset), value);
            return;
        };
        if let Some(allocation) = state.allocations.get_mut(&pointer.allocation) {
            if offset == 0 && allocation.extent == Some(size.bytes) {
                allocation.initialized = Truth::Yes;
                allocation.initialized_type = Some(ty);
                allocation.active_union = value.active_union;
            }
            allocation.raw_touched = true;
            allocation.basis.trust.extend(value.trust.iter().cloned());
            if allocation.initialized_ranges.len() < 256 {
                allocation
                    .initialized_ranges
                    .insert((offset, size.bytes, ty.0));
                allocation.uninitialized_ranges.retain(|&(start, bytes)| {
                    start.saturating_add(bytes) <= offset
                        || start >= offset.saturating_add(size.bytes)
                });
            }
        }
        if let AllocationId::Local(local) = pointer.allocation {
            if offset == 0 {
                state.values[local as usize] = value;
            }
        } else {
            state.contents.insert((pointer.allocation, offset), value);
        }
    }
}

fn read_pointer(pointer: &Pointer, state: &State) -> Value {
    match pointer.allocation {
        AllocationId::Local(local) if pointer.offset == Some(0) => {
            state.values[local as usize].clone()
        }
        _ => pointer
            .offset
            .and_then(|offset| state.contents.get(&(pointer.allocation, offset)))
            .cloned()
            .unwrap_or_default(),
    }
}

fn retain_child(value: &mut Value, basis: Basis) {
    if let Some(pointer) = &mut value.pointer {
        pointer.raw = false;
        pointer.ancestors.insert(pointer.basis.event);
        pointer.basis = basis.clone();
    }
    for field in value.fields.values_mut() {
        retain_child(field, basis.clone());
    }
}
