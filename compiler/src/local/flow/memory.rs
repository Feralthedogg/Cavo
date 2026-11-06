use super::*;
use crate::local::memory::{MemoryLoan, MemoryOrigin, MemoryPlace, MemoryValue, MemoryWrite};
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
pub(super) struct Invocation {
    pub event: EventId,
    pub target: hir::DefId,
    pub span: Span,
}

pub(super) fn join_value(left: &mut Value, right: &Value) -> bool {
    let before = (
        left.valid,
        left.origins.len(),
        left.causes.len(),
        left.functions.len(),
        left.fields.is_some(),
    );
    let mut changed = false;
    let fields = match (&mut left.fields, &right.fields) {
        (Some(a), Some(b)) if a.len() == b.len() => {
            for (a, b) in a.iter_mut().zip(b) {
                changed |= join_value(a, b);
            }
            true
        }
        _ => false,
    };
    left.valid &= right.valid;
    left.origins.extend(right.origins.iter().cloned());
    left.causes.extend(&right.causes);
    left.functions.extend(&right.functions);
    if !fields {
        left.fields = None;
    }
    changed
        || before
            != (
                left.valid,
                left.origins.len(),
                left.causes.len(),
                left.functions.len(),
                left.fields.is_some(),
            )
}

pub(super) fn capture(
    exit: Option<&(State, Value)>,
    places: &Places,
    inputs: &[Option<usize>],
    loans: &LoanSets,
) -> Option<MemorySummary> {
    let Some((state, returned)) = exit else {
        return Some(MemorySummary::default());
    };
    let changed: Vec<_> = state
        .slots
        .iter()
        .enumerate()
        .filter(|(i, s)| s.written.may_write() && places.input_source(places.leaf(*i)).is_some())
        .collect();
    if changed.len() > 1024 || !returned.valid {
        return None;
    }
    let mut roots = BTreeSet::new();
    for origin in returned
        .origins
        .iter()
        .chain(changed.iter().flat_map(|(_, s)| s.origins.iter()))
    {
        if let Origin::Borrow { loan, .. } = origin
            && !matches!(loan, LoanId::Input(_))
        {
            roots.insert(*loan);
        }
    }
    if roots.len() > 128 {
        return None;
    }
    let fresh: BTreeMap<_, _> = roots
        .into_iter()
        .enumerate()
        .map(|(i, l)| (l, i as u32))
        .collect();
    struct Capture<'a> {
        places: &'a Places,
        inputs: &'a [Option<usize>],
        fresh: BTreeMap<LoanId, u32>,
        remaining: usize,
    }
    impl Capture<'_> {
        fn loan(&self, loan: LoanId) -> Option<MemoryLoan> {
            match loan {
                LoanId::Input(p) => Some(MemoryLoan::Input(self.inputs[p.0 as usize]?)),
                loan => Some(MemoryLoan::Fresh(*self.fresh.get(&loan)?)),
            }
        }
        fn place(&self, place: PlaceId) -> Option<MemoryPlace> {
            let (source, fields) = self.places.memory_path(place)?;
            Some(MemoryPlace {
                input: self.inputs[source.0 as usize]?,
                fields,
            })
        }
        fn value(&mut self, value: &Value) -> Option<MemoryValue> {
            self.remaining = self
                .remaining
                .checked_sub(1 + value.origins.len() + value.functions.len())?;
            if !value.valid || value.origins.len() > 64 {
                return None;
            }
            let mut origins = Vec::new();
            for origin in &value.origins {
                origins.push(match *origin {
                    Origin::Borrow {
                        place,
                        precise,
                        mutable,
                        loan,
                        ..
                    } => MemoryOrigin::Reference {
                        place: self.place(place)?,
                        precise,
                        mutable,
                        loan: self.loan(loan)?,
                    },
                    Origin::OpaqueInput(p) => MemoryOrigin::Opaque(self.inputs[p as usize]?),
                    Origin::Static => MemoryOrigin::Static,
                });
            }
            origins.sort();
            origins.dedup();
            let fields = match &value.fields {
                Some(fields) => Some(
                    fields
                        .iter()
                        .map(|v| self.value(v))
                        .collect::<Option<Vec<_>>>()?,
                ),
                None => None,
            };
            Some(MemoryValue {
                origins,
                fields,
                functions: value.functions.iter().copied().collect(),
            })
        }
    }
    let mut capture = Capture {
        places,
        inputs,
        fresh,
        remaining: 4096,
    };
    let mut summary = MemorySummary {
        normal_return: true,
        writes: Vec::new(),
        returned: MemoryValue::default(),
        loans: vec![Vec::new(); capture.fresh.len()],
    };
    // Ancestry is flat/transitive in the local solver. Retain entry loans and
    // other exported loans; internal dead parents cannot constrain a caller.
    for origin in returned
        .origins
        .iter()
        .chain(changed.iter().flat_map(|(_, s)| s.origins.iter()))
    {
        if let Origin::Borrow { loan, parents, .. } = origin
            && let Some(&index) = capture.fresh.get(loan)
        {
            for &parent in &loans.values[parents.0 as usize] {
                if parent != *loan
                    && let Some(parent) = capture.loan(parent)
                {
                    summary.loans[index as usize].push(parent);
                }
            }
        }
    }
    for parents in &mut summary.loans {
        parents.sort();
        parents.dedup();
    }
    for (index, slot) in changed {
        let value = Value {
            valid: slot.flags == AVAILABLE,
            origins: slot.origins.clone(),
            causes: slot.causes.clone(),
            fields: None,
            functions: slot.functions.clone(),
        };
        summary.writes.push(MemoryWrite {
            target: capture.place(places.leaf(index))?,
            value: capture.value(&value)?,
            definite: slot.written.definite(),
        });
    }
    summary.writes.sort_by(|a, b| a.target.cmp(&b.target));
    summary.returned = capture.value(returned)?;
    Some(summary)
}

impl<R: Reporter> Evaluator<'_, R> {
    pub(super) fn contains_callable(&mut self, ty: crate::types::TyId) -> bool {
        let mut pending = vec![ty];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > 4096 || self.budget == 0 {
                self.exhausted = true;
                return true;
            }
            self.budget -= 1;
            self.visits += 1;
            match self.program.types.get(ty) {
                Ty::Function { .. } | Ty::ForAll { .. } => return true,
                Ty::Reference { inner, .. } | Ty::Array { inner, .. } | Ty::Slice(inner) => {
                    pending.push(*inner)
                }
                _ => {
                    if let Some(fields) = self.properties.fields(ty) {
                        pending.extend(fields);
                    }
                }
            }
        }
        false
    }

    pub(super) fn scalar_callback_effects(&mut self, contract: &RegionContract) -> MemorySummary {
        let mut summary = MemorySummary {
            normal_return: true,
            ..MemorySummary::default()
        };
        for (input, reference) in contract.inputs.iter().enumerate() {
            if reference.mutable == Some(true)
                && reference.pointee.is_some_and(|ty| {
                    !self.properties.get(ty).references && !self.contains_callable(ty)
                })
            {
                summary.writes.push(MemoryWrite {
                    target: MemoryPlace {
                        input,
                        fields: Vec::new(),
                    },
                    value: MemoryValue::default(),
                    definite: false,
                });
            }
        }
        summary
    }
    pub(super) fn callable_reference(
        &mut self,
        contract: &RegionContract,
        arguments: &[Value],
        invocation: Invocation,
        state: &mut State,
        result: crate::types::TyId,
    ) -> Value {
        let mut summary = self.scalar_callback_effects(contract);
        let mutable = matches!(
            self.program.types.get(result),
            Ty::Reference { mutable: true, .. }
        );
        for &input in &contract.return_inputs {
            let source = &contract.inputs[input];
            let precise = source
                .pointee
                .zip(contract.result_pointee)
                .is_some_and(|(a, b)| self.program.types.compatible(a, b));
            let loan = if source.mutable == Some(true) {
                let index = summary.loans.len() as u32;
                summary.loans.push(vec![MemoryLoan::Input(input)]);
                MemoryLoan::Fresh(index)
            } else {
                MemoryLoan::Input(input)
            };
            summary.returned.origins.push(MemoryOrigin::Reference {
                place: MemoryPlace {
                    input,
                    fields: Vec::new(),
                },
                precise,
                mutable,
                loan,
            });
        }
        if contract.static_result && contract.return_inputs.is_empty() {
            summary.returned.origins.push(MemoryOrigin::Static);
        }
        self.apply_memory(&summary, contract, arguments, invocation, state)
    }

    pub(super) fn input_store(&mut self, place: PlaceId, value: &Value, span: Span) -> bool {
        if self.places.input_source(place).is_none() {
            return true;
        }
        let ty = self.places.ty(place);
        if self.properties.get(ty).may_drop {
            self.unsupported(
                "replacing input memory whose old value may require Drop",
                span,
            );
            return false;
        }
        if let Ty::Reference { .. } = self.program.types.get(ty) {
            let Some(index) = self.input_positions[place.0 as usize] else {
                self.unsupported("the lifetime of a written input reference cell", span);
                return false;
            };
            let contract = self.contracts[self.function.definition.0 as usize]
                .as_ref()
                .unwrap();
            let required = contract.inputs[index].term;
            let valid = value.valid
                && !value.origins.is_empty()
                && value.origins.iter().all(|o| {
                    self.origin_region(o)
                        .is_some_and(|r| contract.outlives(r, required))
                });
            if !valid && value.valid {
                self.reporter.problem(Problem::InputStore(span));
            }
            return valid;
        }
        if let Some(fields) = self.properties.fields(ty) {
            let mut valid = true;
            for index in 0..fields.len() {
                let Some(child) = self.places.projected(place, &[index as u32]) else {
                    return false;
                };
                let data = value
                    .fields
                    .as_ref()
                    .and_then(|v| v.get(index))
                    .unwrap_or(value);
                valid &= self.input_store(child, data, span);
            }
            return valid;
        }
        true
    }

    fn input_values(
        &mut self,
        summary: &MemorySummary,
        contract: &RegionContract,
        arguments: &[Value],
        state: &State,
        span: Span,
    ) -> Option<Vec<(Value, bool)>> {
        let mut needed = BTreeSet::new();
        let mut pending = vec![&summary.returned];
        for write in &summary.writes {
            needed.insert(write.target.input);
            pending.push(&write.value);
        }
        for parents in &summary.loans {
            for parent in parents {
                if let MemoryLoan::Input(input) = parent {
                    needed.insert(*input);
                }
            }
        }
        while let Some(value) = pending.pop() {
            for origin in &value.origins {
                match origin {
                    MemoryOrigin::Reference { place, loan, .. } => {
                        needed.insert(place.input);
                        if let MemoryLoan::Input(input) = loan {
                            needed.insert(*input);
                        }
                    }
                    MemoryOrigin::Opaque(input) => {
                        needed.insert(*input);
                    }
                    MemoryOrigin::Static => {}
                }
            }
            if let Some(fields) = &value.fields {
                pending.extend(fields);
            }
        }
        contract
            .inputs
            .iter()
            .enumerate()
            .map(|(index, input)| {
                if !needed.contains(&index) {
                    return Some((Value::scalar(), false));
                }
                let value = arguments.get(input.parameter as usize)?;
                let (value, exact) = self.argument_path(value, &input.path, state, span);
                value.valid.then_some((value, exact))
            })
            .collect()
    }

    fn call_parents(
        &mut self,
        summary: &MemorySummary,
        entries: &[(Value, bool)],
        event: EventId,
        target: hir::DefId,
        span: Span,
    ) -> Option<Vec<LoanSetId>> {
        let mut sets: Vec<Option<LoanSetId>> = vec![None; summary.loans.len()];
        for _ in 0..=summary.loans.len() {
            let mut progress = false;
            for (index, parents) in summary.loans.iter().enumerate() {
                if sets[index].is_some() {
                    continue;
                }
                let mut values = BTreeSet::new();
                let mut ready = true;
                for parent in parents {
                    match *parent {
                        MemoryLoan::Input(input) => {
                            for origin in &entries.get(input)?.0.origins {
                                if let Origin::Borrow { loan, parents, .. } = origin {
                                    values.insert(*loan);
                                    values.extend(&self.loans.values[parents.0 as usize]);
                                }
                            }
                        }
                        MemoryLoan::Fresh(input) => {
                            let Some(set) = sets.get(input as usize).copied().flatten() else {
                                ready = false;
                                break;
                            };
                            values.insert(LoanId::Call {
                                event,
                                target,
                                index: input,
                            });
                            values.extend(&self.loans.values[set.0 as usize]);
                        }
                    }
                }
                if ready {
                    if values.contains(&LoanId::Call {
                        event,
                        target,
                        index: index as u32,
                    }) {
                        self.unsupported("a cyclic invocation loan ancestry", span);
                        return None;
                    }
                    if self.budget < values.len() + 1 {
                        self.exhausted = true;
                        return None;
                    }
                    self.budget -= values.len() + 1;
                    self.visits += values.len() + 1;
                    let Some(set) = self.loans.intern(values.into_iter().collect()) else {
                        self.exhausted = true;
                        return None;
                    };
                    sets[index] = Some(set);
                    progress = true;
                    self.reporter.reborrow(
                        self.point,
                        LoanId::Call {
                            event,
                            target,
                            index: index as u32,
                        },
                        event,
                        &self.loans.values[set.0 as usize],
                    );
                }
            }
            if sets.iter().all(Option::is_some) {
                return sets.into_iter().collect();
            }
            if !progress {
                break;
            }
        }
        self.unsupported("a cyclic exported memory loan graph", span);
        None
    }

    fn memory_value(
        &mut self,
        value: &MemoryValue,
        entries: &[(Value, bool)],
        sets: &[LoanSetId],
        invocation: Invocation,
        depth: usize,
    ) -> Option<Value> {
        let Invocation {
            event,
            target,
            span,
        } = invocation;
        if depth >= 128 || self.budget == 0 {
            self.exhausted = true;
            return None;
        }
        self.budget -= 1;
        self.visits += 1;
        if let [MemoryOrigin::Opaque(index)] = value.origins.as_slice()
            && value.fields.is_none()
            && value.functions.is_empty()
        {
            return Some(entries.get(*index)?.0.clone());
        }
        let mut result = Value::scalar();
        result.functions.extend(&value.functions);
        result.causes.insert(event);
        for origin in &value.origins {
            match origin {
                MemoryOrigin::Static => {
                    result.origins.insert(Origin::Static);
                }
                MemoryOrigin::Opaque(index) => {
                    result
                        .origins
                        .extend(entries.get(*index)?.0.origins.iter().cloned());
                }
                MemoryOrigin::Reference {
                    place,
                    precise,
                    mutable,
                    loan,
                } => {
                    let (entry, exact) = entries.get(place.input)?;
                    for source in &entry.origins {
                        match source {
                            Origin::Borrow {
                                place: base,
                                precise: source_precise,
                                mutable: permission,
                                loan: source_loan,
                                parents,
                                event: source_event,
                                ..
                            } => {
                                let exact = *exact && *source_precise && *precise;
                                let base = if exact {
                                    self.places.projected(*base, &place.fields)?
                                } else {
                                    *base
                                };
                                let (loan, parents, event) = match *loan {
                                    MemoryLoan::Input(input) if input == place.input => {
                                        (*source_loan, *parents, *source_event)
                                    }
                                    MemoryLoan::Input(_) => {
                                        self.unsupported(
                                            "an inconsistent input loan mapping",
                                            span,
                                        );
                                        return None;
                                    }
                                    MemoryLoan::Fresh(index) => (
                                        LoanId::Call {
                                            event,
                                            target,
                                            index,
                                        },
                                        *sets.get(index as usize)?,
                                        event,
                                    ),
                                };
                                result.origins.insert(Origin::Borrow {
                                    place: base,
                                    precise: exact,
                                    event,
                                    mutable: *permission && *mutable,
                                    loan,
                                    parents,
                                });
                            }
                            Origin::Static => {
                                result.origins.insert(Origin::Static);
                            }
                            Origin::OpaqueInput(_) => {
                                self.unsupported("an opaque memory summary input", span);
                                return None;
                            }
                        }
                    }
                }
            }
        }
        if let Some(fields) = &value.fields {
            result.fields = Some(
                fields
                    .iter()
                    .map(|v| self.memory_value(v, entries, sets, invocation, depth + 1))
                    .collect::<Option<_>>()?,
            );
        }
        Some(result)
    }

    pub(super) fn apply_memory(
        &mut self,
        summary: &MemorySummary,
        contract: &RegionContract,
        arguments: &[Value],
        invocation: Invocation,
        state: &mut State,
    ) -> Value {
        let Invocation {
            event,
            target,
            span,
        } = invocation;
        if !summary.normal_return {
            state.normal = false;
            return Value::default();
        }
        let Some(entries) = self.input_values(summary, contract, arguments, state, span) else {
            self.unsupported("memory summary input paths", span);
            return Value::default();
        };
        let Some(sets) = self.call_parents(summary, &entries, event, target, span) else {
            return Value::default();
        };
        let Some(returned) = self.memory_value(&summary.returned, &entries, &sets, invocation, 0)
        else {
            self.unsupported("the memory summary return value", span);
            return Value::default();
        };
        // Resolve every address and payload before changing caller memory. This
        // keeps entry snapshots valid when one effect overwrites another path.
        let mut writes = Vec::new();
        for write in &summary.writes {
            let Some((entry, exact)) = entries.get(write.target.input) else {
                return Value::default();
            };
            let Some(value) = self.memory_value(&write.value, &entries, &sets, invocation, 0)
            else {
                self.unsupported("a memory summary write payload", span);
                return Value::default();
            };
            let mut targets = Vec::new();
            for origin in &entry.origins {
                let Origin::Borrow {
                    place,
                    precise,
                    mutable,
                    loan,
                    parents,
                    ..
                } = origin
                else {
                    self.unsupported("a memory summary write destination", span);
                    return Value::default();
                };
                let precise = *precise && *exact;
                let Some(place) = (if precise {
                    self.places.projected(*place, &write.target.fields)
                } else {
                    Some(*place)
                }) else {
                    self.unsupported("a memory summary field path", span);
                    return Value::default();
                };
                let via = self.lineage(*parents, Some(*loan), None);
                targets.push(Target::Place {
                    place,
                    precise,
                    via,
                    projected: true,
                    mutable: *mutable,
                });
            }
            writes.push((targets, value, write.definite));
        }
        let mut valid = returned.valid;
        for (targets, mut value, definite) in writes {
            let strong = definite && targets.len() == 1;
            for target in &targets {
                let Target::Place { place, precise, .. } = target else {
                    unreachable!()
                };
                value.valid &= self.access(target, Access::Write, span, state);
                value.valid &= self.typed_regions(
                    self.places.ty(*place),
                    &value,
                    state,
                    span,
                    "E-REGION-STORE",
                    0,
                );
                value.valid &= self.input_store(*place, &value, span);
                valid &= value.valid;
                self.bind(
                    *place,
                    Some(&value),
                    event,
                    state,
                    if strong && *precise {
                        Update::Strong
                    } else {
                        Update::Weak
                    },
                );
            }
        }
        Value { valid, ..returned }
    }
}
