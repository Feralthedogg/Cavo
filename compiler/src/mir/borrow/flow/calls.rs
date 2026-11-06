use super::*;

struct Snapshot {
    parameters: Vec<Value>,
    pointees: Vec<Value>,
    paths: Vec<(u32, Vec<Key>)>,
    values: Vec<Value>,
    targets: Vec<Resolved>,
    fallback: Loans,
}

struct Invocation<'a> {
    destination: &'a Place,
    exits: [BlockId; 3],
    targets: BTreeSet<hir::DefId>,
    arguments: Vec<Value>,
    unknown: bool,
}

impl<R: Reporter> Evaluator<'_, '_, R> {
    pub(super) fn call(
        &mut self,
        terminator: &Terminator,
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let call = self.invocation(terminator, &mut state);
        if call.targets.len() == 1
            && !call.unknown
            && let Some(&role) = call
                .targets
                .first()
                .and_then(|definition| self.context.hir.contracts.intrinsics.get(definition))
        {
            return match role {
                crate::contracts::Intrinsic::TaskJoin
                | crate::contracts::Intrinsic::TaskIgnore
                | crate::contracts::Intrinsic::TaskCancel => {
                    self.task_operation(role, &call.arguments, call.destination, call.exits, state)
                }
                _ => self.memory_intrinsic(
                    role,
                    &call.arguments,
                    call.destination,
                    call.exits[0],
                    state,
                ),
            };
        }
        if call.targets.is_empty() || call.unknown {
            return self.unknown_call(&call, state);
        }
        self.known_call(&call, state)
    }

    fn known_call(&mut self, call: &Invocation<'_>, state: State) -> Vec<(BlockId, State)> {
        let mut edges = Vec::new();
        for &definition in &call.targets {
            let declared = self.context.hir.modular.functions.contains_key(&definition)
                && crate::modular::usable(self.context.hir, definition);
            let summary = if declared {
                &self.context.summaries.declared[definition.0 as usize]
            } else {
                &self.context.summaries.functions[definition.0 as usize]
            };
            let Some(summary) = summary.as_ref() else {
                edges.extend(self.unknown_call(call, state.clone()));
                continue;
            };
            for &assumption in &summary.assumptions {
                self.reporter.assumption(assumption);
            }
            if summary.limited {
                edges.extend(self.unknown_call(call, state.clone()));
                continue;
            }
            if !summary.complete {
                self.gap(GapKind::CallReferenceEffects);
                if summary.normal.is_none() && summary.panic.is_none() && summary.cancel.is_none() {
                    edges.extend(self.unknown_call(call, state.clone()));
                    continue;
                }
            }
            let frame = self.context.summaries.frames[definition.0 as usize]
                .as_ref()
                .unwrap();
            let snapshot = self.snapshot(definition, frame, &call.arguments, &state);
            self.static_inputs(frame, &snapshot, &state);
            self.call_accesses(summary, &snapshot, &state);
            for (index, outcome) in [&summary.normal, &summary.panic, &summary.cancel]
                .into_iter()
                .enumerate()
            {
                if let Some(outcome) = outcome {
                    let next = self.apply_outcome(
                        definition,
                        index,
                        outcome,
                        &snapshot,
                        call.destination,
                        state.clone(),
                    );
                    edges.push((call.exits[index], next));
                }
            }
        }
        edges
    }

    fn invocation<'t>(&mut self, terminator: &'t Terminator, state: &mut State) -> Invocation<'t> {
        match terminator {
            Terminator::Call {
                callee,
                arguments,
                parameter_types,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => {
                let function = self.consume(callee, state);
                let arguments = self.consume_arguments(arguments, parameter_types, state);
                Invocation {
                    destination,
                    exits: [*normal, *panic, *cancel],
                    targets: function.functions,
                    arguments,
                    unknown: function.unknown,
                }
            }
            Terminator::DynCall {
                receiver,
                trait_method,
                arguments,
                parameter_types,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => {
                let (receiver, targets) = self.dynamic_receiver(receiver, *trait_method, state);
                let unknown = receiver.unknown || receiver.vtables.is_empty();
                let mut values = vec![receiver];
                values.extend(self.consume_arguments(arguments, parameter_types, state));
                Invocation {
                    destination,
                    exits: [*normal, *panic, *cancel],
                    targets,
                    arguments: values,
                    unknown,
                }
            }
            _ => unreachable!("call terminator"),
        }
    }

    fn dynamic_receiver(
        &mut self,
        receiver: &Operand,
        method: hir::DefId,
        state: &mut State,
    ) -> (Value, BTreeSet<hir::DefId>) {
        let receiver = self.consume(receiver, state);
        let targets = if self.context.hir.modular.functions.contains_key(&method) {
            BTreeSet::from([method])
        } else {
            receiver
                .vtables
                .iter()
                .flat_map(|&vtable| &self.context.hir.vtables[vtable as usize].slots)
                .filter(|slot| slot.declaration == method)
                .map(|slot| slot.implementation)
                .collect()
        };
        if let Ty::Function { parameters, .. } = self
            .context
            .hir
            .types
            .get(self.context.hir.definitions[method].ty)
            && let Some(&ty) = parameters.first()
        {
            self.static_constraints(&receiver, ty, state, 0);
        }
        (receiver, targets)
    }

    fn consume_arguments(
        &mut self,
        arguments: &[Operand],
        types: &[TyId],
        state: &mut State,
    ) -> Vec<Value> {
        arguments
            .iter()
            .zip(types)
            .map(|(argument, &ty)| {
                let value = self.consume(argument, state);
                self.static_constraints(&value, ty, state, 0);
                value
            })
            .collect()
    }

    fn static_constraints(&mut self, value: &Value, ty: TyId, state: &State, depth: usize) {
        if depth >= 64 {
            self.gap(GapKind::ResourceLimit);
            return;
        }
        match self.context.hir.types.get(ty) {
            Ty::Reference { region, inner, .. } => {
                if *region == crate::types::Region::Static
                    || matches!(region, crate::types::Region::Named { owner, .. } if *owner == self.context.body.definition)
                {
                    self.check_region(value, *region, state);
                }
                if self.context.properties.get(*inner).references
                    && !matches!(
                        self.context.hir.types.get(*inner),
                        Ty::Parameter { .. } | Ty::Dynamic { .. } | Ty::Str
                    )
                {
                    let target = self.value_target(value, state);
                    let value = self.read_value(&target, *inner, state);
                    self.static_constraints(&value, *inner, state, depth + 1);
                }
            }
            _ => {
                if let Some(children) =
                    summary::children(ty, self.context.hir, self.context.properties)
                {
                    for (path, ty) in children {
                        self.static_constraints(&value.project(&path), ty, state, depth + 1);
                    }
                }
            }
        }
    }

    fn static_inputs(&mut self, frame: &summary::Frame, snapshot: &Snapshot, state: &State) {
        for (index, input) in frame.inputs.iter().enumerate() {
            if input.region == crate::types::Region::Static {
                self.check_region(&snapshot.values[index], crate::types::Region::Static, state);
            }
        }
    }

    fn snapshot(
        &mut self,
        definition: hir::DefId,
        frame: &summary::Frame,
        arguments: &[Value],
        state: &State,
    ) -> Snapshot {
        let mut snapshot = Snapshot {
            parameters: arguments.to_vec(),
            pointees: Vec::with_capacity(frame.inputs.len()),
            paths: frame
                .inputs
                .iter()
                .map(|input| {
                    (
                        input.parameter,
                        input.path.iter().copied().chain([Key::Deref]).collect(),
                    )
                })
                .collect(),
            values: Vec::with_capacity(frame.inputs.len()),
            targets: Vec::with_capacity(frame.inputs.len()),
            fallback: self.return_fallback(definition, arguments, state),
        };
        for input in &frame.inputs {
            let mut inherited = Resolved::default();
            let value = match &input.storage {
                summary::Storage::Parameter { parameter, path } => {
                    arguments[*parameter as usize].project(path)
                }
                summary::Storage::Pointee {
                    input: parent,
                    path,
                } => {
                    let mut target = snapshot.targets[*parent as usize].clone();
                    for &step in path {
                        target.project(step);
                    }
                    let value = self.read_value(&target, input.ty, state);
                    inherited = target;
                    value
                }
            };
            let mut target = self.value_target(&value, state);
            // Access to a nested capability is delegated through its outer
            // reference as well. A shared outer reference stays read-only.
            target.via.extend(inherited.via);
            target.permissions.extend(inherited.permissions);
            let inner = match self.context.hir.types.get(input.ty) {
                Ty::Reference { inner, .. } => *inner,
                _ => TyId::ERROR,
            };
            snapshot
                .pointees
                .push(self.read_value(&target, inner, state));
            snapshot.values.push(value);
            snapshot.targets.push(target);
        }
        snapshot
    }

    fn return_fallback(
        &mut self,
        definition: hir::DefId,
        arguments: &[Value],
        state: &State,
    ) -> Loans {
        let Ty::Function { parameters, result } = self
            .context
            .hir
            .types
            .get(self.context.hir.definitions[definition].ty)
        else {
            return arguments.iter().flat_map(Value::loans).collect();
        };
        let Some(opaque) = self.opaque_result_parameters(*result) else {
            return arguments.iter().flat_map(Value::loans).collect();
        };
        let mut loans = Loans::new();
        for (&ty, value) in parameters.iter().zip(arguments) {
            loans.extend(self.opaque_argument_loans(ty, value, &opaque, state, 0));
        }
        loans
    }

    fn opaque_result_parameters(&mut self, result: TyId) -> Option<HashSet<TyId>> {
        let mut parameters = HashSet::new();
        let mut pending = vec![result];
        let mut visited = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !visited.insert(ty) || !self.context.properties.get(ty).references {
                continue;
            }
            if visited.len() > 128 {
                self.gap(GapKind::ResourceLimit);
                return None;
            }
            if matches!(self.context.hir.types.get(ty), Ty::Parameter { .. }) {
                parameters.insert(ty);
            } else {
                // A concrete reference can point at an entire argument. For
                // opaque values, trace the contained value rather than the
                // borrow used to reach an enclosing closure environment.
                pending.extend(
                    summary::children(ty, self.context.hir, self.context.properties)?
                        .into_iter()
                        .map(|(_, ty)| ty),
                );
            }
        }
        Some(parameters)
    }

    fn opaque_argument_loans(
        &mut self,
        ty: TyId,
        value: &Value,
        parameters: &HashSet<TyId>,
        state: &State,
        depth: usize,
    ) -> Loans {
        if parameters.contains(&ty) {
            return value.loans();
        }
        if depth >= 64 {
            self.gap(GapKind::ResourceLimit);
            return value.loans();
        }
        if !self.context.properties.get(ty).references {
            return Loans::new();
        }
        if let Ty::Reference { inner, .. } = self.context.hir.types.get(ty) {
            let target = self.value_target(value, state);
            let value = self.read_value(&target, *inner, state);
            return self.opaque_argument_loans(*inner, &value, parameters, state, depth + 1);
        }
        let mut loans = Loans::new();
        let Some(children) = summary::children(ty, self.context.hir, self.context.properties)
        else {
            // An opaque U can supply T through a trait method. Without a
            // structural shape, retain its known origins conservatively.
            return value.loans();
        };
        for (path, child) in children {
            loans.extend(self.opaque_argument_loans(
                child,
                &value.project(&path),
                parameters,
                state,
                depth + 1,
            ));
        }
        loans
    }

    pub(super) fn value_target(&self, value: &Value, state: &State) -> Resolved {
        let mut resolved = Resolved {
            unknown: value.unknown,
            ..Resolved::default()
        };
        for loan in value.loans() {
            let state = &state.loans[loan.0 as usize];
            resolved.via.insert(loan);
            resolved.via.extend(&state.parents);
            resolved.permissions.insert(loan);
            resolved.locations.extend(state.targets.iter().cloned());
            resolved.unknown |= state.unknown;
        }
        resolved.unknown |= resolved.locations.is_empty();
        resolved
    }

    fn call_accesses(
        &mut self,
        summary: &summary::FunctionSummary,
        snapshot: &Snapshot,
        state: &State,
    ) {
        for access in &summary.accesses {
            let target = footprint(&access.target, snapshot);
            self.check(
                &target,
                if access.write {
                    Access::Write
                } else {
                    Access::Read
                },
                state,
            );
        }
    }

    fn apply_outcome(
        &mut self,
        definition: hir::DefId,
        index: usize,
        outcome: &summary::Outcome,
        snapshot: &Snapshot,
        destination: &Place,
        mut state: State,
    ) -> State {
        if outcome.unmodeled {
            self.gap(GapKind::CallReferenceEffects);
        }
        let slots = self.context.sites.calls[self.point.block.0 as usize]
            .get(&definition)
            .map(|sites| sites[index].as_slice())
            .unwrap_or(&[]);
        if slots.len() < outcome.loans.len() {
            self.gap(GapKind::CallReferenceEffects);
            return if index == 0 {
                self.clobber_return(destination, state)
            } else {
                state
            };
        }
        self.fresh_loans(&outcome.loans, slots, snapshot, &mut state);
        self.apply_writes(&outcome.writes, snapshot, slots, &mut state);
        if index == 0 {
            let mut value = instantiate(
                &outcome.returned,
                snapshot,
                slots,
                self.context.sites.static_loan,
            );
            if value.unknown
                && self
                    .context
                    .properties
                    .get(self.place_type(destination))
                    .references
            {
                value
                    .fields
                    .entry(Vec::new())
                    .or_default()
                    .extend(&snapshot.fallback);
            }
            let target = self.resolve(destination, &state);
            self.check(&target, Access::Write, &state);
            self.store(&target, value, &mut state);
        }
        state
    }

    fn apply_writes(
        &mut self,
        writes: &[summary::Write],
        snapshot: &Snapshot,
        slots: &[LoanId],
        state: &mut State,
    ) {
        // Read every source from the entry snapshot before any store is applied.
        // This is required for swaps and aliases among reference-valued cells.
        let writes: Vec<_> = writes
            .iter()
            .map(|write| {
                let target = footprint(&write.target, snapshot);
                let mut value = instantiate(
                    &write.value,
                    snapshot,
                    slots,
                    self.context.sites.static_loan,
                );
                if value.unknown
                    && target.locations.iter().any(|location| {
                        self.context
                            .properties
                            .get(self.location_type(location))
                            .references
                    })
                {
                    let fallback = self.storable_loans(&snapshot.parameters, &target, state);
                    value.fields.entry(Vec::new()).or_default().extend(fallback);
                }
                (target, write.definite, value)
            })
            .collect();
        for (target, definite, value) in writes {
            let update = if definite {
                Update::Strong
            } else {
                Update::Weak
            };
            self.store_with_update(&target, value, state, update);
        }
    }

    fn fresh_loans(
        &mut self,
        loans: &[summary::FreshLoan],
        slots: &[LoanId],
        snapshot: &Snapshot,
        state: &mut State,
    ) {
        for (index, loan) in loans.iter().enumerate() {
            let mut targets = Locations::new();
            let mut parents = Loans::new();
            for target in &loan.targets {
                let target = footprint(target, snapshot);
                for location in &target.locations {
                    match location.root {
                        Root::Local(local) => parents
                            .extend(state.values[local as usize].project(&location.path).loans()),
                        Root::External(input) => parents
                            .extend(state.memory[input as usize].project(&location.path).loans()),
                        Root::Static => {}
                    }
                }
                targets.extend(target.locations);
                parents.extend(target.via);
            }
            for origin in &loan.parents {
                parents.extend(origin_loans(
                    *origin,
                    snapshot,
                    slots,
                    self.context.sites.static_loan,
                ));
            }
            if self.active.contains(&slots[index]) {
                self.gap(GapKind::BorrowGeneration);
            }
            state.loans[slots[index].0 as usize] = LoanState {
                targets,
                parents,
                unknown: loan.unknown,
            };
        }
    }

    fn unknown_call(&mut self, call: &Invocation<'_>, mut state: State) -> Vec<(BlockId, State)> {
        self.gap(GapKind::CallReferenceEffects);
        self.clobber_inputs(&call.arguments, &mut state);
        let failure = state.clone();
        let mut normal_state = self.clobber_return(call.destination, state);
        if self
            .context
            .properties
            .get(self.place_type(call.destination))
            .references
        {
            let target = self.resolve(call.destination, &normal_state);
            let mut value = Value::unknown();
            value.fields.insert(
                Vec::new(),
                call.arguments.iter().flat_map(Value::loans).collect(),
            );
            self.store(&target, value, &mut normal_state);
        }
        vec![
            (call.exits[0], normal_state),
            (call.exits[1], failure.clone()),
            (call.exits[2], failure),
        ]
    }

    fn clobber_inputs(&self, arguments: &[Value], state: &mut State) {
        for value in arguments {
            let target = self.value_target(value, state);
            if !target.unknown
                && target
                    .permissions
                    .iter()
                    .any(|loan| !self.context.loans[loan.0 as usize].mutable)
            {
                continue;
            }
            for location in target.locations {
                let references = self
                    .context
                    .properties
                    .get(self.location_type(&location))
                    .references;
                let stored = self.storable_loans(
                    arguments,
                    &Resolved {
                        locations: Locations::from([location.clone()]),
                        ..Resolved::default()
                    },
                    state,
                );
                let value = match location.root {
                    Root::Local(local) => &mut state.values[local as usize],
                    Root::External(input) => &mut state.memory[input as usize],
                    Root::Static => continue,
                };
                value.unknown = true;
                value.parameters.clear();
                value.functions.clear();
                value.vtables.clear();
                if references {
                    value.fields.entry(Vec::new()).or_default().extend(stored);
                }
            }
        }
    }

    fn location_type(&self, location: &Location) -> TyId {
        let mut ty = match location.root {
            Root::Local(local) => self.context.body.locals[local as usize].ty,
            Root::External(input) => {
                let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
                    .as_ref()
                    .expect("body frame");
                match self.context.hir.types.get(frame.inputs[input as usize].ty) {
                    Ty::Reference { inner, .. } => *inner,
                    _ => TyId::ERROR,
                }
            }
            Root::Static => return TyId::ERROR,
        };
        let mut variant = None;
        for step in &location.path {
            ty = match step {
                Key::Variant(id) => {
                    variant = Some(*id);
                    ty
                }
                Key::Deref => match self.context.hir.types.get(ty) {
                    Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                    _ => TyId::ERROR,
                },
                Key::Element => match self.context.hir.types.get(ty) {
                    Ty::Array { inner, .. }
                    | Ty::SymbolicArray { inner, .. }
                    | Ty::Slice(inner) => *inner,
                    _ => TyId::ERROR,
                },
                Key::Field(field) => {
                    let fields = if let Some(id) = variant.take() {
                        self.context.properties.variant_fields(ty, id)
                    } else {
                        self.context.properties.fields(ty)
                    };
                    fields
                        .and_then(|f| f.get(*field as usize))
                        .copied()
                        .unwrap_or(TyId::ERROR)
                }
            };
        }
        ty
    }

    fn storable_loans(&self, arguments: &[Value], target: &Resolved, state: &State) -> Loans {
        arguments
            .iter()
            .flat_map(Value::loans)
            .filter(|loan| {
                // Safe code cannot store the exclusive receiver loan into its own
                // referent. Keep other origins, including references inside it.
                !state.loans[loan.0 as usize].targets.iter().any(|source| {
                    target
                        .locations
                        .iter()
                        .any(|destination| overlap(source, destination))
                })
            })
            .collect()
    }

    fn clobber_return(&mut self, destination: &Place, mut state: State) -> State {
        let target = self.resolve(destination, &state);
        self.check(&target, Access::Write, &state);
        let value = if self
            .context
            .properties
            .get(self.place_type(destination))
            .references
        {
            Value::unknown()
        } else {
            Value::default()
        };
        self.store(&target, value, &mut state);
        state
    }
}

fn footprint(footprint: &summary::Footprint, snapshot: &Snapshot) -> Resolved {
    let mut target = snapshot.targets[footprint.input as usize].clone();
    for &step in &footprint.path {
        target.project(step);
    }
    target
}

fn origin_loans(
    origin: summary::Origin,
    snapshot: &Snapshot,
    slots: &[LoanId],
    static_loan: Option<LoanId>,
) -> Loans {
    match origin {
        summary::Origin::Input(input) => snapshot.values[input as usize].loans(),
        summary::Origin::Fresh(index) => Loans::from([slots[index as usize]]),
        summary::Origin::Static => Loans::from([static_loan.expect("summary static site")]),
    }
}

fn instantiate(
    template: &summary::Value,
    snapshot: &Snapshot,
    slots: &[LoanId],
    static_loan: Option<LoanId>,
) -> Value {
    let mut value = Value {
        unknown: template.unknown,
        functions: template.functions.clone(),
        vtables: template.vtables.clone(),
        ..Value::default()
    };
    for (path, parameters) in &template.parameters {
        for parameter in parameters {
            value.insert(path, parameter_value(parameter, snapshot));
        }
    }
    for (path, origins) in &template.fields {
        for &origin in origins {
            value
                .fields
                .entry(path.clone())
                .or_default()
                .extend(origin_loans(origin, snapshot, slots, static_loan));
            if let summary::Origin::Input(input) = origin {
                value.unknown |= snapshot.values[input as usize].unknown;
                value
                    .vtables
                    .extend(&snapshot.values[input as usize].vtables);
            }
        }
    }
    value
}

fn parameter_value(source: &summary::ParameterOrigin, snapshot: &Snapshot) -> Value {
    let input = snapshot
        .paths
        .iter()
        .enumerate()
        .filter(|(_, (parameter, prefix))| {
            *parameter == source.parameter && source.path.starts_with(prefix)
        })
        .max_by_key(|(_, (_, prefix))| prefix.len());
    if let Some((index, (_, prefix))) = input {
        return snapshot.pointees[index].project(&source.path[prefix.len()..]);
    }
    if source.path.contains(&Key::Deref) {
        return Value::unknown();
    }
    snapshot
        .parameters
        .get(source.parameter as usize)
        .map(|value| value.project(&source.path))
        .unwrap_or_else(Value::unknown)
}
