use super::*;

impl<R: Reporter> Evaluator<'_, '_, R> {
    pub(super) fn spawn(
        &mut self,
        terminator: &Terminator,
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let Terminator::Spawn {
            registry,
            callee,
            arguments,
            destination,
            normal,
            panic,
            cancel,
            ..
        } = terminator
        else {
            unreachable!("spawn transfer");
        };
        let mut retained = self.consume(callee, &mut state);
        let mut captures = retained.clone();
        for (index, argument) in arguments.iter().enumerate() {
            let value = self.consume(argument, &mut state);
            captures.insert(&[Key::Field(index as u32 + 1)], value.clone());
            retained.merge(value);
        }
        // The scope registry outlives observation handles, including every
        // admission failure/cancellation path. Never release it at last handle use.
        let site = TaskSlot {
            registry: *registry,
            spawn: self.point.block,
        };
        let many = if state.task_slots.contains_key(&site) {
            TaskCount::MayBeMany
        } else {
            TaskCount::AtMostOne
        };
        state.task_slots.insert(site, many);
        state.values[registry.0 as usize].insert(&[Key::Field(site.spawn.0)], retained.clone());
        let failed = state.clone();
        let admission = self.admission_value(retained, captures, site);
        let destination = self.resolve(destination, &state);
        self.store(&destination, admission, &mut state);
        vec![
            (*normal, state),
            (*panic, failed.clone()),
            (*cancel, failed),
        ]
    }

    fn admission_value(&self, mut retained: Value, mut captures: Value, site: TaskSlot) -> Value {
        retained.tasks.insert(site);
        retained
            .task_fields
            .insert(site, BTreeSet::from([Vec::new()]));
        retained
            .task_paths
            .insert(site, BTreeSet::from([Vec::new()]));
        captures
            .task_fields
            .insert(site, BTreeSet::from([Vec::new()]));
        let result = self
            .context
            .hir
            .enums
            .iter()
            .find(|item| Some(item.definition) == self.context.hir.tasks.result)
            .expect("Result provider");
        let mut admission = Value::default();
        admission.insert(&[Key::Variant(result.variants[0]), Key::Field(0)], retained);
        admission.insert(
            &[
                Key::Variant(result.variants[1]),
                Key::Field(0),
                Key::Field(0),
            ],
            captures,
        );

        admission
    }

    pub(super) fn drain(&mut self, registry: LocalId, state: &mut State) {
        self.check_task_scope_escape(registry, state);
        let value = state.values[registry.0 as usize].clone();
        for loan in value.loans() {
            let target = Resolved {
                locations: state.loans[loan.0 as usize].targets.clone(),
                via: ancestors(loan, state),
                permissions: Loans::from([loan]),
                unknown: state.loans[loan.0 as usize].unknown,
            };
            self.check(&target, Access::Read, state);
        }
        state.values[registry.0 as usize] = Value::default();
        state.task_slots.retain(|site, _| site.registry != registry);
    }

    pub(super) fn task_operation(
        &mut self,
        role: crate::contracts::Intrinsic,
        arguments: &[Value],
        destination: &Place,
        exits: [BlockId; 3],
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let cancelled = state.clone();
        let mut value = arguments.first().cloned().unwrap_or_default();
        if value
            .tasks
            .iter()
            .any(|site| !state.task_slots.contains_key(site))
        {
            self.finding(FindingKind::TaskEscape, None);
        }
        if role == crate::contracts::Intrinsic::TaskJoin && value.tasks.len() == 1 {
            let &site = value.tasks.first().expect("one task observation");
            if state.task_slots.get(&site) == Some(&TaskCount::AtMostOne) {
                state.values[site.registry.0 as usize].clear(&[Key::Field(site.spawn.0)]);
                for value in state.values.iter_mut().chain(&mut state.memory) {
                    value.observe(site);
                }
                state.task_slots.remove(&site);
            }
        }
        value.tasks.clear();
        value.task_paths.clear();
        value.task_fields.clear();
        value.parameters.clear();
        value.opaque = false;
        let mut returned = Value::default();
        if role == crate::contracts::Intrinsic::TaskJoin
            && self
                .context
                .properties
                .carries_origins(self.place_type(destination))
        {
            // The child may return any permitted capture origin. A precise
            // payload shape must not turn that unknown into no references.
            value.unknown = true;
            let result = self
                .context
                .hir
                .enums
                .iter()
                .find(|item| Some(item.definition) == self.context.hir.tasks.result)
                .expect("Result provider");
            returned.insert(&[Key::Variant(result.variants[0]), Key::Field(0)], value);
        }
        let target = self.resolve(destination, &state);
        self.store(&target, returned, &mut state);
        if role == crate::contracts::Intrinsic::TaskJoin {
            vec![(exits[0], state), (exits[2], cancelled)]
        } else {
            vec![(exits[0], state)]
        }
    }

    fn check_task_scope_escape(&mut self, registry: LocalId, state: &State) {
        let scope = self.context.body.local(registry).scope;
        for (index, value) in state.values.iter().enumerate() {
            if !value.tasks.iter().any(|site| site.registry == registry) {
                continue;
            }
            let mut owner = Some(self.context.body.locals[index].scope);
            let mut contained = false;
            while let Some(candidate) = owner {
                if candidate == scope {
                    contained = true;
                    break;
                }
                owner = self.context.body.scopes[candidate.0 as usize].parent;
            }
            if !contained {
                self.finding(FindingKind::TaskEscape, None);
            }
        }
        if state
            .memory
            .iter()
            .any(|value| value.tasks.iter().any(|site| site.registry == registry))
        {
            self.finding(FindingKind::TaskEscape, None);
        }
    }
}
