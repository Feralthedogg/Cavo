use super::*;

impl Flow<'_, '_> {
    pub(super) fn transfer(
        &self,
        id: BlockId,
        block: &Block,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        for (index, statement) in block.statements.iter().enumerate() {
            self.statement(
                &statement.kind,
                self.sites.blocks[id.0 as usize][index],
                state,
            )
            .map_err(|error| error.at(statement.span))?;
        }
        self.exit(&block.terminator, state)
            .map_err(|error| error.at(block.span))
    }

    fn statement(
        &self,
        statement: &StatementKind,
        site: Site,
        state: &mut State,
    ) -> Result<(), InvariantError> {
        match statement {
            StatementKind::RegistryStart(local) => {
                require(
                    state.registries[local.0 as usize] == Registry::Closed,
                    "task registry was initialized twice or after admission",
                )?;
                self.initialize(&Place::local(*local), state)?;
                state.registries[local.0 as usize] = Registry::Empty;
            }
            StatementKind::Contract(contract) => {
                for argument in &contract.atom.arguments {
                    self.consume(argument, state)?;
                }
            }
            StatementKind::EnterScope(scope) => {
                require(
                    state.scopes.last().copied()
                        == self.verifier.body.scopes[scope.0 as usize].parent,
                    "scope entered outside its lexical parent",
                )?;
                state.scopes.push(*scope);
            }
            StatementKind::ExitScope(scope) => self.exit_scope(*scope, state)?,
            StatementKind::StorageLive(local) => self.storage_live(*local, state)?,
            StatementKind::StorageDead(local) => self.storage_dead(*local, state)?,
            StatementKind::Argument(local) => self.argument(*local, state)?,
            StatementKind::IteratorStart { iterator, value } => {
                self.iterator_start(*iterator, value, state)?
            }
            StatementKind::Assign { destination, value } => {
                self.assign(destination, value, site, state)?
            }
        }
        Ok(())
    }

    fn exit_scope(&self, scope: ScopeId, state: &mut State) -> Result<(), InvariantError> {
        require(
            state.scopes.last() == Some(&scope),
            "scope exit does not match the active scope",
        )?;
        require(
            self.verifier
                .body
                .locals
                .iter()
                .enumerate()
                .all(|(index, local)| {
                    local.scope != scope || local.kind == LocalKind::Return || !state.live[index]
                }),
            "scope exited with live local storage",
        )?;
        state.scopes.pop();
        Ok(())
    }

    fn storage_live(&self, local: LocalId, state: &mut State) -> Result<(), InvariantError> {
        let index = local.0 as usize;
        require(!state.live[index], "local storage is already live")?;
        let binding = self.verifier.body.local(local);
        if binding.kind == LocalKind::TaskRegistry {
            require(
                state.registries[index] != Registry::MayOwn,
                "task registry storage ended before the cancellation-immune drain",
            )?;
            state.registries[index] = Registry::Closed;
        }
        require(
            binding.kind == LocalKind::Return || state.scopes.contains(&binding.scope),
            "storage starts outside its declaring scope",
        )?;
        state.live[index] = true;
        self.paths
            .set(&Access::owned(self.paths.roots[index]), state, Init::No);
        state.captures[index] = None;
        state.predicates[index] = None;
        state.bounds.retain(|(base, element)| {
            base.local != local
                && *element != local
                && !base.projection.contains(&Projection::Index(local))
        });
        state
            .variants
            .retain(|id| self.sites.tests[*id].place.local != local);
        Ok(())
    }

    fn storage_dead(&self, local: LocalId, state: &mut State) -> Result<(), InvariantError> {
        let index = local.0 as usize;
        require(state.live[index], "local storage is already dead")?;
        let binding = self.verifier.body.local(local);
        if binding.kind == LocalKind::TaskRegistry {
            require(
                state.registries[index] == Registry::Drained,
                "task registry storage ended before the cancellation-immune drain",
            )?;
            state.registries[index] = Registry::Closed;
        }
        let root = Access::owned(self.paths.roots[index]);
        let needs_cleanup = binding.kind == LocalKind::ArrayIterator
            || self.verifier.properties.get(binding.ty).may_drop;
        require(
            binding.kind == LocalKind::Address
                || !needs_cleanup
                || !self.paths.may_live(self.paths.roots[index], state),
            "storage ended before dropping its initialized values",
        )?;
        self.invalidate_captures(&root, state);
        self.invalidate_write(&Place::local(local), false, state);
        state.live[index] = false;
        self.paths.set(&root, state, Init::No);
        state.captures[index] = None;
        state.predicates[index] = None;
        Ok(())
    }

    fn argument(&self, local: LocalId, state: &mut State) -> Result<(), InvariantError> {
        let index = local.0 as usize;
        require(
            state.live[index] && !self.paths.may_live(self.paths.roots[index], state),
            "parameter initialized twice or outside live storage",
        )?;
        self.paths
            .set(&Access::owned(self.paths.roots[index]), state, Init::Yes);
        Ok(())
    }

    fn iterator_start(
        &self,
        iterator: LocalId,
        value: &Operand,
        state: &mut State,
    ) -> Result<(), InvariantError> {
        let index = iterator.0 as usize;
        require(
            state.live[index] && !self.paths.may_live(self.paths.roots[index], state),
            "iterator initialized twice or outside live storage",
        )?;
        self.consume(value, state)?;
        self.paths
            .set(&Access::owned(self.paths.roots[index]), state, Init::Yes);
        Ok(())
    }

    fn assign(
        &self,
        destination: &Place,
        value: &Rvalue,
        site: Site,
        state: &mut State,
    ) -> Result<(), InvariantError> {
        if let Site::Capture(capture) = site {
            self.access(self.sites.captures[capture], state, 0)?;
            let index = destination.local.0 as usize;
            require(state.live[index], "capture assigned to dead address local")?;
            let fresh = !self.paths.may_live(self.paths.roots[index], state);
            self.invalidate_write(destination, fresh, state);
            self.paths
                .set(&Access::owned(self.paths.roots[index]), state, Init::Yes);
            state.captures[index] = Some(capture);
            return Ok(());
        }
        let predicate = match site {
            Site::Predicate(id) => Some(id),
            _ => self.predicate_value(value, state),
        };
        let target = self.access(destination, state, 0)?;
        let fresh = destination.projection.is_empty()
            && target
                .node
                .is_some_and(|node| !self.paths.may_live(node, state));
        self.evaluate(value, state)?;
        self.invalidate_captures(&target, state);
        self.initialize(destination, state)?;
        self.invalidate_write(destination, fresh, state);
        if destination.projection.is_empty() {
            state.predicates[destination.local.0 as usize] = predicate;
        }
        Ok(())
    }

    fn predicate_value(&self, value: &Rvalue, state: &State) -> Option<usize> {
        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = value else {
            return None;
        };
        place
            .projection
            .is_empty()
            .then(|| state.predicates[place.local.0 as usize])
            .flatten()
    }

    fn exit(&self, exit: &Terminator, state: &mut State) -> Result<Edges, InvariantError> {
        match exit {
            Terminator::Spawn { .. } => self.spawn(exit, state),
            Terminator::TaskDrain {
                registry,
                next,
                abort,
                ..
            } => self.drain(*registry, *next, *abort, state),
            Terminator::Goto(target) => Ok(vec![(*target, state.clone())]),
            Terminator::Switch { condition, yes, no } => self.switch(condition, *yes, *no, state),
            Terminator::Call { .. } | Terminator::DynCall { .. } => self.call(exit, state),
            Terminator::Checked {
                value,
                destination,
                normal,
                trap,
            } => self.checked(value, destination, *normal, *trap, state),
            Terminator::Bounds {
                base,
                index,
                normal,
                trap,
            } => self.bounds(base, *index, *normal, *trap, state),
            Terminator::IteratorNext {
                iterator,
                destination,
                some,
                none,
            } => self.iterator_next(*iterator, destination, *some, *none, state),
            Terminator::Drop {
                place,
                next,
                unwind,
            } => self.drop_value(place, *next, *unwind, state),
            Terminator::Return => {
                self.returned(state)?;
                Ok(Vec::new())
            }
            Terminator::Resume(_) => {
                require(
                    state.scopes.is_empty() && state.live.iter().all(|live| !live),
                    "abnormal exit bypasses cleanup",
                )?;
                Ok(Vec::new())
            }
            Terminator::Abort | Terminator::Unreachable => Ok(Vec::new()),
        }
    }

    fn spawn(&self, exit: &Terminator, state: &mut State) -> Result<Edges, InvariantError> {
        let Terminator::Spawn {
            registry,
            callee,
            arguments,
            destination,
            normal,
            panic,
            cancel,
            ..
        } = exit
        else {
            unreachable!("spawn transfer")
        };
        require(
            matches!(
                state.registries[registry.0 as usize],
                Registry::Empty | Registry::MayOwn
            ),
            "spawn attempted after admission was sealed or before registry initialization",
        )?;
        self.read(&Place::local(*registry), state)?;
        self.consume(callee, state)?;
        for argument in arguments {
            self.consume(argument, state)?;
        }
        state.registries[registry.0 as usize] = Registry::MayOwn;
        let failure = state.clone();
        self.initialize(destination, state)?;
        state.forget_guards();
        Ok(vec![
            (*normal, state.clone()),
            (*panic, failure.clone()),
            (*cancel, failure),
        ])
    }

    fn drain(
        &self,
        registry: LocalId,
        next: BlockId,
        abort: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        require(
            matches!(
                state.registries[registry.0 as usize],
                Registry::Empty | Registry::MayOwn
            ),
            "task drain repeated, uninitialized, or path-inconsistent",
        )?;
        self.read(&Place::local(registry), state)?;
        state.registries[registry.0 as usize] = Registry::Drained;
        state.forget_guards();
        Ok(vec![(next, state.clone()), (abort, state.clone())])
    }

    fn switch(
        &self,
        condition: &Operand,
        yes: BlockId,
        no: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        let predicate = match condition {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                state.predicates[place.local.0 as usize]
            }
            _ => None,
        };
        self.consume(condition, state)?;
        if let Operand::Constant {
            value: hir::Constant::Bool(value),
            ..
        } = condition
        {
            return Ok(vec![(if *value { yes } else { no }, state.clone())]);
        }
        let mut matched = state.clone();
        if let Some(predicate) = predicate {
            if state.variants.contains(&predicate) {
                return Ok(vec![(yes, state.clone())]);
            }
            let test = &self.sites.tests[predicate];
            if state.variants.iter().any(|&id| {
                self.sites.tests[id].place == test.place
                    && self.sites.tests[id].variant != test.variant
            }) {
                return Ok(vec![(no, state.clone())]);
            }
            require(
                matched.variants.len() < 1024,
                "MIR variant fact budget exceeded",
            )?;
            matched.variants.insert(predicate);
        }
        Ok(vec![(yes, matched), (no, state.clone())])
    }

    fn call(&self, exit: &Terminator, state: &mut State) -> Result<Edges, InvariantError> {
        let (prefix, arguments, destination, normal, panic, cancel) = match exit {
            Terminator::Call {
                callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => (callee, arguments, destination, normal, panic, cancel),
            Terminator::DynCall {
                receiver,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => (receiver, arguments, destination, normal, panic, cancel),
            _ => unreachable!("call edge handling"),
        };
        self.access(destination, state, 0)?;
        self.consume(prefix, state)?;
        for argument in arguments {
            self.consume(argument, state)?;
        }
        if self.may_mutate(prefix)?
            || arguments
                .iter()
                .any(|argument| self.may_mutate(argument).unwrap_or(true))
        {
            self.forget_guarded_captures(state);
        }
        state.forget_guards();
        let failure = state.clone();
        self.initialize(destination, state)?;
        Ok(vec![
            (*normal, state.clone()),
            (*panic, failure.clone()),
            (*cancel, failure),
        ])
    }

    fn may_mutate(&self, value: &Operand) -> Result<bool, InvariantError> {
        let ty = self.verifier.operand(value)?;
        match self.verifier.ty(ty)? {
            Ty::Reference { mutable: false, .. } => Ok(false),
            Ty::Pointer { .. } | Ty::Reference { mutable: true, .. } => Ok(true),
            _ => Ok(self.verifier.properties.get(ty).references),
        }
    }

    fn forget_guarded_captures(&self, state: &mut State) {
        let invalid: Vec<_> = state
            .captures
            .iter()
            .enumerate()
            .filter_map(|(local, capture)| {
                let place = self.sites.captures[(*capture)?];
                let guarded = guarded(place)
                    || self
                        .access(place, state, 1)
                        .is_ok_and(|access| !access.tags.is_empty());
                guarded.then_some(local)
            })
            .collect();
        for local in invalid {
            state.captures[local] = None;
        }
    }

    fn checked(
        &self,
        value: &Rvalue,
        destination: &Place,
        normal: BlockId,
        trap: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        let access = self.access(destination, state, 0)?;
        self.evaluate(value, state)?;
        let failure = state.clone();
        self.invalidate_captures(&access, state);
        self.initialize(destination, state)?;
        self.invalidate_write(destination, true, state);
        Ok(vec![(normal, state.clone()), (trap, failure)])
    }

    fn bounds(
        &self,
        base: &Place,
        index: LocalId,
        normal: BlockId,
        trap: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        self.read(base, state)?;
        self.read(&Place::local(index), state)?;
        let failure = state.clone();
        require(state.bounds.len() < 1024, "MIR bounds fact budget exceeded")?;
        state.bounds.insert((base.clone(), index));
        Ok(vec![(normal, state.clone()), (trap, failure)])
    }

    fn iterator_next(
        &self,
        iterator: LocalId,
        destination: &Place,
        some: BlockId,
        none: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        self.read(&Place::local(iterator), state)?;
        let target = self.access(destination, state, 0)?;
        require(
            target
                .node
                .is_some_and(|node| !self.paths.may_live(node, state)),
            "iterator output must be uninitialized before selecting an edge",
        )?;
        let exhausted = state.clone();
        self.initialize(destination, state)?;
        self.invalidate_write(destination, true, state);
        Ok(vec![(some, state.clone()), (none, exhausted)])
    }

    fn drop_value(
        &self,
        place: &Place,
        next: BlockId,
        unwind: BlockId,
        state: &mut State,
    ) -> Result<Edges, InvariantError> {
        let access = self.access(place, state, 0)?;
        if access.borrowed && access.node.is_none() {
            self.drop_replacement(place, next)?;
        }
        self.invalidate_captures(&access, state);
        self.paths.set(&access, state, Init::No);
        self.invalidate_write(place, false, state);
        Ok(vec![(next, state.clone()), (unwind, state.clone())])
    }

    fn drop_replacement(&self, place: &Place, next: BlockId) -> Result<(), InvariantError> {
        // References must expose initialized pointees on every observable exit.
        // A replacement may end the old value only when its already evaluated
        // successor stores the new value before any read, call or branch.
        let replacement = self.verifier.body.block(next).statements.first();
        let Some(Statement {
            kind:
                StatementKind::Assign {
                    destination,
                    value: Rvalue::Use(value),
                },
            ..
        }) = replacement
        else {
            return fail("borrowed Drop must immediately restore its pointee");
        };
        require(
            destination == place,
            "borrowed Drop restores a different place",
        )?;
        if let Operand::Copy(source) | Operand::Move(source) = value {
            require(
                !source.projection.contains(&Projection::Deref),
                "borrowed Drop replacement must use an already evaluated value",
            )?;
        }
        Ok(())
    }

    fn returned(&self, state: &State) -> Result<(), InvariantError> {
        require(state.scopes.is_empty(), "return bypasses lexical cleanup")?;
        let returned = self.verifier.body.return_local.0 as usize;
        require(
            state.live[returned] && self.paths.initialized(self.paths.roots[returned], state),
            "return value is uninitialized or dead",
        )?;
        require(
            state
                .live
                .iter()
                .enumerate()
                .all(|(index, live)| index == returned || !live),
            "return leaves ordinary local storage live",
        )
    }
}
