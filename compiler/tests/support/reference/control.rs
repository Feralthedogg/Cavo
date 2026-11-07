use super::*;
use mir::drop::{Instruction, Terminator as CleanupExit};

enum Step {
    Next(usize),
    Finish(Outcome),
}

impl Machine<'_> {
    pub(super) fn execute(&mut self, frame: &mut Frame<'_>) -> Result<Outcome> {
        let cleanup = frame.cleanup;
        let mut block = cleanup.entry.0 as usize;
        loop {
            self.tick()?;
            let current = cleanup
                .blocks
                .get(block)
                .ok_or(Error::Undefined("invalid cleanup target"))?;
            for instruction in &current.instructions {
                self.instruction(instruction, frame)?;
            }
            match self.cleanup_exit(&current.terminator, frame)? {
                Step::Next(next) => block = next,
                Step::Finish(outcome) => return Ok(outcome),
            }
        }
    }

    fn instruction(&mut self, instruction: &Instruction, frame: &mut Frame<'_>) -> Result<()> {
        match instruction {
            Instruction::CoreStatement { source, statement } => {
                let body = frame.body;
                let statement = body
                    .blocks
                    .get(source.0 as usize)
                    .and_then(|block| block.statements.get(*statement as usize))
                    .ok_or(Error::Undefined("invalid core statement"))?;
                self.statement(&statement.kind, frame)
            }
            Instruction::SetFlag { flag, value } => {
                *frame
                    .flags
                    .get_mut(flag.0 as usize)
                    .ok_or(Error::Undefined("invalid drop flag"))? =
                    *value == mir::drop::FlagValue::Set;
                Ok(())
            }
            Instruction::RecomputeFlag { flag, all } => {
                let mut initialized = true;
                for item in all {
                    initialized &= *frame
                        .flags
                        .get(item.0 as usize)
                        .ok_or(Error::Undefined("invalid initialization flag"))?;
                }
                *frame
                    .flags
                    .get_mut(flag.0 as usize)
                    .ok_or(Error::Undefined("invalid drop flag"))? = initialized;
                Ok(())
            }
        }
    }

    fn statement(&mut self, statement: &mir::StatementKind, frame: &mut Frame<'_>) -> Result<()> {
        use mir::StatementKind as S;
        match statement {
            S::StorageLive(local) => self.storage_live(*local, frame),
            S::StorageDead(local) => self.storage_dead(*local, frame),
            S::EnterScope(scope) => {
                frame.scopes.push(*scope);
                Ok(())
            }
            S::ExitScope(scope) => {
                if frame.scopes.pop() != Some(*scope) {
                    return Err(Error::Undefined("scope stack mismatch"));
                }
                Ok(())
            }
            S::Argument(local) => {
                let value = frame
                    .arguments
                    .get(frame.argument)
                    .cloned()
                    .ok_or(Error::Undefined("missing argument"))?;
                frame.argument += 1;
                let destination = self.place(&mir::Place::local(*local), frame)?;
                self.write(&destination, &value)
            }
            S::Assign { destination, value } => self.assign(destination, value, frame),
            S::IteratorStart { iterator, value } => {
                let value = self.operand(value, frame)?;
                let address = self.place(&mir::Place::local(*iterator), frame)?;
                self.write(&address, &value)?;
                frame.cursors.insert(*iterator, 0);
                Ok(())
            }
            S::RegistryStart(local) => {
                frame.registries.insert(*local, Vec::new());
                Ok(())
            }
            S::Contract(_) => Ok(()), // Logical evidence is not an executable safety check.
        }
    }

    fn storage_live(&mut self, local: mir::LocalId, frame: &mut Frame<'_>) -> Result<()> {
        let binding = frame
            .body
            .locals
            .get(local.0 as usize)
            .ok_or(Error::Undefined("invalid local ID"))?;
        if frame.locals[local.0 as usize].is_some() {
            return Err(Error::Undefined("storage already live"));
        }
        let size = if binding.kind == mir::LocalKind::Address {
            0
        } else {
            self.layout(binding.ty)?.size
        };
        frame.locals[local.0 as usize] = Some(self.memory.stack(size)?);
        Ok(())
    }

    fn storage_dead(&mut self, local: mir::LocalId, frame: &mut Frame<'_>) -> Result<()> {
        if frame
            .registries
            .get(&local)
            .is_some_and(|tasks| !tasks.is_empty())
        {
            return Err(Error::Undefined("registry storage ended before drain"));
        }
        let pointer = frame
            .locals
            .get_mut(local.0 as usize)
            .and_then(Option::take)
            .ok_or(Error::Undefined("storage already dead"))?;
        frame.captures.remove(&local);
        frame.cursors.remove(&local);
        self.memory.end_stack(&pointer)
    }

    fn assign(
        &mut self,
        destination: &mir::Place,
        value: &mir::Rvalue,
        frame: &mut Frame<'_>,
    ) -> Result<()> {
        if let mir::Rvalue::AddressOf(place) = value {
            let address = self.place(place, frame)?;
            frame.captures.insert(destination.local, address);
            return Ok(());
        }
        let address = self.place(destination, frame)?;
        let value = self
            .value(value, address.ty, frame)
            .map_err(|error| match error {
                Error::Trap(_) => Error::Undefined("trapping arithmetic bypassed a checked edge"),
                other => other,
            })?;
        self.write(&address, &value)
    }

    fn cleanup_exit(&mut self, exit: &CleanupExit, frame: &mut Frame<'_>) -> Result<Step> {
        let next = match exit {
            CleanupExit::Core { source, successors } => {
                return self.core_exit(*source, successors, frame);
            }
            CleanupExit::Goto(next) => *next,
            CleanupExit::TestFlag {
                flag,
                initialized,
                clear,
            } => {
                if *frame
                    .flags
                    .get(flag.0 as usize)
                    .ok_or(Error::Undefined("invalid flag"))?
                {
                    *initialized
                } else {
                    *clear
                }
            }
            CleanupExit::TestVariant {
                place,
                variant,
                matches,
                otherwise,
            } => {
                let address = self.place(place, frame)?;
                if self.tag(&address)? == *variant {
                    *matches
                } else {
                    *otherwise
                }
            }
            CleanupExit::InvokeGlue {
                place,
                glue,
                next,
                unwind,
            } => {
                let address = self.place(place, frame)?;
                let cursor = frame.cursors.get(&place.local).copied().unwrap_or(0);
                if self.glue(*glue, &address, cursor)? {
                    *next
                } else {
                    *unwind
                }
            }
        };
        Ok(Step::Next(next.0 as usize))
    }

    fn core_exit(
        &mut self,
        source: mir::BlockId,
        successors: &[mir::drop::BlockId],
        frame: &mut Frame<'_>,
    ) -> Result<Step> {
        let body = frame.body;
        let block = body
            .blocks
            .get(source.0 as usize)
            .ok_or(Error::Undefined("invalid core target"))?;
        if let Some(outcome) = self.terminal(&block.terminator, frame)? {
            return Ok(Step::Finish(outcome));
        }
        let branch = match &block.terminator {
            mir::Terminator::Goto(_) => 0,
            mir::Terminator::Switch { condition, .. } => {
                if self.operand(condition, frame)?.boolean_value()? {
                    0
                } else {
                    1
                }
            }
            mir::Terminator::Checked {
                value, destination, ..
            } => self.checked_branch(value, destination, frame)?,
            mir::Terminator::Bounds { base, index, .. } => {
                self.bounds_branch(base, *index, frame)?
            }
            mir::Terminator::Call {
                callee,
                arguments,
                destination,
                ..
            } => self.call_branch(callee, arguments, destination, frame)?,
            mir::Terminator::DynCall {
                receiver,
                trait_method,
                arguments,
                destination,
                ..
            } => self.dynamic_branch(receiver, *trait_method, arguments, destination, frame)?,
            mir::Terminator::IteratorNext {
                iterator,
                destination,
                ..
            } => self.iterator_branch(*iterator, destination, frame)?,
            mir::Terminator::Spawn { .. } => self.spawn_branch(&block.terminator, frame)?,
            mir::Terminator::TaskDrain { registry, .. } => {
                if self.drain(*registry, frame)? {
                    0
                } else {
                    1
                }
            }
            _ => return Err(Error::Undefined("unelaborated cleanup reached execution")),
        };
        Ok(Step::Next(
            successors
                .get(branch)
                .ok_or(Error::Undefined("missing cleanup successor"))?
                .0 as usize,
        ))
    }

    fn terminal(
        &mut self,
        exit: &mir::Terminator,
        frame: &mut Frame<'_>,
    ) -> Result<Option<Outcome>> {
        let result = match exit {
            mir::Terminator::Return => {
                let address = self.place(&mir::Place::local(frame.body.return_local), frame)?;
                Outcome::Returned(self.read(&address)?)
            }
            mir::Terminator::Resume(mir::ExitKind::Panic) => Outcome::Panicked,
            mir::Terminator::Resume(mir::ExitKind::Cancel) => Outcome::Cancelled,
            mir::Terminator::Abort => Outcome::Aborted,
            mir::Terminator::Unreachable => return Err(Error::Undefined("unreachable executed")),
            _ => return Ok(None),
        };
        Ok(Some(result))
    }

    fn checked_branch(
        &mut self,
        value: &mir::Rvalue,
        destination: &mir::Place,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let address = self.place(destination, frame)?;
        match self.value(value, address.ty, frame) {
            Ok(value) => {
                self.write(&address, &value)?;
                Ok(0)
            }
            Err(Error::Trap(_)) => Ok(1),
            Err(error) => Err(error),
        }
    }

    fn bounds_branch(
        &mut self,
        base: &mir::Place,
        index: mir::LocalId,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let address = self.place(base, frame)?;
        let index = self
            .operand(&mir::Operand::Copy(mir::Place::local(index)), frame)?
            .unsigned()?;
        Ok(usize::from(index >= self.length(&address)? as u128))
    }

    fn call_branch(
        &mut self,
        callee: &mir::Operand,
        arguments: &[mir::Operand],
        destination: &mir::Place,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let callee = self.operand(callee, frame)?;
        let ValueKind::Function(definition) = callee.kind else {
            return Err(Error::Undefined("call target has no callable provenance"));
        };
        let arguments = arguments
            .iter()
            .map(|value| self.operand(value, frame))
            .collect::<Result<_>>()?;
        let address = self.place(destination, frame)?;
        let outcome = if let Some(&role) = self.program.hir.contracts.intrinsics.get(&definition) {
            self.intrinsic(role, arguments, address.ty)?
        } else {
            self.invoke(definition, arguments)?
        };
        self.call_outcome(outcome, &address)
    }

    fn call_outcome(&mut self, outcome: Outcome, destination: &Address) -> Result<usize> {
        match outcome {
            Outcome::Returned(value) => {
                self.write(destination, &value)?;
                Ok(0)
            }
            Outcome::Panicked => Ok(1),
            Outcome::Cancelled => Ok(2),
            Outcome::Aborted => Err(Error::Trap("callee aborted")),
        }
    }

    fn dynamic_branch(
        &mut self,
        receiver: &mir::Operand,
        method: hir::DefId,
        arguments: &[mir::Operand],
        destination: &mir::Place,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let receiver = self.operand(receiver, frame)?;
        let ValueKind::Pointer {
            data: Some(data),
            metadata: Some(Metadata::Vtable(index)),
        } = receiver.kind
        else {
            return Err(Error::Undefined(
                "dynamic receiver has no vtable provenance",
            ));
        };
        let table = self
            .program
            .hir
            .vtables
            .get(index as usize)
            .ok_or(Error::Undefined("invalid vtable"))?;
        let slot = table
            .slots
            .iter()
            .find(|slot| slot.declaration == method)
            .ok_or(Error::Undefined("invalid dynamic method"))?;
        let definition = slot.implementation;
        let mut values = vec![Value::pointer(receiver.ty, data, None)];
        values.extend(
            arguments
                .iter()
                .map(|value| self.operand(value, frame))
                .collect::<Result<Vec<_>>>()?,
        );
        let outcome = self.invoke(definition, values)?;
        let destination = self.place(destination, frame)?;
        self.call_outcome(outcome, &destination)
    }

    fn iterator_branch(
        &mut self,
        iterator: mir::LocalId,
        destination: &mir::Place,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let cursor = frame
            .cursors
            .get(&iterator)
            .copied()
            .ok_or(Error::Undefined("uninitialized iterator"))?;
        let array = self.place(&mir::Place::local(iterator), frame)?;
        if cursor >= self.length(&array)? {
            return Ok(1);
        }
        let element = self.element_address(&array, cursor)?;
        let value = self.read(&element)?;
        self.memory
            .invalidate(&element.pointer, self.layout(element.ty)?.size)?;
        frame.cursors.insert(iterator, cursor + 1);
        let destination = self.place(destination, frame)?;
        self.write(&destination, &value)?;
        Ok(0)
    }
}
