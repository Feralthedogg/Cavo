use super::*;
use cavo_compiler::contracts::Intrinsic as I;

impl Machine<'_> {
    pub(super) fn intrinsic(
        &mut self,
        role: I,
        arguments: Vec<Value>,
        result: TyId,
    ) -> Result<Outcome> {
        self.tick()?;
        let first = arguments
            .first()
            .ok_or(Error::Undefined("intrinsic argument"))?;
        let value = match role {
            I::AsPtr | I::AsMutPtr => Value {
                ty: result,
                kind: first.kind.clone(),
            },
            I::Length => {
                let address = self.reference_target(first)?;
                Value::bits(result, self.length(&address)?.into())
            }
            I::Allocate => return self.allocate_intrinsic(first, result),
            I::Offset => return self.offset_intrinsic(&arguments, result),
            I::Deallocate => {
                let pointer = first.address()?;
                self.memory.free(&pointer)?;
                self.events.push(Event::Freed(pointer.allocation));
                Value::unit()
            }
            I::Read | I::ReadUnaligned | I::Take => self.raw_read(role, first, result)?,
            I::Initialize | I::Replace | I::WriteUnaligned => self.raw_write(role, &arguments)?,
            I::TaskJoin => return self.join_task(first, result),
            I::TaskCancel | I::TaskIgnore => self.task_intrinsic(role, first)?,
        };
        Ok(Outcome::Returned(value))
    }

    fn allocate_intrinsic(&mut self, count: &Value, result: TyId) -> Result<Outcome> {
        let Ty::Pointer { inner, .. } = self.program.hir.types.get(result) else {
            return Err(Error::Undefined("allocation result type"));
        };
        let size = self.layout(*inner)?.size;
        let Some(bytes) = count
            .unsigned()?
            .checked_mul(size.into())
            .and_then(|bytes| u64::try_from(bytes).ok())
        else {
            return Ok(Outcome::Panicked);
        };
        let pointer = self.memory.heap(bytes)?;
        Ok(Outcome::Returned(Value::pointer(result, pointer, None)))
    }

    fn offset_intrinsic(&mut self, arguments: &[Value], result: TyId) -> Result<Outcome> {
        let first = &arguments[0];
        let Ty::Pointer { inner, .. } = self.program.hir.types.get(first.ty) else {
            return Err(Error::Undefined("offset input type"));
        };
        let size = self.layout(*inner)?.size;
        let count = arguments
            .get(1)
            .ok_or(Error::Undefined("offset count"))?
            .unsigned()?;
        let Some(bytes) = count
            .checked_mul(size.into())
            .and_then(|bytes| u64::try_from(bytes).ok())
        else {
            return Ok(Outcome::Panicked);
        };
        Ok(Outcome::Returned(Value::pointer(
            result,
            self.memory.offset(&first.address()?, bytes)?,
            None,
        )))
    }

    fn raw_write(&mut self, role: I, arguments: &[Value]) -> Result<Value> {
        let first = &arguments[0];
        let Ty::Pointer { inner, .. } = self.program.hir.types.get(first.ty) else {
            return Err(Error::Undefined("raw write input type"));
        };
        let ty = *inner;
        let value = arguments
            .get(1)
            .ok_or(Error::Undefined("raw write value"))?;
        let pointer = first.address()?;
        if role != I::WriteUnaligned {
            self.memory
                .check(&pointer, self.layout(ty)?.size, self.layout(ty)?.alignment)?;
        }
        let address = Address {
            pointer,
            ty,
            metadata: None,
            variant: None,
        };
        if role == I::Replace {
            self.read(&address)?;
        }
        self.write(&address, value)?;
        Ok(Value::unit())
    }

    fn task_intrinsic(&mut self, role: I, value: &Value) -> Result<Value> {
        if role == I::TaskCancel {
            let address = self.reference_target(value)?;
            let ValueKind::Task(task) = self.read(&address)?.kind else {
                return Err(Error::Undefined("invalid task handle"));
            };
            if self.tasks.get(task).is_none() {
                return Err(Error::Undefined("invalid task record"));
            }
            // This deterministic schedule completes children before their
            // parent resumes; a later cancellation cannot change that result.
        } else {
            let ValueKind::Task(task) = value.kind else {
                return Err(Error::Undefined("invalid task handle"));
            };
            self.observe_task(task, false)?;
        }
        Ok(Value::unit())
    }

    fn raw_read(&mut self, role: I, first: &Value, result: TyId) -> Result<Value> {
        let pointer = first.address()?;
        if role != I::ReadUnaligned {
            self.memory.check(
                &pointer,
                self.layout(result)?.size,
                self.layout(result)?.alignment,
            )?;
        }
        let address = Address {
            pointer,
            ty: result,
            metadata: None,
            variant: None,
        };
        let value = self.read(&address)?;
        if role == I::Take {
            self.memory
                .invalidate(&address.pointer, self.layout(result)?.size)?;
        }
        Ok(value)
    }

    fn reference_target(&self, value: &Value) -> Result<Address> {
        let Ty::Reference { inner, .. } = self.program.hir.types.get(value.ty) else {
            return Err(Error::Undefined("expected reference"));
        };
        let metadata = match value.kind {
            ValueKind::Pointer { metadata, .. } => metadata,
            _ => None,
        };
        Ok(Address {
            pointer: value.address()?,
            ty: *inner,
            metadata,
            variant: None,
        })
    }

    pub(super) fn spawn_branch(
        &mut self,
        exit: &mir::Terminator,
        frame: &mut Frame<'_>,
    ) -> Result<usize> {
        let mir::Terminator::Spawn {
            callee,
            arguments,
            registry,
            destination,
            ..
        } = exit
        else {
            return Err(Error::Undefined("invalid spawn"));
        };
        if self.tasks.len() >= self.limits.objects {
            return Err(Error::Limit("task budget"));
        }
        let ValueKind::Function(definition) = self.operand(callee, frame)?.kind else {
            return Err(Error::Undefined("invalid child entry"));
        };
        let arguments = arguments
            .iter()
            .map(|argument| self.operand(argument, frame))
            .collect::<Result<_>>()?;
        let index = self.tasks.len();
        self.tasks.push(Task {
            outcome: None,
            observed: false,
        });
        let outcome = self.invoke(definition, arguments)?;
        if outcome == Outcome::Aborted {
            return Err(Error::Trap("child aborted"));
        }
        self.tasks[index].outcome = Some(outcome);
        frame
            .registries
            .get_mut(registry)
            .ok_or(Error::Undefined("spawn outside a live registry"))?
            .push(index);
        let address = self.place(destination, frame)?;
        let task_ty = self.variant_field_type(address.ty, "Ok", 0)?;
        let task = Value {
            ty: task_ty,
            kind: ValueKind::Task(index),
        };
        let admission = self.variant(address.ty, "Ok", vec![task])?;
        self.write(&address, &admission)?;
        Ok(0)
    }

    fn join_task(&mut self, value: &Value, result: TyId) -> Result<Outcome> {
        let ValueKind::Task(task) = value.kind else {
            return Err(Error::Undefined("join input is not a task"));
        };
        let outcome = self
            .observe_task(task, true)?
            .ok_or(Error::Undefined("task already observed"))?;
        let value = match outcome {
            Outcome::Returned(value) => self.variant(result, "Ok", vec![value])?,
            Outcome::Panicked | Outcome::Cancelled => {
                let error = self.variant_field_type(result, "Err", 0)?;
                let error = self.variant(
                    error,
                    if outcome == Outcome::Panicked {
                        "Panicked"
                    } else {
                        "Cancelled"
                    },
                    vec![],
                )?;
                self.variant(result, "Err", vec![error])?
            }
            Outcome::Aborted => return Ok(Outcome::Aborted),
        };
        Ok(Outcome::Returned(value))
    }

    pub(super) fn observe_task(&mut self, task: usize, keep: bool) -> Result<Option<Outcome>> {
        let record = self
            .tasks
            .get_mut(task)
            .ok_or(Error::Undefined("invalid task observation"))?;
        if record.observed {
            return Err(Error::Undefined("task observation used twice"));
        }
        record.observed = true;
        let outcome = record
            .outcome
            .take()
            .ok_or(Error::Undefined("task has not completed"))?;
        if keep {
            return Ok(Some(outcome));
        }
        if let Outcome::Returned(value) = outcome {
            self.drop_value(value)?;
        }
        Ok(None)
    }

    pub(super) fn release_observation(&mut self, task: usize) -> Result<()> {
        let record = self
            .tasks
            .get_mut(task)
            .ok_or(Error::Undefined("invalid task observation"))?;
        if record.observed {
            return Err(Error::Undefined("task observation used twice"));
        }
        // Releasing a handle never takes the registry's result or its lifetime
        // responsibility. Drain and explicit ignore/join own result disposal.
        record.observed = true;
        Ok(())
    }

    pub(super) fn drain(&mut self, registry: mir::LocalId, frame: &mut Frame<'_>) -> Result<bool> {
        let tasks = frame
            .registries
            .remove(&registry)
            .ok_or(Error::Undefined("registry drained twice"))?;
        for task in tasks {
            if let Some(Outcome::Returned(value)) = self.tasks[task].outcome.take() {
                self.drop_value(value)?;
            }
        }
        Ok(true)
    }

    fn variant(&self, ty: TyId, name: &str, values: Vec<Value>) -> Result<Value> {
        let layout::Kind::Enum { ref variants, .. } = self.layout(ty)?.kind else {
            return Err(Error::Undefined("expected result enum"));
        };
        let definition = variants
            .iter()
            .find(|variant| {
                self.symbols
                    .get(self.program.hir.definitions[variant.definition].name)
                    == name
            })
            .ok_or(Error::Undefined("missing result variant"))?
            .definition;
        Ok(Value {
            ty,
            kind: ValueKind::Variant(definition, values),
        })
    }
    fn variant_field_type(&self, ty: TyId, name: &str, index: usize) -> Result<TyId> {
        let layout::Kind::Enum { ref variants, .. } = self.layout(ty)?.kind else {
            return Err(Error::Undefined("expected result enum"));
        };
        variants
            .iter()
            .find(|variant| {
                self.symbols
                    .get(self.program.hir.definitions[variant.definition].name)
                    == name
            })
            .and_then(|variant| variant.fields.get(index))
            .map(|field| field.ty)
            .ok_or(Error::Undefined("missing result payload"))
    }
}
