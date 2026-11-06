use super::*;

pub(super) struct Builder<'a> {
    core: &'a super::super::Body,
    paths: Paths,
    blocks: Vec<Block>,
    instructions: usize,
}
impl<'a> Builder<'a> {
    pub(super) fn new(core: &'a super::super::Body, glue: &mut Glues<'_>) -> Result<Self, Error> {
        let paths = Paths::build(core, glue)?;
        let blocks = core
            .blocks
            .iter()
            .enumerate()
            .map(|(index, _)| Block {
                instructions: Vec::new(),
                terminator: Terminator::Core {
                    source: CoreBlock(index as u32),
                    successors: Vec::new(),
                },
            })
            .collect();
        Ok(Self {
            core,
            paths,
            blocks,
            instructions: 0,
        })
    }
    pub(super) fn build(mut self) -> Result<Body, Error> {
        for (index, block) in self.core.blocks.iter().enumerate() {
            let source = CoreBlock(index as u32);
            let mut instructions = Instructions::default();
            for (statement, operation) in block.statements.iter().enumerate() {
                self.statement(source, statement as u32, &operation.kind, &mut instructions)?;
            }
            let terminator = self.terminator(source, &block.terminator, &mut instructions)?;
            self.charge_instructions(instructions.cost)?;
            self.blocks[index] = Block {
                instructions: instructions.values,
                terminator,
            };
        }
        Ok(Body {
            definition: self.core.definition,
            flags: self.paths.flags,
            blocks: self.blocks,
            entry: BlockId(self.core.entry.0),
        })
    }
    fn flags(
        &self,
        place: &Place,
        value: FlagValue,
        output: &mut Instructions,
    ) -> Result<(), Error> {
        let flags = self.paths.affected(place, value)?;
        if output.cost.saturating_add(flags.len()) > LIMIT {
            return Err(Error("drop instruction limit exceeded".into()));
        }
        for flag in flags {
            output.push(Instruction::SetFlag { flag, value })?;
        }
        self.recompute_ancestors(place, output)
    }
    fn recompute_ancestors(&self, place: &Place, output: &mut Instructions) -> Result<(), Error> {
        for owner in self.paths.ancestors(place)? {
            let all = owner
                .dependencies
                .clone()
                .map(|index| FlagId(index as u32))
                .collect();
            output.push(Instruction::RecomputeFlag {
                flag: owner.flag,
                all,
            })?;
        }
        Ok(())
    }
    fn deactivate_ancestors(&self, place: &Place, output: &mut Instructions) -> Result<(), Error> {
        for owner in self.paths.ancestors(place)? {
            output.push(Instruction::SetFlag {
                flag: owner.flag,
                value: FlagValue::Clear,
            })?;
        }
        Ok(())
    }
    fn consume(&self, value: &Operand, output: &mut Instructions) -> Result<(), Error> {
        if let Operand::Move(place) = value {
            self.paths.ensure_movable(place)?;
            self.flags(place, FlagValue::Clear, output)?;
        }
        Ok(())
    }
    fn rvalue(&self, value: &Rvalue, output: &mut Instructions) -> Result<(), Error> {
        visit_moves(value, &mut |place| {
            self.paths.ensure_movable(place)?;
            self.flags(place, FlagValue::Clear, output)
        })
    }
    fn statement(
        &self,
        source: CoreBlock,
        statement: u32,
        kind: &super::super::StatementKind,
        output: &mut Instructions,
    ) -> Result<(), Error> {
        use super::super::StatementKind as S;
        match kind {
            S::StorageLive(local) | S::StorageDead(local) => {
                self.flags(&Place::local(*local), FlagValue::Clear, output)?
            }
            S::Assign { value, .. } => self.rvalue(value, output)?,
            S::IteratorStart { value, .. } => self.consume(value, output)?,
            _ => {}
        }
        output.push(Instruction::CoreStatement { source, statement })?;
        match kind {
            S::Argument(local) => self.flags(&Place::local(*local), FlagValue::Set, output)?,
            S::IteratorStart { iterator, .. } => {
                self.flags(&Place::local(*iterator), FlagValue::Set, output)?
            }
            S::Assign { destination, value } if !matches!(value, Rvalue::AddressOf(_)) => {
                self.flags(destination, FlagValue::Set, output)?
            }
            _ => {}
        }
        Ok(())
    }
    fn push(
        &mut self,
        instructions: Vec<Instruction>,
        terminator: Terminator,
    ) -> Result<BlockId, Error> {
        if self.blocks.len() >= LIMIT {
            return Err(Error("drop elaboration block limit exceeded".into()));
        }
        self.charge_instructions(instructions.iter().map(instruction_cost).sum())?;
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Block {
            instructions,
            terminator,
        });
        Ok(id)
    }
    fn charge_instructions(&mut self, count: usize) -> Result<(), Error> {
        self.instructions = self.instructions.saturating_add(count);
        if self.instructions > LIMIT {
            return Err(Error("drop instruction limit exceeded".into()));
        }
        Ok(())
    }
    fn initialized_edge(
        &mut self,
        destination: &Place,
        target: CoreBlock,
    ) -> Result<BlockId, Error> {
        let mut instructions = Instructions::default();
        self.flags(destination, FlagValue::Set, &mut instructions)?;
        if instructions.values.is_empty() {
            return Ok(BlockId(target.0));
        }
        self.push(instructions.values, Terminator::Goto(BlockId(target.0)))
    }
    fn terminator(
        &mut self,
        source: CoreBlock,
        kind: &super::super::Terminator,
        output: &mut Instructions,
    ) -> Result<Terminator, Error> {
        use super::super::Terminator as T;
        let successors = match kind {
            T::Call { .. } | T::DynCall { .. } | T::Spawn { .. } => {
                self.call_edges(kind, output)?
            }
            T::TaskDrain { next, abort, .. } => vec![BlockId(next.0), BlockId(abort.0)],
            T::IteratorNext {
                destination,
                some,
                none,
                ..
            } => {
                vec![self.initialized_edge(destination, *some)?, BlockId(none.0)]
            }
            T::Checked {
                value,
                destination,
                normal,
                trap,
            } => {
                self.rvalue(value, output)?;
                vec![
                    self.initialized_edge(destination, *normal)?,
                    BlockId(trap.0),
                ]
            }
            T::Drop {
                place,
                next,
                unwind,
            } => {
                self.deactivate_ancestors(place, output)?;
                return Ok(Terminator::Goto(self.drop_chain(place, *next, *unwind)?));
            }
            T::Goto(target) => vec![BlockId(target.0)],
            T::Switch { condition, yes, no } => {
                self.consume(condition, output)?;
                vec![BlockId(yes.0), BlockId(no.0)]
            }
            T::Bounds { normal, trap, .. } => vec![BlockId(normal.0), BlockId(trap.0)],
            T::Return => {
                self.flags(
                    &Place::local(self.core.return_local),
                    FlagValue::Clear,
                    output,
                )?;
                Vec::new()
            }
            T::Resume(_) | T::Abort | T::Unreachable => Vec::new(),
        };
        Ok(Terminator::Core { source, successors })
    }
    fn call_edges(
        &mut self,
        kind: &super::super::Terminator,
        output: &mut Instructions,
    ) -> Result<Vec<BlockId>, Error> {
        use super::super::Terminator as T;
        let (receiver, arguments, destination, normal, panic, cancel) = match kind {
            T::Call {
                callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            }
            | T::DynCall {
                receiver: callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            }
            | T::Spawn {
                callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => (callee, arguments, destination, normal, panic, cancel),
            _ => unreachable!("call flag transfer requires a call terminator"),
        };
        self.consume(receiver, output)?;
        for value in arguments {
            self.consume(value, output)?;
        }
        Ok(vec![
            self.initialized_edge(destination, *normal)?,
            BlockId(panic.0),
            BlockId(cancel.0),
        ])
    }
    fn drop_chain(
        &mut self,
        place: &Place,
        next: CoreBlock,
        unwind: CoreBlock,
    ) -> Result<BlockId, Error> {
        let flags = self.paths.affected(place, FlagValue::Clear)?;
        let mut next = BlockId(next.0);
        for flag in flags.into_iter().rev() {
            next = self.drop_flag(flag, next, BlockId(unwind.0))?;
        }
        Ok(next)
    }

    fn drop_flag(
        &mut self,
        flag: FlagId,
        next: BlockId,
        unwind: BlockId,
    ) -> Result<BlockId, Error> {
        let owned = self.paths.flags[flag.0 as usize].clone();
        let call = if owned.kind == FlagKind::Initialization {
            Terminator::Goto(next)
        } else {
            Terminator::InvokeGlue {
                place: owned.place,
                glue: owned.glue,
                next,
                unwind,
            }
        };
        // Clear before invoking glue, including a fatal cleanup failure.
        let mut initialized = self.push(
            vec![Instruction::SetFlag {
                flag,
                value: FlagValue::Clear,
            }],
            call,
        )?;
        if !owned.guards.is_empty() {
            let skipped = self.push(
                vec![Instruction::SetFlag {
                    flag,
                    value: FlagValue::Clear,
                }],
                Terminator::Goto(next),
            )?;
            for guard in owned.guards.into_iter().rev() {
                initialized = self.push(
                    Vec::new(),
                    Terminator::TestVariant {
                        place: guard.place,
                        variant: guard.variant,
                        matches: initialized,
                        otherwise: skipped,
                    },
                )?;
            }
        }
        self.push(
            Vec::new(),
            Terminator::TestFlag {
                flag,
                initialized,
                clear: next,
            },
        )
    }
}

#[derive(Default)]
struct Instructions {
    values: Vec<Instruction>,
    cost: usize,
}
impl Instructions {
    fn push(&mut self, instruction: Instruction) -> Result<(), Error> {
        self.cost = self
            .cost
            .checked_add(instruction_cost(&instruction))
            .filter(|cost| *cost <= LIMIT)
            .ok_or_else(|| Error("drop instruction work limit exceeded".into()))?;
        self.values.push(instruction);
        Ok(())
    }
}
fn instruction_cost(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::RecomputeFlag { all, .. } => all.len().saturating_add(1),
        _ => 1,
    }
}
