use super::*;
use mir::drop as cleanup;

pub(super) struct Emitter<'m, 'p> {
    pub module: &'m mut Module<'p>,
    pub core: &'p mir::Body,
    pub cleanup: &'p cleanup::Body,
    pub ir: ir::Writer,
}

impl<'m, 'p> Emitter<'m, 'p> {
    pub fn function(
        module: &'m mut Module<'p>,
        core: &'p mir::Body,
        cleanup: &'p cleanup::Body,
    ) -> Result<(), Error> {
        let mut emitter = Self {
            module,
            core,
            cleanup,
            ir: ir::Writer::new(),
        };
        emitter.header()?;
        let header = std::mem::take(&mut emitter.ir.text);
        for (index, block) in cleanup.blocks.iter().enumerate() {
            emitter.ir.start(&format!("b{index}"));
            for instruction in &block.instructions {
                emitter.instruction(instruction)?;
            }
            emitter.cleanup_exit(&block.terminator)?;
            emitter.module.budget()?;
        }
        emitter.module.output.push_str(&header);
        emitter.module.output.push_str(&emitter.ir.allocations);
        let _ = writeln!(emitter.module.output, "  br label %b{}", cleanup.entry.0);
        emitter.module.output.push_str(&emitter.ir.text);
        emitter.module.output.push_str("}\n\n");
        Ok(())
    }

    fn header(&mut self) -> Result<(), Error> {
        let parameters: Vec<_> = self
            .core
            .locals
            .iter()
            .enumerate()
            .filter(|(_, local)| local.kind == mir::LocalKind::Parameter)
            .map(|(index, _)| format!("ptr %a{index}"))
            .collect();
        let parameters = if parameters.is_empty() {
            String::new()
        } else {
            format!(", {}", parameters.join(", "))
        };
        let _ = writeln!(
            self.ir.text,
            "define i32 {}(ptr %context, ptr %out{parameters}) #0 {{\nentry:",
            self.module.function(self.core.definition)
        );
        for (index, local) in self.core.locals.iter().enumerate() {
            if local.kind == mir::LocalKind::TaskRegistry {
                return Err(self.scope_error());
            }
            let (size, align) = self.storage(local)?;
            self.ir.line(format!(
                "%l{index} = alloca [{} x i8], align {align}",
                size.max(1)
            ));
        }
        for index in 0..self.cleanup.flags.len() {
            self.ir.line(format!("%flag{index} = alloca i1, align 1"));
            self.ir
                .line(format!("store i1 false, ptr %flag{index}, align 1"));
        }
        Ok(())
    }

    fn storage(&self, local: &mir::Local) -> Result<(u64, u64), Error> {
        if local.kind == mir::LocalKind::Address {
            let wide = matches!(
                self.module.program.hir.types.get(local.ty),
                Ty::Slice(_) | Ty::Str | Ty::Dynamic { .. }
            );
            return Ok((if wide { 16 } else { 8 }, 8));
        }
        let layout = self.module.layout(local.ty)?;
        let size = if local.kind == mir::LocalKind::ArrayIterator {
            iterator_cursor(layout.size)
                .checked_add(8)
                .ok_or_else(|| self.error("iterator storage size overflow"))?
        } else {
            layout.size
        };
        Ok((
            size,
            layout
                .alignment
                .max(if local.kind == mir::LocalKind::ArrayIterator {
                    8
                } else {
                    1
                }),
        ))
    }

    fn instruction(&mut self, instruction: &cleanup::Instruction) -> Result<(), Error> {
        match instruction {
            cleanup::Instruction::CoreStatement { source, statement } => {
                let statement = &self.core.blocks[*source].statements[*statement as usize];
                self.statement(&statement.kind)
            }
            cleanup::Instruction::SetFlag { flag, value } => {
                self.ir.line(format!(
                    "store i1 {}, ptr %flag{}, align 1",
                    matches!(value, cleanup::FlagValue::Set),
                    flag.0
                ));
                Ok(())
            }
            cleanup::Instruction::RecomputeFlag { flag, all } => {
                let mut initialized = "true".into();
                for item in all {
                    let value = self
                        .ir
                        .temp(format!("load i1, ptr %flag{}, align 1", item.0));
                    initialized = self.ir.temp(format!("and i1 {initialized}, {value}"));
                }
                self.ir.line(format!(
                    "store i1 {initialized}, ptr %flag{}, align 1",
                    flag.0
                ));
                Ok(())
            }
        }
    }

    fn statement(&mut self, statement: &mir::StatementKind) -> Result<(), Error> {
        match statement {
            mir::StatementKind::Assign { destination, value } => {
                if let mir::Rvalue::AddressOf(place) = value {
                    let address = self.address(place)?;
                    self.ir.line(format!(
                        "store ptr {}, ptr %l{}, align 1",
                        address.pointer, destination.local.0
                    ));
                    if let Some(metadata) = address.metadata {
                        let slot = self.ir.offset(&format!("%l{}", destination.local.0), 8);
                        self.ir
                            .line(format!("store i64 {metadata}, ptr {slot}, align 1"));
                    }
                    return Ok(());
                }
                let destination = self.address(destination)?;
                self.value(&destination, value)
            }
            mir::StatementKind::Argument(local) => {
                let destination = format!("%l{}", local.0);
                self.copy(
                    &destination,
                    &format!("%a{}", local.0),
                    self.module.layout(self.core.locals[*local].ty)?.size,
                )
            }
            mir::StatementKind::IteratorStart { iterator, value } => {
                let ty = self.core.locals[*iterator].ty;
                self.copy_operand(&format!("%l{}", iterator.0), value, ty)?;
                let cursor = self.ir.offset(
                    &format!("%l{}", iterator.0),
                    iterator_cursor(self.module.layout(ty)?.size),
                );
                self.ir.line(format!("store i64 0, ptr {cursor}, align 1"));
                Ok(())
            }
            mir::StatementKind::RegistryStart(_) => Err(self.scope_error()),
            mir::StatementKind::Contract(_)
            | mir::StatementKind::EnterScope(_)
            | mir::StatementKind::ExitScope(_)
            | mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_) => Ok(()),
        }
    }

    pub fn error(&self, message: impl Into<String>) -> Error {
        problem(self.core.blocks[0].span, message)
    }
    pub fn scope_error(&self) -> Error {
        Error { code:"E-RUNTIME-SCOPE-DRAIN",span:self.core.blocks[0].span,message:"LLAM 3.0.0 has no cancellation-immune managed group drain; scoped task code cannot release borrowed storage through its host-only drain API".into() }
    }
    pub fn copy(&mut self, destination: &str, source: &str, bytes: u64) -> Result<(), Error> {
        if bytes == 0 {
            return Ok(());
        }
        self.module.declare(
            "llvm.memmove.p0.p0.i64",
            "declare void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1 immarg)".into(),
        )?;
        self.ir.line(format!("call void @llvm.memmove.p0.p0.i64(ptr {destination}, ptr {source}, i64 {bytes}, i1 false)"));
        Ok(())
    }
}

pub(super) fn iterator_cursor(bytes: u64) -> u64 {
    (bytes + 7) & !7
}
