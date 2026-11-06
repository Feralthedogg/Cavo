use super::{
    body::{Emitter, iterator_cursor},
    *,
};

impl Emitter<'_, '_> {
    pub fn core_exit(
        &mut self,
        source: mir::BlockId,
        targets: &[mir::drop::BlockId],
    ) -> Result<(), Error> {
        let labels = targets
            .iter()
            .map(|target| format!("b{}", target.0))
            .collect::<Vec<_>>();
        match &self.core.blocks[source].terminator {
            mir::Terminator::Goto(_) => self.ir.line(format!("br label %{}", labels[0])),
            mir::Terminator::Switch { condition, .. } => {
                let (_, value) = self.scalar(condition)?;
                let test = self.ir.temp(format!("icmp ne i8 {value}, 0"));
                self.ir.line(format!(
                    "br i1 {test}, label %{}, label %{}",
                    labels[0], labels[1]
                ));
            }
            mir::Terminator::Checked {
                value, destination, ..
            } => self.checked(value, destination, &labels[0], &labels[1])?,
            mir::Terminator::Bounds { base, index, .. } => self.bounds(base, *index, &labels)?,
            mir::Terminator::Call { .. } | mir::Terminator::DynCall { .. } => {
                self.call(&self.core.blocks[source].terminator, &labels)?
            }
            mir::Terminator::IteratorNext {
                iterator,
                destination,
                ..
            } => self.iterator_next(*iterator, destination, &labels)?,
            mir::Terminator::Return => {
                self.copy(
                    "%out",
                    &format!("%l{}", self.core.return_local.0),
                    self.module.layout(self.core.result)?.size,
                )?;
                self.ir.line("ret i32 0".into());
            }
            mir::Terminator::Resume(kind) => self.ir.line(format!(
                "ret i32 {}",
                if *kind == mir::ExitKind::Panic { 1 } else { 2 }
            )),
            mir::Terminator::Abort => self.abort()?,
            mir::Terminator::Unreachable => self.ir.line("unreachable".into()),
            mir::Terminator::Spawn { .. } | mir::Terminator::TaskDrain { .. } => {
                return Err(self.scope_error());
            }
            mir::Terminator::Drop { .. } => {
                return Err(self.error("unelaborated drop reached native code generation"));
            }
        }
        Ok(())
    }

    fn bounds(
        &mut self,
        base: &mir::Place,
        index: mir::LocalId,
        labels: &[String],
    ) -> Result<(), Error> {
        let length = self.length(base)?;
        let (ty, index) = self.scalar(&mir::Operand::Copy(mir::Place::local(index)))?;
        let index = self.integer_to_i64(ty, index)?;
        let valid = self.ir.temp(format!("icmp ult i64 {index}, {length}"));
        self.ir.line(format!(
            "br i1 {valid}, label %{}, label %{}",
            labels[0], labels[1]
        ));
        Ok(())
    }

    fn iterator_next(
        &mut self,
        iterator: mir::LocalId,
        destination: &mir::Place,
        labels: &[String],
    ) -> Result<(), Error> {
        let ty = self.core.locals[iterator].ty;
        let layout = self.module.layout(ty)?;
        let layout::Kind::Array {
            element,
            count,
            stride,
        } = layout.kind
        else {
            return Err(self.error("owned iterator has no concrete array layout"));
        };
        let cursor = self
            .ir
            .offset(&format!("%l{}", iterator.0), iterator_cursor(layout.size));
        let index = self.ir.temp(format!("load i64, ptr {cursor}, align 1"));
        let present = self.ir.temp(format!("icmp ult i64 {index}, {count}"));
        let take = self.ir.fresh("iterator_take");
        self.ir.line(format!(
            "br i1 {present}, label %{take}, label %{}",
            labels[1]
        ));
        self.ir.start(&take);
        let bytes = self.ir.temp(format!("mul i64 {index}, {stride}"));
        let pointer = self.ir.temp(format!(
            "getelementptr i8, ptr %l{}, i64 {bytes}",
            iterator.0
        ));
        let destination = self.address(destination)?;
        self.copy(
            &destination.pointer,
            &pointer,
            self.module.layout(element)?.size,
        )?;
        let next = self.ir.temp(format!("add i64 {index}, 1"));
        self.ir
            .line(format!("store i64 {next}, ptr {cursor}, align 1"));
        self.ir.line(format!("br label %{}", labels[0]));
        Ok(())
    }

    fn call(&mut self, terminator: &mir::Terminator, labels: &[String]) -> Result<(), Error> {
        let mir::Terminator::Call {
            callee,
            arguments,
            parameter_types,
            destination,
            ..
        } = terminator
        else {
            return self.dynamic_call(terminator, labels);
        };
        if let mir::Operand::Function { definition, .. } = callee {
            if let Some(&role) = self.module.program.hir.contracts.intrinsics.get(definition) {
                return self.intrinsic(role, arguments, destination, labels);
            }
            if self.module.program.hir.definitions[*definition]
                .foreign_abi
                .is_some()
            {
                return self.foreign_call(*definition, arguments, destination, labels);
            }
            if !self
                .module
                .program
                .mir
                .functions
                .iter()
                .any(|body| body.definition == *definition)
            {
                return Err(self.error("this declaration has no linked native implementation; rebuild the package source graph instead of an interface-only capsule"));
            }
        }
        let (_, callee) = self.scalar(callee)?;
        let slots = self.argument_slots(arguments, parameter_types)?;
        let destination = self.address(destination)?;
        self.invoke(&callee, &destination.pointer, &slots, labels)
    }

    pub fn argument_slots(
        &mut self,
        arguments: &[mir::Operand],
        types: &[TyId],
    ) -> Result<Vec<String>, Error> {
        arguments
            .iter()
            .zip(types)
            .map(|(argument, &ty)| {
                let layout = self.module.layout(ty)?;
                let (bytes, alignment) = (layout.size, layout.alignment);
                let slot = self.ir.alloca(bytes, alignment);
                self.copy_operand(&slot, argument, ty)?;
                Ok(slot)
            })
            .collect()
    }

    pub fn invoke(
        &mut self,
        callee: &str,
        destination: &str,
        arguments: &[String],
        labels: &[String],
    ) -> Result<(), Error> {
        let arguments = arguments
            .iter()
            .map(|argument| format!(", ptr {argument}"))
            .collect::<String>();
        let status = self.ir.temp(format!(
            "call i32 {callee}(ptr %context, ptr {destination}{arguments})"
        ));
        self.status(&status, labels)
    }

    pub fn status(&mut self, status: &str, labels: &[String]) -> Result<(), Error> {
        if labels.len() != 3 {
            return Err(self.error("native call has incomplete normal, panic or cancel successors"));
        }
        let bad = self.ir.fresh("invalid_status");
        self.ir.line(format!("switch i32 {status}, label %{bad} [i32 0, label %{} i32 1, label %{} i32 2, label %{}]",labels[0],labels[1],labels[2]));
        self.ir.start(&bad);
        self.abort()
    }

    fn foreign_call(
        &mut self,
        definition: hir::DefId,
        arguments: &[mir::Operand],
        destination: &mir::Place,
        labels: &[String],
    ) -> Result<(), Error> {
        let declaration = &self.module.program.hir.definitions[definition];
        if declaration.foreign_abi.as_deref() != Some("C") {
            return Err(self.error("native FFI currently requires an explicit C ABI"));
        }
        let Ty::Function { result, .. } = self.module.program.hir.types.get(declaration.ty) else {
            return Err(self.error("foreign declaration is not callable"));
        };
        let result = *result;
        let name = self.module.function(definition);
        let mut values = Vec::new();
        let mut signature = Vec::new();
        for argument in arguments {
            let (ty, value) = self.scalar(argument)?;
            let llvm = self.module.scalar_type(ty)?;
            values.push(format!("{llvm} {value}"));
            signature.push(llvm);
        }
        let output = if result == TyId::VOID {
            "void".into()
        } else {
            self.module.scalar_type(result)?
        };
        self.module.declare(
            &name,
            format!("declare {output} {name}({})", signature.join(", ")),
        )?;
        let call = format!("call {output} {name}({})", values.join(", "));
        if result == TyId::VOID {
            self.ir.line(call);
        } else {
            let value = self.ir.temp(call);
            let destination = self.address(destination)?;
            self.store_scalar(&destination.pointer, result, &value)?;
        }
        self.ir.line(format!("br label %{}", labels[0]));
        Ok(())
    }

    fn dynamic_call(
        &mut self,
        terminator: &mir::Terminator,
        labels: &[String],
    ) -> Result<(), Error> {
        let mir::Terminator::DynCall {
            receiver,
            trait_method,
            arguments,
            parameter_types,
            destination,
            ..
        } = terminator
        else {
            unreachable!("dynamic call");
        };
        let receiver = match receiver {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.address(place)?,
            _ => return Err(self.error("dynamic receiver has no native storage")),
        };
        let slot = self
            .module
            .program
            .hir
            .traits
            .iter()
            .find_map(|trait_| {
                trait_
                    .methods
                    .iter()
                    .position(|method| method.definition == *trait_method)
            })
            .ok_or_else(|| self.error("dynamic method has no vtable position"))?;
        let data = self
            .ir
            .temp(format!("load ptr, ptr {}, align 1", receiver.pointer));
        let metadata = self.ir.offset(&receiver.pointer, 8);
        let table = self.ir.temp(format!("load ptr, ptr {metadata}, align 1"));
        let pointer = self.ir.offset(&table, slot as u64 * 8);
        let callee = self.ir.temp(format!("load ptr, ptr {pointer}, align 1"));
        let concrete = self.ir.alloca(8, 8);
        self.ir
            .line(format!("store ptr {data}, ptr {concrete}, align 1"));
        let mut slots = vec![concrete];
        slots.extend(self.argument_slots(arguments, parameter_types)?);
        let destination = self.address(destination)?;
        self.invoke(&callee, &destination.pointer, &slots, labels)
    }

    pub fn abort(&mut self) -> Result<(), Error> {
        self.module.runtime_import(
            "cavo_rt_abort",
            "declare void @cavo_rt_abort() cold noreturn nounwind",
        )?;
        self.ir.line("call void @cavo_rt_abort()".into());
        self.ir.line("unreachable".into());
        Ok(())
    }
}
