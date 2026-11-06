use super::{body::Emitter, place::Address, *};

impl Emitter<'_, '_> {
    pub fn scalar(&mut self, operand: &mir::Operand) -> Result<(TyId, String), Error> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let address = self.address(place)?;
                let ty = self.module.scalar_type(address.ty)?;
                Ok((
                    address.ty,
                    self.ir
                        .temp(format!("load {ty}, ptr {}, align 1", address.pointer)),
                ))
            }
            mir::Operand::Function { definition, ty } => {
                Ok((*ty, self.module.function(*definition)))
            }
            mir::Operand::Constant { value, ty } => Ok((*ty, self.constant(value, *ty)?)),
            mir::Operand::ConstTerm { value, ty } => {
                let value = self
                    .module
                    .program
                    .hir
                    .types
                    .const_usize(*value)
                    .ok_or_else(|| self.error("native constant is not concrete"))?;
                Ok((*ty, value.to_string()))
            }
            mir::Operand::Unit => Err(self.error("unit is not a scalar LLVM operand")),
        }
    }

    fn constant(&self, value: &hir::Constant, ty: TyId) -> Result<String, Error> {
        Ok(match value {
            hir::Constant::Integer {
                magnitude,
                negative,
            } => format!("{}{magnitude}", if *negative { "-" } else { "" }),
            hir::Constant::Bool(value) => u8::from(*value).to_string(),
            hir::Constant::Char(value) => u32::from(*value).to_string(),
            hir::Constant::Float(value) => {
                let value = if matches!(
                    self.module.program.hir.types.get(ty),
                    Ty::Float { bits: 32 }
                ) {
                    f64::from(*value as f32)
                } else {
                    *value
                };
                format!("0x{:016X}", value.to_bits())
            }
            _ => return Err(self.error("aggregate literal needs native storage")),
        })
    }

    pub fn copy_operand(
        &mut self,
        destination: &str,
        operand: &mir::Operand,
        ty: TyId,
    ) -> Result<(), Error> {
        if ty == TyId::VOID {
            return Ok(());
        }
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let source = self.address(place)?;
                self.copy(destination, &source.pointer, self.module.layout(ty)?.size)
            }
            mir::Operand::Constant {
                value: hir::Constant::String(value),
                ..
            } => {
                let bytes = value.as_bytes().to_vec();
                let next = self.module.strings.len();
                let name = self
                    .module
                    .strings
                    .entry(bytes)
                    .or_insert_with(|| format!("@__cavo_string_{next}"))
                    .clone();
                self.ir
                    .line(format!("store ptr {name}, ptr {destination}, align 1"));
                let length = self.ir.offset(destination, 8);
                self.ir
                    .line(format!("store i64 {}, ptr {length}, align 1", value.len()));
                Ok(())
            }
            _ => {
                let (_, value) = self.scalar(operand)?;
                self.store_scalar(destination, ty, &value)
            }
        }
    }

    pub fn store_scalar(&mut self, destination: &str, ty: TyId, value: &str) -> Result<(), Error> {
        let ty = self.module.scalar_type(ty)?;
        self.ir
            .line(format!("store {ty} {value}, ptr {destination}, align 1"));
        Ok(())
    }

    pub fn value(&mut self, destination: &Address, value: &mir::Rvalue) -> Result<(), Error> {
        match value {
            mir::Rvalue::Use(value) => {
                self.copy_operand(&destination.pointer, value, destination.ty)
            }
            mir::Rvalue::Binary { op, left, right } => {
                let (_, result) = self.binary(*op, left, right)?;
                self.store_scalar(&destination.pointer, destination.ty, &result)
            }
            mir::Rvalue::Unary { op, operand } => {
                let (_, result) = self.unary(*op, operand)?;
                self.store_scalar(&destination.pointer, destination.ty, &result)
            }
            mir::Rvalue::Borrow { place, .. } => self.borrow(destination, place),
            mir::Rvalue::IsVariant { place, variant } => {
                let test = self.tag(place, *variant)?;
                let value = self.ir.temp(format!("zext i1 {test} to i8"));
                self.store_scalar(&destination.pointer, destination.ty, &value)
            }
            mir::Rvalue::Record { fields, .. } => self.record(destination, None, fields),
            mir::Rvalue::Variant { definition, fields } => {
                self.variant(destination, *definition, fields)
            }
            mir::Rvalue::Array(values) => self.array(destination, values),
            mir::Rvalue::Repeat { value, count } => self.repeat(destination, value, *count),
            mir::Rvalue::RepeatConst { value, count } => {
                let count = self
                    .module
                    .program
                    .hir
                    .types
                    .const_usize(*count)
                    .ok_or_else(|| self.error("native repeat count is not concrete"))?;
                self.repeat(destination, value, count)
            }
            mir::Rvalue::Length(place) => {
                let length = self.length(place)?;
                self.store_scalar(&destination.pointer, destination.ty, &length)
            }
            mir::Rvalue::ArrayToSlice(value) => self.slice(destination, value),
            mir::Rvalue::DynCoerce { value, vtable } => self.dynamic(destination, value, *vtable),
            mir::Rvalue::AddressOf(_) => {
                Err(self.error("address capture is not an ordinary native value"))
            }
        }
    }

    fn borrow(&mut self, destination: &Address, place: &mir::Place) -> Result<(), Error> {
        let source = self.address(place)?;
        self.ir.line(format!(
            "store ptr {}, ptr {}, align 1",
            source.pointer, destination.pointer
        ));
        if matches!(
            self.module.layout(destination.ty)?.kind,
            layout::Kind::Pointer { words: 2 }
        ) {
            let metadata = source
                .metadata
                .ok_or_else(|| self.error("unsized borrow has no length or vtable"))?;
            let slot = self.ir.offset(&destination.pointer, 8);
            self.ir
                .line(format!("store i64 {metadata}, ptr {slot}, align 1"));
        }
        Ok(())
    }

    fn record(
        &mut self,
        destination: &Address,
        variant: Option<hir::DefId>,
        fields: &[(u32, mir::Operand)],
    ) -> Result<(), Error> {
        for (index, value) in fields {
            let field = self.field(destination.ty, variant, *index)?;
            let slot = self.ir.offset(&destination.pointer, field.offset);
            self.copy_operand(&slot, value, field.ty)?;
        }
        Ok(())
    }

    fn variant(
        &mut self,
        destination: &Address,
        variant: hir::DefId,
        fields: &[mir::Operand],
    ) -> Result<(), Error> {
        let layout::Kind::Enum {
            tag_bytes,
            variants,
            ..
        } = &self.module.layout(destination.ty)?.kind
        else {
            return Err(self.error("native variant has no enum layout"));
        };
        let discriminant = variants
            .iter()
            .find(|item| item.definition == variant)
            .ok_or_else(|| self.error("variant layout is missing"))?
            .discriminant;
        self.ir.line(format!(
            "store i{} {discriminant}, ptr {}, align 1",
            u32::from(*tag_bytes) * 8,
            destination.pointer
        ));
        let fields = fields
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, value)| (index as u32, value))
            .collect::<Vec<_>>();
        self.record(destination, Some(variant), &fields)
    }

    fn array(&mut self, destination: &Address, values: &[mir::Operand]) -> Result<(), Error> {
        let layout::Kind::Array {
            element, stride, ..
        } = self.module.layout(destination.ty)?.kind
        else {
            return Err(self.error("native array has no array layout"));
        };
        for (index, value) in values.iter().enumerate() {
            let slot = self.ir.offset(&destination.pointer, index as u64 * stride);
            self.copy_operand(&slot, value, element)?;
        }
        Ok(())
    }

    fn repeat(
        &mut self,
        destination: &Address,
        value: &mir::Operand,
        count: u64,
    ) -> Result<(), Error> {
        if count == 0 {
            return Ok(());
        }
        let layout::Kind::Array {
            element, stride, ..
        } = self.module.layout(destination.ty)?.kind
        else {
            return Err(self.error("native repeat has no array layout"));
        };
        let predecessor = self.ir.label.clone();
        let body = self.ir.fresh("repeat");
        let done = self.ir.fresh("repeat_done");
        let index = self.ir.fresh("repeat_index");
        let next = self.ir.fresh("repeat_next");
        self.ir.line(format!("br label %{body}"));
        self.ir.start(&body);
        self.ir.line(format!(
            "%{index} = phi i64 [0, %{predecessor}], [%{next}, %{body}]"
        ));
        let bytes = self.ir.temp(format!("mul i64 %{index}, {stride}"));
        let slot = self.ir.temp(format!(
            "getelementptr i8, ptr {}, i64 {bytes}",
            destination.pointer
        ));
        self.copy_operand(&slot, value, element)?;
        self.ir.line(format!("%{next} = add i64 %{index}, 1"));
        let again = self.ir.temp(format!("icmp ult i64 %{next}, {count}"));
        self.ir
            .line(format!("br i1 {again}, label %{body}, label %{done}"));
        self.ir.start(&done);
        Ok(())
    }

    pub fn length(&mut self, place: &mir::Place) -> Result<String, Error> {
        let mut address = self.address(place)?;
        while matches!(
            self.module.program.hir.types.get(address.ty),
            Ty::Reference { .. }
        ) {
            address = self.dereference(address)?;
        }
        if let Ty::Array { length, .. } = self.module.program.hir.types.get(address.ty) {
            return Ok(length.to_string());
        }
        address
            .metadata
            .ok_or_else(|| self.error("native length has no slice metadata"))
    }

    fn slice(&mut self, destination: &Address, value: &mir::Operand) -> Result<(), Error> {
        let (ty, pointer) = self.scalar(value)?;
        let Ty::Reference { inner, .. } = self.module.program.hir.types.get(ty) else {
            return Err(self.error("slice coercion needs an array reference"));
        };
        let Ty::Array { length, .. } = self.module.program.hir.types.get(*inner) else {
            return Err(self.error("slice coercion lost its array length"));
        };
        let length = *length;
        self.ir.line(format!(
            "store ptr {pointer}, ptr {}, align 1",
            destination.pointer
        ));
        let slot = self.ir.offset(&destination.pointer, 8);
        self.ir
            .line(format!("store i64 {length}, ptr {slot}, align 1"));
        Ok(())
    }

    fn dynamic(
        &mut self,
        destination: &Address,
        value: &mir::Operand,
        vtable: u32,
    ) -> Result<(), Error> {
        let (_, data) = self.scalar(value)?;
        self.ir.line(format!(
            "store ptr {data}, ptr {}, align 1",
            destination.pointer
        ));
        let slot = self.ir.offset(&destination.pointer, 8);
        self.ir.line(format!(
            "store ptr @__cavo_vtable_{vtable}, ptr {slot}, align 1"
        ));
        Ok(())
    }
}
