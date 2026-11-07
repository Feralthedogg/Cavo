use super::*;
use memory::Atom;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Metadata {
    Length(u64),
    Vtable(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Value {
    pub ty: TyId,
    pub kind: ValueKind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueKind {
    Unit,
    Bits(u128),
    FloatBits(u64),
    Pointer {
        data: Option<Pointer>,
        metadata: Option<Metadata>,
    },
    Function(hir::DefId),
    Fields(Vec<Value>),
    Variant(hir::DefId, Vec<Value>),
    Union(u32, Box<Value>),
    Task(usize),
}

impl Value {
    pub(super) fn node_count(&self, limit: usize) -> Result<usize> {
        let mut pending = vec![self];
        let mut count = 0usize;
        while let Some(value) = pending.pop() {
            count += 1;
            if count > limit {
                return Err(Error::Limit("logical value budget"));
            }
            match &value.kind {
                ValueKind::Fields(fields) | ValueKind::Variant(_, fields) => pending.extend(fields),
                ValueKind::Union(_, value) => pending.push(value),
                _ => {}
            }
        }
        Ok(count)
    }
    pub fn fields(&self) -> Result<&[Value]> {
        match &self.kind {
            ValueKind::Fields(fields) => Ok(fields),
            _ => Err(Error::Undefined("invalid aggregate value")),
        }
    }

    pub fn integer(ty: TyId, value: i128) -> Self {
        Self {
            ty,
            kind: ValueKind::Bits(value as u128),
        }
    }
    pub fn bits(ty: TyId, value: u128) -> Self {
        Self {
            ty,
            kind: ValueKind::Bits(value),
        }
    }
    pub fn boolean(value: bool) -> Self {
        Self::bits(TyId::BOOL, value.into())
    }
    pub fn unit() -> Self {
        Self {
            ty: TyId::VOID,
            kind: ValueKind::Unit,
        }
    }
    pub fn pointer(ty: TyId, data: Pointer, metadata: Option<Metadata>) -> Self {
        Self {
            ty,
            kind: ValueKind::Pointer {
                data: Some(data),
                metadata,
            },
        }
    }
    pub fn unsigned(&self) -> Result<u128> {
        match self.kind {
            ValueKind::Bits(value) => Ok(value),
            _ => Err(Error::Undefined("expected integer value")),
        }
    }
    pub fn boolean_value(&self) -> Result<bool> {
        match self.kind {
            ValueKind::Bits(0) => Ok(false),
            ValueKind::Bits(1) => Ok(true),
            _ => Err(Error::Undefined("invalid bool bit pattern")),
        }
    }
    pub fn address(&self) -> Result<Pointer> {
        match &self.kind {
            ValueKind::Pointer {
                data: Some(pointer),
                ..
            } => Ok(pointer.clone()),
            _ => Err(Error::Undefined("null or non-pointer dereference")),
        }
    }
}

impl Machine<'_> {
    pub fn cell(&mut self, value: Value) -> Result<Value> {
        let size = self.layout(value.ty)?.size;
        let pointer = self.memory.stack(size)?;
        self.write(
            &Address {
                pointer: pointer.clone(),
                ty: value.ty,
                metadata: None,
                variant: None,
            },
            &value,
        )?;
        // Fixture callers choose the actual reference type from the signature.
        Ok(Value::pointer(value.ty, pointer, None))
    }

    pub fn load(&mut self, pointer: &Pointer, ty: TyId) -> Result<Value> {
        self.read(&Address {
            pointer: pointer.clone(),
            ty,
            metadata: None,
            variant: None,
        })
    }

    pub(super) fn read(&mut self, address: &Address) -> Result<Value> {
        self.tick()?;
        for &(offset, nominal, field) in &address.pointer.unions {
            if self
                .unions
                .get(&(address.pointer.allocation, offset, nominal))
                != Some(&field)
            {
                return Err(Error::Undefined("read of inactive union field"));
            }
        }
        let program = self.program;
        let layout = program
            .layouts
            .get(address.ty)
            .ok_or(Error::Unsupported("read of unsized storage"))?;
        if cavo_compiler::tasks::task_arguments(&program.hir, address.ty).is_some() {
            return Ok(Value {
                ty: address.ty,
                kind: ValueKind::Task(self.memory.task(&address.pointer)?),
            });
        }
        let kind = match &layout.kind {
            layout::Kind::Scalar => self.read_scalar(address, layout.size)?,
            layout::Kind::Pointer { words } => self.read_pointer(address, *words)?,
            layout::Kind::Record { fields, .. } => {
                ValueKind::Fields(self.read_fields(address, fields, 0)?)
            }
            layout::Kind::Union { fields } => self.read_union(address, fields)?,
            layout::Kind::Array {
                element,
                count,
                stride,
            } => self.read_array(address, *element, *count, *stride)?,
            layout::Kind::Enum {
                tag_bytes,
                payload_offset,
                variants,
            } => {
                let tag = self.read_word(&address.pointer, *tag_bytes as u64)?;
                let variant = variants
                    .iter()
                    .find(|variant| variant.discriminant as u128 == tag)
                    .ok_or(Error::Undefined("invalid enum bit pattern"))?;
                let fields = self.read_fields(address, &variant.fields, *payload_offset)?;
                ValueKind::Variant(variant.definition, fields)
            }
        };
        if layout.size == 0 && !self.memory.zero_initialized(&address.pointer)? {
            return Err(Error::Undefined("uninitialized or moved zero-sized value"));
        }
        Ok(Value {
            ty: address.ty,
            kind,
        })
    }

    fn read_union(&mut self, address: &Address, fields: &[layout::Field]) -> Result<ValueKind> {
        let Ty::Named { definition, .. } = self.program.hir.types.get(address.ty) else {
            return Err(Error::Undefined("invalid union identity"));
        };
        let index = *self
            .unions
            .get(&(
                address.pointer.allocation,
                address.pointer.offset,
                *definition,
            ))
            .ok_or(Error::Undefined("uninitialized union"))?;
        let field = fields
            .iter()
            .find(|field| field.index == index)
            .ok_or(Error::Undefined("invalid union field"))?;
        let pointer = self
            .memory
            .child(&address.pointer, field.offset, index.into())?;
        let value = self.read(&Address {
            pointer,
            ty: field.ty,
            metadata: None,
            variant: None,
        })?;
        Ok(ValueKind::Union(index, Box::new(value)))
    }

    fn read_scalar(&self, address: &Address, size: u64) -> Result<ValueKind> {
        if address.ty == TyId::VOID {
            return Ok(ValueKind::Unit);
        }
        let bits = self.read_word(&address.pointer, size)?;
        match self.program.hir.types.get(address.ty) {
            Ty::Bool if bits > 1 => Err(Error::Undefined("invalid bool bit pattern")),
            Ty::Char if char::from_u32(bits as u32).is_none() => {
                Err(Error::Undefined("invalid char bit pattern"))
            }
            Ty::Float { .. } => Ok(ValueKind::FloatBits(bits as u64)),
            _ => Ok(ValueKind::Bits(bits)),
        }
    }

    fn read_pointer(&self, address: &Address, words: u8) -> Result<ValueKind> {
        match self.memory.atom(&address.pointer)? {
            Atom::Function(definition) => Ok(ValueKind::Function(*definition)),
            Atom::Pointer(data) => {
                let metadata = if words == 2 {
                    let slot = self.memory.offset(&address.pointer, 8)?;
                    let Atom::Metadata(metadata) = self.memory.atom(&slot)? else {
                        return Err(Error::Undefined("invalid fat-pointer metadata"));
                    };
                    Some(*metadata)
                } else {
                    None
                };
                if let Ty::Reference { inner, .. } = self.program.hir.types.get(address.ty) {
                    let data = data.as_ref().ok_or(Error::Undefined("null reference"))?;
                    let (size, alignment) = self.referent_layout(*inner, metadata)?;
                    self.memory.check(data, size, alignment)?;
                }
                Ok(ValueKind::Pointer {
                    data: data.clone(),
                    metadata,
                })
            }
            _ => Err(Error::Undefined("invalid pointer bit pattern")),
        }
    }

    pub(super) fn referent_layout(
        &self,
        ty: TyId,
        metadata: Option<Metadata>,
    ) -> Result<(u64, u64)> {
        match self.program.hir.types.get(ty) {
            Ty::Str => match metadata {
                Some(Metadata::Length(n)) => Ok((n, 1)),
                _ => Err(Error::Undefined("invalid str metadata")),
            },
            Ty::Slice(inner) => {
                let Some(Metadata::Length(n)) = metadata else {
                    return Err(Error::Undefined("invalid slice metadata"));
                };
                let layout = self.layout(*inner)?;
                Ok((
                    layout
                        .size
                        .checked_mul(n)
                        .ok_or(Error::Undefined("slice byte range overflow"))?,
                    layout.alignment,
                ))
            }
            Ty::Dynamic { .. } => {
                let Some(Metadata::Vtable(index)) = metadata else {
                    return Err(Error::Undefined("invalid dynamic metadata"));
                };
                let table = self
                    .program
                    .hir
                    .vtables
                    .get(index as usize)
                    .ok_or(Error::Undefined("invalid vtable provenance"))?;
                let layout = self.layout(table.concrete)?;
                Ok((layout.size, layout.alignment))
            }
            _ => {
                let layout = self.layout(ty)?;
                Ok((layout.size, layout.alignment))
            }
        }
    }

    fn read_array(
        &mut self,
        address: &Address,
        element: TyId,
        count: u64,
        stride: u64,
    ) -> Result<ValueKind> {
        if count > self.limits.objects as u64 {
            return Err(Error::Limit("array element budget"));
        }
        let mut values = Vec::new();
        for index in 0..count {
            let pointer = self.memory.child(
                &address.pointer,
                index
                    .checked_mul(stride)
                    .ok_or(Error::Undefined("array byte range overflow"))?,
                (1 << 63) | index,
            )?;
            values.push(self.read(&Address {
                pointer,
                ty: element,
                metadata: None,
                variant: None,
            })?);
        }
        Ok(ValueKind::Fields(values))
    }

    fn read_fields(
        &mut self,
        address: &Address,
        fields: &[layout::Field],
        payload: u64,
    ) -> Result<Vec<Value>> {
        let mut values = Vec::new();
        for field in fields {
            let pointer =
                self.memory
                    .child(&address.pointer, payload + field.offset, field.index as u64)?;
            values.push(self.read(&Address {
                pointer,
                ty: field.ty,
                metadata: None,
                variant: None,
            })?);
        }
        Ok(values)
    }

    pub(super) fn read_word(&self, pointer: &Pointer, size: u64) -> Result<u128> {
        let bytes = self.memory.read_bytes(pointer, size)?;
        let mut word = [0; 16];
        if bytes.len() > word.len() {
            return Err(Error::Unsupported("non-scalar word"));
        }
        word[..bytes.len()].copy_from_slice(&bytes);
        Ok(u128::from_le_bytes(word))
    }

    pub(super) fn write(&mut self, address: &Address, value: &Value) -> Result<()> {
        self.tick()?;
        let program = self.program;
        let layout = program
            .layouts
            .get(address.ty)
            .ok_or(Error::Unsupported("write to unsized storage"))?;
        if let Ty::Named { definition, .. } = program.hir.types.get(address.ty) {
            self.memory
                .reinitialize(&address.pointer, *definition, layout.size == 0);
        }
        if let ValueKind::Task(task) = value.kind {
            if cavo_compiler::tasks::task_arguments(&program.hir, address.ty).is_none() {
                return Err(Error::Undefined("task handle stored as an unrelated type"));
            }
            return self.memory.write_task(&address.pointer, task);
        }
        match &layout.kind {
            layout::Kind::Scalar => self.write_scalar(address, value, layout.size)?,
            layout::Kind::Pointer { words } => self.write_pointer(address, value, *words)?,
            layout::Kind::Record { fields, .. } => {
                self.write_fields(address, fields, value.fields()?, 0)?
            }
            layout::Kind::Array {
                element,
                count,
                stride,
            } => self.write_array(address, *element, *count, *stride, value.fields()?)?,
            layout::Kind::Union { fields } => self.write_union(address, fields, value)?,
            layout::Kind::Enum { .. } => self.write_enum(address, layout, value)?,
        }
        if layout.size == 0 {
            self.memory.initialize_zero(&address.pointer)?;
        }
        for &(offset, nominal, field) in &address.pointer.unions {
            self.unions
                .insert((address.pointer.allocation, offset, nominal), field);
        }
        Ok(())
    }

    fn write_scalar(&mut self, address: &Address, value: &Value, size: u64) -> Result<()> {
        let bits = match value.kind {
            ValueKind::Bits(bits) => bits,
            ValueKind::FloatBits(bits) => bits.into(),
            ValueKind::Unit if size == 0 => return Ok(()),
            _ => return Err(Error::Undefined("invalid scalar representation")),
        };
        match self.program.hir.types.get(address.ty) {
            Ty::Bool if bits > 1 => return Err(Error::Undefined("invalid bool bit pattern")),
            Ty::Char if char::from_u32(bits as u32).is_none() => {
                return Err(Error::Undefined("invalid char bit pattern"));
            }
            _ => {}
        }
        self.write_word(&address.pointer, size, bits)
    }

    fn write_union(
        &mut self,
        address: &Address,
        fields: &[layout::Field],
        value: &Value,
    ) -> Result<()> {
        let ValueKind::Union(index, value) = &value.kind else {
            return Err(Error::Undefined("invalid union value"));
        };
        let field = fields
            .iter()
            .find(|field| field.index == *index)
            .ok_or(Error::Undefined("invalid union field"))?;
        let pointer = self
            .memory
            .child(&address.pointer, field.offset, field.index as u64)?;
        self.write(
            &Address {
                pointer,
                ty: field.ty,
                metadata: None,
                variant: None,
            },
            value,
        )?;
        let Ty::Named { definition, .. } = self.program.hir.types.get(address.ty) else {
            return Err(Error::Undefined("invalid union identity"));
        };
        self.unions.insert(
            (
                address.pointer.allocation,
                address.pointer.offset,
                *definition,
            ),
            *index,
        );
        Ok(())
    }

    fn write_enum(
        &mut self,
        address: &Address,
        layout: &layout::Layout,
        value: &Value,
    ) -> Result<()> {
        let layout::Kind::Enum {
            tag_bytes,
            payload_offset,
            variants,
        } = &layout.kind
        else {
            return Err(Error::Undefined("invalid enum layout"));
        };
        let ValueKind::Variant(id, values) = &value.kind else {
            return Err(Error::Undefined("invalid enum value"));
        };
        let variant = variants
            .iter()
            .find(|variant| variant.definition == *id)
            .ok_or(Error::Undefined("invalid enum variant"))?;
        self.write_word(
            &address.pointer,
            (*tag_bytes).into(),
            variant.discriminant.into(),
        )?;
        self.write_fields(address, &variant.fields, values, *payload_offset)
    }

    fn write_pointer(&mut self, address: &Address, value: &Value, words: u8) -> Result<()> {
        match &value.kind {
            ValueKind::Function(definition) => self
                .memory
                .write_atom(&address.pointer, Atom::Function(*definition)),
            ValueKind::Pointer { data, metadata } => {
                self.memory
                    .write_atom(&address.pointer, Atom::Pointer(data.clone()))?;
                if words == 2 {
                    let slot = self.memory.offset(&address.pointer, 8)?;
                    self.memory.write_atom(
                        &slot,
                        Atom::Metadata(metadata.unwrap_or(Metadata::Length(0))),
                    )?;
                }
                Ok(())
            }
            _ => Err(Error::Undefined("invalid pointer store")),
        }
    }

    fn write_fields(
        &mut self,
        address: &Address,
        fields: &[layout::Field],
        values: &[Value],
        payload: u64,
    ) -> Result<()> {
        if fields.len() != values.len() {
            return Err(Error::Undefined("invalid aggregate shape"));
        }
        for (field, value) in fields.iter().zip(values) {
            let pointer =
                self.memory
                    .child(&address.pointer, payload + field.offset, field.index as u64)?;
            self.write(
                &Address {
                    pointer,
                    ty: field.ty,
                    metadata: None,
                    variant: None,
                },
                value,
            )?;
        }
        Ok(())
    }

    fn write_array(
        &mut self,
        address: &Address,
        element: TyId,
        count: u64,
        stride: u64,
        values: &[Value],
    ) -> Result<()> {
        if count != values.len() as u64 {
            return Err(Error::Undefined("invalid array shape"));
        }
        for (index, value) in values.iter().enumerate() {
            let pointer = self.memory.child(
                &address.pointer,
                stride
                    .checked_mul(index as u64)
                    .ok_or(Error::Undefined("array byte range overflow"))?,
                (1 << 63) | index as u64,
            )?;
            self.write(
                &Address {
                    pointer,
                    ty: element,
                    metadata: None,
                    variant: None,
                },
                value,
            )?;
        }
        Ok(())
    }

    pub(super) fn write_word(&mut self, pointer: &Pointer, size: u64, bits: u128) -> Result<()> {
        let bytes = bits.to_le_bytes();
        let size = usize::try_from(size).map_err(|_| Error::Unsupported("non-scalar word"))?;
        if size > bytes.len() {
            return Err(Error::Unsupported("non-scalar word"));
        }
        self.memory.write_bytes(pointer, &bytes[..size])
    }
}
