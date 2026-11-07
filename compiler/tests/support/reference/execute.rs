use super::*;

impl Machine<'_> {
    pub(super) fn invoke(
        &mut self,
        definition: hir::DefId,
        arguments: Vec<Value>,
    ) -> Result<Outcome> {
        self.tick()?;
        if let Some(outcome) = self.stimulated(definition, &arguments)? {
            return Ok(outcome);
        }
        if self.depth >= self.limits.frames {
            return Err(Error::Limit("call frame budget"));
        }
        let program = self.program;
        let body = program
            .mir
            .functions
            .iter()
            .find(|body| body.definition == definition)
            .ok_or(Error::Unsupported(
                "external call needs an explicit test binding",
            ))?;
        let cleanup = program
            .analysis
            .drops
            .functions
            .iter()
            .find(|body| body.definition == definition)
            .ok_or(Error::Unsupported("missing concrete cleanup graph"))?;
        if arguments.len()
            != body
                .locals
                .iter()
                .filter(|local| local.kind == mir::LocalKind::Parameter)
                .count()
        {
            return Err(Error::Undefined("call argument count"));
        }
        let mut frame = Frame {
            body,
            cleanup,
            locals: vec![None; body.locals.len()],
            flags: vec![false; cleanup.flags.len()],
            captures: HashMap::new(),
            cursors: HashMap::new(),
            registries: HashMap::new(),
            arguments,
            argument: 0,
            scopes: Vec::new(),
        };
        self.depth += 1;
        let result = self.execute(&mut frame);
        self.depth -= 1;
        if matches!(
            result,
            Ok(Outcome::Returned(_) | Outcome::Panicked | Outcome::Cancelled)
        ) {
            self.finish_frame(&mut frame)?;
        }
        result
    }

    fn stimulated(
        &mut self,
        definition: hir::DefId,
        arguments: &[Value],
    ) -> Result<Option<Outcome>> {
        let Some(stimulus) = self.stimuli.get(&definition).cloned() else {
            return Ok(None);
        };
        if arguments.iter().any(|value| self.owns_cleanup(value)) {
            return Err(Error::Unsupported(
                "opaque stimulus must model owned-argument cleanup",
            ));
        }
        if let Stimulus::Return(value) = &stimulus
            && !self
                .copies
                .get(value.ty.0 as usize)
                .copied()
                .unwrap_or(false)
        {
            self.stimuli.remove(&definition);
        }
        Ok(Some(match stimulus {
            Stimulus::Return(value) => Outcome::Returned(value),
            Stimulus::Panic => Outcome::Panicked,
            Stimulus::Cancel => Outcome::Cancelled,
        }))
    }

    fn owns_cleanup(&self, value: &Value) -> bool {
        if hir::traits::has_drop(&self.program.hir, value.ty) {
            return true;
        }
        match &value.kind {
            ValueKind::Task(_) => true,
            ValueKind::Fields(fields) | ValueKind::Variant(_, fields) => {
                fields.iter().any(|value| self.owns_cleanup(value))
            }
            ValueKind::Union(_, value) => self.owns_cleanup(value),
            _ => false,
        }
    }

    fn finish_frame(&mut self, frame: &mut Frame<'_>) -> Result<()> {
        for (index, local) in frame.locals.iter_mut().enumerate() {
            if let Some(pointer) = local.take() {
                if index != frame.body.return_local.0 as usize {
                    return Err(Error::Undefined("frame exited before storage cleanup"));
                }
                self.memory.end_stack(&pointer)?;
            }
        }
        Ok(())
    }

    pub(super) fn operand(
        &mut self,
        operand: &mir::Operand,
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let address = self.place(place, frame)?;
                if matches!(operand, mir::Operand::Copy(_))
                    && !self
                        .copies
                        .get(address.ty.0 as usize)
                        .copied()
                        .unwrap_or(false)
                {
                    return Err(Error::Undefined("copy of an affine value"));
                }
                let value = self.read(&address)?;
                if matches!(operand, mir::Operand::Move(_)) {
                    self.memory
                        .invalidate(&address.pointer, self.layout(address.ty)?.size)?;
                }
                Ok(value)
            }
            mir::Operand::Constant { value, ty } => self.constant(value, *ty),
            mir::Operand::ConstTerm { value, ty } => Ok(Value::bits(
                *ty,
                self.program
                    .hir
                    .types
                    .const_usize(*value)
                    .ok_or(Error::Unsupported("symbolic runtime constant"))?
                    .into(),
            )),
            mir::Operand::Function { definition, ty } => Ok(Value {
                ty: *ty,
                kind: ValueKind::Function(*definition),
            }),
            mir::Operand::Unit => Ok(Value::unit()),
        }
    }

    fn constant(&mut self, value: &hir::Constant, ty: TyId) -> Result<Value> {
        match value {
            hir::Constant::Integer {
                magnitude,
                negative,
            } => {
                let (width, _) = self.integer_type(ty)?;
                Ok(Value::bits(
                    ty,
                    if *negative {
                        magnitude.wrapping_neg()
                    } else {
                        *magnitude
                    } & arithmetic::mask(width),
                ))
            }
            hir::Constant::Bool(value) => Ok(Value::boolean(*value)),
            hir::Constant::Char(value) => Ok(Value::bits(ty, (*value as u32).into())),
            hir::Constant::Float(value) => Ok(self.float_value(ty, *value)),
            hir::Constant::Null => Ok(Value {
                ty,
                kind: ValueKind::Pointer {
                    data: None,
                    metadata: None,
                },
            }),
            hir::Constant::String(value) => {
                let data = if let Some(pointer) = self.strings.get(value) {
                    pointer.clone()
                } else {
                    let pointer = self.memory.literal(value.as_bytes())?;
                    self.strings.insert(value.clone(), pointer.clone());
                    pointer
                };
                Ok(Value::pointer(
                    ty,
                    data,
                    Some(Metadata::Length(value.len() as u64)),
                ))
            }
        }
    }

    pub(super) fn place(&mut self, place: &mir::Place, frame: &mut Frame<'_>) -> Result<Address> {
        let local = &frame.body.locals[place.local.0 as usize];
        let pointer = frame
            .locals
            .get(place.local.0 as usize)
            .and_then(Clone::clone)
            .ok_or(Error::Undefined("access to dead local storage"))?;
        let mut address = Address {
            pointer,
            ty: local.ty,
            metadata: None,
            variant: None,
        };
        for (index, projection) in place.projection.iter().enumerate() {
            match projection {
                mir::Projection::Deref if index == 0 && local.kind == mir::LocalKind::Address => {
                    address = frame
                        .captures
                        .get(&place.local)
                        .cloned()
                        .ok_or(Error::Undefined("uninitialized captured address"))?
                }
                mir::Projection::Deref => address = self.dereference(&address)?,
                mir::Projection::Downcast(variant) => {
                    if self.tag(&address)? != *variant {
                        return Err(Error::Undefined("inactive enum projection"));
                    }
                    address.variant = Some(*variant);
                }
                mir::Projection::Field(index) => address = self.field_address(&address, *index)?,
                mir::Projection::Index(index) => {
                    let index = self
                        .operand(&mir::Operand::Copy(mir::Place::local(*index)), frame)?
                        .unsigned()?;
                    address = self.element_address(
                        &address,
                        u64::try_from(index)
                            .map_err(|_| Error::Undefined("array index overflow"))?,
                    )?;
                }
            }
        }
        Ok(address)
    }

    fn dereference(&mut self, address: &Address) -> Result<Address> {
        let (Ty::Reference { inner, .. } | Ty::Pointer { inner, .. }) =
            self.program.hir.types.get(address.ty)
        else {
            return Err(Error::Undefined("dereference of non-pointer"));
        };
        let ty = *inner;
        let value = self.read(address)?;
        let pointer = value.address()?;
        let ValueKind::Pointer { metadata, .. } = value.kind else {
            return Err(Error::Undefined("dereference of non-pointer"));
        };
        Ok(Address {
            pointer,
            ty,
            metadata,
            variant: None,
        })
    }

    pub(super) fn field_address(&mut self, address: &Address, index: u32) -> Result<Address> {
        let program = self.program;
        let layout = program
            .layouts
            .get(address.ty)
            .ok_or(Error::Unsupported("field layout"))?;
        let (fields, payload) = match &layout.kind {
            layout::Kind::Record { fields, .. } | layout::Kind::Union { fields } => (fields, 0),
            layout::Kind::Enum {
                variants,
                payload_offset,
                ..
            } => (
                &variants
                    .iter()
                    .find(|variant| Some(variant.definition) == address.variant)
                    .ok_or(Error::Undefined("enum projection lacks a variant"))?
                    .fields,
                *payload_offset,
            ),
            _ => return Err(Error::Undefined("field projection of non-aggregate")),
        };
        let field = fields
            .iter()
            .find(|field| field.index == index)
            .ok_or(Error::Undefined("field index"))?;
        let mut pointer =
            self.memory
                .child(&address.pointer, payload + field.offset, index.into())?;
        if matches!(layout.kind, layout::Kind::Union { .. }) {
            let Ty::Named { definition, .. } = program.hir.types.get(address.ty) else {
                return Err(Error::Undefined("union without nominal identity"));
            };
            pointer
                .unions
                .push((address.pointer.offset, *definition, index));
        }
        Ok(Address {
            pointer,
            ty: field.ty,
            metadata: None,
            variant: None,
        })
    }

    pub(super) fn element_address(&mut self, address: &Address, index: u64) -> Result<Address> {
        let (element, count, stride) = match self.program.hir.types.get(address.ty) {
            Ty::Slice(inner) => {
                let Some(Metadata::Length(count)) = address.metadata else {
                    return Err(Error::Undefined("slice lacks length"));
                };
                (*inner, count, self.layout(*inner)?.size)
            }
            _ => match self.layout(address.ty)?.kind {
                layout::Kind::Array {
                    element,
                    count,
                    stride,
                } => (element, count, stride),
                _ => return Err(Error::Undefined("indexing a non-array")),
            },
        };
        if index >= count {
            return Err(Error::Undefined("out of bounds"));
        }
        let pointer = self.memory.child(
            &address.pointer,
            stride
                .checked_mul(index)
                .ok_or(Error::Undefined("array offset overflow"))?,
            (1 << 63) | index,
        )?;
        Ok(Address {
            pointer,
            ty: element,
            metadata: None,
            variant: None,
        })
    }

    pub(super) fn tag(&self, address: &Address) -> Result<hir::DefId> {
        let layout::Kind::Enum {
            tag_bytes,
            ref variants,
            ..
        } = self.layout(address.ty)?.kind
        else {
            return Err(Error::Undefined("tag of non-enum"));
        };
        let tag = self.read_word(&address.pointer, tag_bytes.into())?;
        variants
            .iter()
            .find(|variant| variant.discriminant as u128 == tag)
            .map(|variant| variant.definition)
            .ok_or(Error::Undefined("invalid enum bit pattern"))
    }

    pub(super) fn length(&self, address: &Address) -> Result<u64> {
        match self.program.hir.types.get(address.ty) {
            Ty::Str | Ty::Slice(_) => match address.metadata {
                Some(Metadata::Length(n)) => Ok(n),
                _ => Err(Error::Undefined("missing length metadata")),
            },
            _ => match self.layout(address.ty)?.kind {
                layout::Kind::Array { count, .. } => Ok(count),
                _ => Err(Error::Undefined("length of a non-sequence")),
            },
        }
    }

    pub(super) fn value(
        &mut self,
        value: &mir::Rvalue,
        ty: TyId,
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        use mir::Rvalue as R;
        match value {
            R::Use(operand) => self.operand(operand, frame),
            R::Unary { op, operand } => {
                let value = self.operand(operand, frame)?;
                self.unary(*op, value)
            }
            R::Binary { op, left, right } => {
                let a = self.operand(left, frame)?;
                let b = self.operand(right, frame)?;
                self.binary(*op, a, b)
            }
            R::Borrow { place, .. } => self.borrow_value(place, ty, frame),
            R::AddressOf(_) => Err(Error::Undefined("internal address used as a Cavo value")),
            R::Array(values) => {
                let values = self.operands(values, frame)?;
                Ok(Value {
                    ty,
                    kind: ValueKind::Fields(values),
                })
            }
            R::Record { fields, .. } => self.record_value(ty, fields, frame),
            R::Variant { definition, fields } => {
                let values = self.operands(fields, frame)?;
                Ok(Value {
                    ty,
                    kind: ValueKind::Variant(*definition, values),
                })
            }
            R::Repeat { value, count } => self.repeat(value, *count, ty, frame),
            R::RepeatConst { value, count } => self.repeat(
                value,
                self.program
                    .hir
                    .types
                    .const_usize(*count)
                    .ok_or(Error::Unsupported("symbolic repeat"))?,
                ty,
                frame,
            ),
            R::Length(place) => {
                let address = self.place(place, frame)?;
                Ok(Value::bits(ty, self.length(&address)?.into()))
            }
            R::IsVariant { place, variant } => {
                let address = self.place(place, frame)?;
                Ok(Value::boolean(self.tag(&address)? == *variant))
            }
            R::ArrayToSlice(value) => self.slice_value(value, ty, frame),
            R::DynCoerce { value, vtable } => {
                let value = self.operand(value, frame)?;
                Ok(Value::pointer(
                    ty,
                    value.address()?,
                    Some(Metadata::Vtable(*vtable)),
                ))
            }
        }
    }

    pub(super) fn operands(
        &mut self,
        values: &[mir::Operand],
        frame: &mut Frame<'_>,
    ) -> Result<Vec<Value>> {
        if values.len() > self.limits.objects {
            return Err(Error::Limit("operand value budget"));
        }
        let mut result = Vec::new();
        for value in values {
            self.tick()?;
            result.push(self.operand(value, frame)?);
        }
        Ok(result)
    }

    fn validate_referent(&mut self, address: &Address) -> Result<()> {
        match self.program.hir.types.get(address.ty) {
            Ty::Dynamic { .. } => {
                let Some(Metadata::Vtable(index)) = address.metadata else {
                    return Err(Error::Undefined("dynamic reference lacks metadata"));
                };
                let table = self
                    .program
                    .hir
                    .vtables
                    .get(index as usize)
                    .ok_or(Error::Undefined("invalid vtable"))?;
                self.read(&Address {
                    ty: table.concrete,
                    ..address.clone()
                })?;
            }
            Ty::Slice(_) => {
                for index in 0..self.length(address)? {
                    let element = self.element_address(address, index)?;
                    self.read(&element)?;
                }
            }
            Ty::Str => {
                let bytes = self
                    .memory
                    .read_bytes(&address.pointer, self.length(address)?)?;
                std::str::from_utf8(&bytes)
                    .map_err(|_| Error::Undefined("invalid str representation"))?;
            }
            _ => {
                self.read(address)?;
            }
        }
        Ok(())
    }

    fn borrow_value(
        &mut self,
        place: &mir::Place,
        ty: TyId,
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        let address = self.place(place, frame)?;
        self.validate_referent(&address)?;
        let (size, alignment) = self.referent_layout(address.ty, address.metadata)?;
        self.memory.check(&address.pointer, size, alignment)?;
        Ok(Value::pointer(ty, address.pointer, address.metadata))
    }

    fn repeat(
        &mut self,
        value: &mir::Operand,
        count: u64,
        ty: TyId,
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        if count > self.limits.objects as u64 {
            return Err(Error::Limit("repeat element budget"));
        }
        let value = self.operand(value, frame)?;
        let nodes = value.node_count(self.limits.objects)?;
        if (count as usize)
            .checked_mul(nodes)
            .is_none_or(|nodes| nodes > self.limits.objects || nodes > self.remaining)
        {
            return Err(Error::Limit("repeated logical value budget"));
        }
        Ok(Value {
            ty,
            kind: ValueKind::Fields(vec![value; count as usize]),
        })
    }

    fn record_value(
        &mut self,
        ty: TyId,
        fields: &[(u32, mir::Operand)],
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        if matches!(self.layout(ty)?.kind, layout::Kind::Union { .. }) {
            let [(index, value)] = fields else {
                return Err(Error::Undefined("invalid union initializer"));
            };
            return Ok(Value {
                ty,
                kind: ValueKind::Union(*index, Box::new(self.operand(value, frame)?)),
            });
        }
        let mut values = vec![None; fields.len()];
        for (index, value) in fields {
            *values
                .get_mut(*index as usize)
                .ok_or(Error::Undefined("record field index"))? = Some(self.operand(value, frame)?);
        }
        let values = values
            .into_iter()
            .map(|value| value.ok_or(Error::Undefined("uninitialized record field")))
            .collect::<Result<_>>()?;
        Ok(Value {
            ty,
            kind: ValueKind::Fields(values),
        })
    }

    fn slice_value(
        &mut self,
        value: &mir::Operand,
        ty: TyId,
        frame: &mut Frame<'_>,
    ) -> Result<Value> {
        let value = self.operand(value, frame)?;
        let Ty::Reference { inner, .. } = self.program.hir.types.get(value.ty) else {
            return Err(Error::Undefined("slice coercion requires a reference"));
        };
        let layout::Kind::Array { count, .. } = self.layout(*inner)?.kind else {
            return Err(Error::Undefined("slice coercion requires an array"));
        };
        Ok(Value::pointer(
            ty,
            value.address()?,
            Some(Metadata::Length(count)),
        ))
    }
}
