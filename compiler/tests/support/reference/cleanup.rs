use super::*;
use mir::drop::{GlueId, GlueKind};

impl Machine<'_> {
    pub(super) fn glue(&mut self, id: GlueId, address: &Address, cursor: u64) -> Result<bool> {
        self.tick()?;
        if self.depth >= self.limits.frames {
            return Err(Error::Limit("cleanup stack budget"));
        }
        self.depth += 1;
        let result = self.glue_inner(id, address, cursor);
        self.depth -= 1;
        result
    }

    fn glue_inner(&mut self, id: GlueId, address: &Address, cursor: u64) -> Result<bool> {
        let program = self.program;
        let glue = program
            .analysis
            .drops
            .glue
            .get(id.0 as usize)
            .ok_or(Error::Undefined("invalid glue ID"))?;
        let address = Address {
            ty: glue.ty,
            ..address.clone()
        };
        match &glue.kind {
            GlueKind::Trivial => Ok(true),
            GlueKind::TaskHandle => self.drop_observation(&address),
            GlueKind::Destructor { destructor, .. } => {
                self.destructor(destructor.definition, &address)
            }
            GlueKind::User {
                destructor, fields, ..
            } => self.user_glue(destructor.definition, *fields, &address),
            GlueKind::Record(fields) => self.fields_glue(
                &address,
                fields.iter().map(|field| (field.field, field.glue)),
            ),
            GlueKind::Array { element, count } => self.array_glue(*element, &address, 0, *count),
            GlueKind::ArrayTail {
                element,
                count: mir::drop::ArrayLength::Concrete(count),
            } => self.array_glue(*element, &address, cursor, *count),
            GlueKind::Enum(variants) => self.enum_glue(&address, variants),
            _ => Err(Error::Unsupported("unresolved or manual drop glue")),
        }
    }

    fn drop_observation(&mut self, address: &Address) -> Result<bool> {
        let ValueKind::Task(task) = self.read(address)?.kind else {
            return Err(Error::Undefined("invalid task observation"));
        };
        self.release_observation(task)?;
        Ok(true)
    }

    fn user_glue(
        &mut self,
        destructor: hir::DefId,
        fields: GlueId,
        address: &Address,
    ) -> Result<bool> {
        let first = self.destructor(destructor, address)?;
        let second = self.glue(fields, address, 0)?;
        if !first && !second {
            return Err(Error::Trap("double cleanup failure"));
        }
        Ok(first && second)
    }

    fn fields_glue(
        &mut self,
        address: &Address,
        fields: impl Iterator<Item = (u32, GlueId)>,
    ) -> Result<bool> {
        let mut normal = true;
        for (field, glue) in fields {
            let place = self.field_address(address, field)?;
            let next = self.glue(glue, &place, 0)?;
            if !normal && !next {
                return Err(Error::Trap("double cleanup failure"));
            }
            normal &= next;
        }
        Ok(normal)
    }

    fn enum_glue(
        &mut self,
        address: &Address,
        variants: &[mir::drop::VariantGlue],
    ) -> Result<bool> {
        let active = self.tag(address)?;
        let variant = variants
            .iter()
            .find(|variant| variant.variant == active)
            .ok_or(Error::Undefined("invalid enum drop tag"))?;
        let address = Address {
            variant: Some(active),
            ..address.clone()
        };
        self.fields_glue(
            &address,
            variant
                .fields
                .iter()
                .enumerate()
                .map(|(index, &glue)| (index as u32, glue)),
        )
    }

    fn array_glue(
        &mut self,
        element: GlueId,
        address: &Address,
        start: u64,
        count: u64,
    ) -> Result<bool> {
        let mut normal = true;
        for index in start..count {
            let place = self.element_address(address, index)?;
            let next = self.glue(element, &place, 0)?;
            if !normal && !next {
                return Err(Error::Trap("double cleanup failure"));
            }
            normal &= next;
        }
        Ok(normal)
    }

    fn destructor(&mut self, definition: hir::DefId, address: &Address) -> Result<bool> {
        self.read(address)?;
        let Ty::Named {
            definition: nominal,
            ..
        } = self.program.hir.types.get(address.ty)
        else {
            return Err(Error::Undefined("destructor of non-nominal type"));
        };
        self.memory.note_drop(
            &address.pointer,
            *nominal,
            self.layout(address.ty)?.size == 0,
        )?;
        self.events.push(Event::Destructor(definition));
        let ty = self.program.hir.definitions[definition].ty;
        let Ty::Function { parameters, .. } = self.program.hir.types.get(ty) else {
            return Err(Error::Undefined("invalid destructor signature"));
        };
        let value = Value::pointer(parameters[0], address.pointer.clone(), None);
        match self.invoke(definition, vec![value])? {
            Outcome::Returned(_) => Ok(true),
            Outcome::Panicked | Outcome::Cancelled => Ok(false),
            Outcome::Aborted => Err(Error::Trap("destructor aborted")),
        }
    }

    pub(super) fn drop_value(&mut self, value: Value) -> Result<bool> {
        let layout = self.layout(value.ty)?;
        let pointer = self.memory.stack(layout.size)?;
        let address = Address {
            pointer: pointer.clone(),
            ty: value.ty,
            metadata: None,
            variant: None,
        };
        self.write(&address, &value)?;
        let glue = self
            .program
            .analysis
            .drops
            .glue
            .iter()
            .enumerate()
            .filter(|(_, glue)| {
                glue.ty == value.ty && !matches!(glue.kind, GlueKind::Destructor { .. })
            })
            .min_by_key(|(_, glue)| usize::from(!matches!(glue.kind, GlueKind::User { .. })))
            .map(|(index, _)| index);
        let normal = if let Some(glue) = glue {
            self.glue(GlueId(glue as u32), &address, 0)?
        } else {
            true
        };
        self.memory.end_stack(&pointer)?;
        Ok(normal)
    }
}
