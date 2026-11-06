use super::{body::Emitter, *};

pub(super) struct Address {
    pub pointer: String,
    pub ty: TyId,
    pub metadata: Option<String>,
}

impl Emitter<'_, '_> {
    pub fn address(&mut self, place: &mir::Place) -> Result<Address, Error> {
        let local = &self.core.locals[place.local];
        let mut address = Address {
            pointer: format!("%l{}", place.local.0),
            ty: local.ty,
            metadata: None,
        };
        let mut variant = None;
        for (index, projection) in place.projection.iter().enumerate() {
            match projection {
                mir::Projection::Deref if index == 0 && local.kind == mir::LocalKind::Address => {
                    if matches!(
                        self.module.program.hir.types.get(local.ty),
                        Ty::Slice(_) | Ty::Str | Ty::Dynamic { .. }
                    ) {
                        let slot = self.ir.offset(&address.pointer, 8);
                        address.metadata =
                            Some(self.ir.temp(format!("load i64, ptr {slot}, align 1")));
                    }
                    address.pointer = self
                        .ir
                        .temp(format!("load ptr, ptr {}, align 1", address.pointer));
                }
                mir::Projection::Deref => address = self.dereference(address)?,
                mir::Projection::Downcast(id) => variant = Some(*id),
                mir::Projection::Field(index) => {
                    let field = self.field(address.ty, variant.take(), *index)?;
                    address.pointer = self.ir.offset(&address.pointer, field.offset);
                    address.ty = field.ty;
                    address.metadata = None;
                }
                mir::Projection::Index(local) => {
                    let (element, stride) = match self
                        .module
                        .program
                        .layouts
                        .get(address.ty)
                        .map(|layout| &layout.kind)
                    {
                        Some(layout::Kind::Array {
                            element, stride, ..
                        }) => (*element, *stride),
                        _ => match self.module.program.hir.types.get(address.ty) {
                            Ty::Slice(inner) => (*inner, self.module.layout(*inner)?.size),
                            _ => {
                                return Err(
                                    self.error("native indexing requires array or slice storage")
                                );
                            }
                        },
                    };
                    let (ty, index) =
                        self.scalar(&mir::Operand::Copy(mir::Place::local(*local)))?;
                    let index = self.integer_to_i64(ty, index)?;
                    let bytes = self.ir.temp(format!("mul i64 {index}, {stride}"));
                    address.pointer = self.ir.temp(format!(
                        "getelementptr i8, ptr {}, i64 {bytes}",
                        address.pointer
                    ));
                    address.ty = element;
                    address.metadata = None;
                }
            }
        }
        Ok(address)
    }

    pub fn dereference(&mut self, address: Address) -> Result<Address, Error> {
        let inner = match self.module.program.hir.types.get(address.ty) {
            Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
            _ => return Err(self.error("dereference has no native pointer representation")),
        };
        let wide = matches!(
            self.module.layout(address.ty)?.kind,
            layout::Kind::Pointer { words: 2 }
        );
        let metadata = if wide {
            let slot = self.ir.offset(&address.pointer, 8);
            Some(self.ir.temp(format!("load i64, ptr {slot}, align 1")))
        } else {
            None
        };
        let pointer = self
            .ir
            .temp(format!("load ptr, ptr {}, align 1", address.pointer));
        Ok(Address {
            pointer,
            ty: inner,
            metadata,
        })
    }

    pub fn field(
        &self,
        ty: TyId,
        variant: Option<hir::DefId>,
        index: u32,
    ) -> Result<layout::Field, Error> {
        let (fields, payload) = match &self.module.layout(ty)?.kind {
            layout::Kind::Record { fields, .. } | layout::Kind::Union { fields } => (fields, 0),
            layout::Kind::Enum {
                variants,
                payload_offset,
                ..
            } => (
                &variants
                    .iter()
                    .find(|item| Some(item.definition) == variant)
                    .ok_or_else(|| self.error("enum field lacks a checked downcast"))?
                    .fields,
                *payload_offset,
            ),
            _ => return Err(self.error("field projection has no aggregate layout")),
        };
        fields
            .iter()
            .find(|field| field.index == index)
            .cloned()
            .map(|mut field| {
                field.offset += payload;
                field
            })
            .ok_or_else(|| self.error("native field layout is missing"))
    }

    pub fn integer_to_i64(&mut self, ty: TyId, value: String) -> Result<String, Error> {
        let scalar = self.module.scalar_type(ty)?;
        if scalar == "i64" {
            return Ok(value);
        }
        let Ty::Integer { bits, .. } = self.module.program.hir.types.get(ty) else {
            return Err(self.error("native index is not an integer"));
        };
        Ok(self.ir.temp(format!(
            "{} {scalar} {value} to i64",
            if *bits < 64 { "zext" } else { "trunc" }
        )))
    }

    pub fn tag(&mut self, place: &mir::Place, variant: hir::DefId) -> Result<String, Error> {
        let address = self.address(place)?;
        let layout::Kind::Enum {
            tag_bytes,
            variants,
            ..
        } = &self.module.layout(address.ty)?.kind
        else {
            return Err(self.error("variant test requires enum storage"));
        };
        let discriminant = variants
            .iter()
            .find(|item| item.definition == variant)
            .ok_or_else(|| self.error("unknown native enum variant"))?
            .discriminant;
        let ty = format!("i{}", u32::from(*tag_bytes) * 8);
        let tag = self
            .ir
            .temp(format!("load {ty}, ptr {}, align 1", address.pointer));
        Ok(self.ir.temp(format!("icmp eq {ty} {tag}, {discriminant}")))
    }
}
