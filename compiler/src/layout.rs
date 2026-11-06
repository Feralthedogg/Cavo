//! Checked, target-explicit storage layouts. This is not C calling-convention
//! classification and does not authorize LLVM pointer or alias attributes.

mod attributes;

use crate::{
    hir,
    source::{SourceMap, Span},
    symbol::Interner,
    types::{GenericArg, Ty, TyId},
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetLayout {
    pub pointer_bits: u16,
    pub integer_128_alignment: u64,
    pub maximum_alignment: u64,
    pub maximum_object_size: u64,
}
impl TargetLayout {
    /// Storage rules shared by the currently selected 64-bit Cavo targets.
    /// Target-specific aggregate register/sret classification is a later pass.
    pub const LP64: Self = Self {
        pointer_bits: 64,
        integer_128_alignment: 16,
        maximum_alignment: 1 << 29,
        maximum_object_size: i64::MAX as u64,
    };
    fn validate(self) -> Result<(), Error> {
        if self.pointer_bits != 64
            || !self.integer_128_alignment.is_power_of_two()
            || !self.maximum_alignment.is_power_of_two()
            || self.integer_128_alignment > self.maximum_alignment
            || self.maximum_object_size > i64::MAX as u64
        {
            return Err(Error::new(
                TyId::ERROR,
                "unsupported or inconsistent target layout",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub ty: TyId,
    pub size: u64,
    pub alignment: u64,
    pub c_compatible: bool,
    pub kind: Kind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Scalar,
    Pointer {
        words: u8,
    },
    Record {
        fields: Vec<Field>,
        packed: bool,
    },
    Union {
        fields: Vec<Field>,
    },
    Array {
        element: TyId,
        count: u64,
        stride: u64,
    },
    Enum {
        tag_bytes: u8,
        payload_offset: u64,
        variants: Vec<Variant>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub index: u32,
    pub ty: TyId,
    pub offset: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub definition: hir::DefId,
    /// Physical tag value; variant identity in HIR/MIR remains its DefId.
    pub discriminant: u64,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug)]
pub struct Table {
    pub target: TargetLayout,
    pub entries: Vec<Layout>,
    indices: HashMap<TyId, usize>,
}
impl Table {
    pub fn get(&self, ty: TyId) -> Option<&Layout> {
        self.indices.get(&ty).map(|&index| &self.entries[index])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub ty: TyId,
    pub span: Option<Span>,
    pub message: String,
}
impl Error {
    fn new(ty: TyId, message: &str) -> Self {
        Self {
            ty,
            span: None,
            message: message.into(),
        }
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Error {}

pub fn compute(
    program: &mut hir::Program,
    target: TargetLayout,
    symbols: &Interner,
    sources: &SourceMap,
    roots: &[TyId],
) -> Result<Table, Error> {
    target.validate()?;
    program
        .validate()
        .map_err(|error| Error::new(TyId::ERROR, &format!("invalid layout input: {error}")))?;
    let mut query = Query::new(program, target, symbols, sources);
    for &root in roots {
        query.resolve(root, 0)?;
    }
    Ok(query.table)
}

struct Query<'a> {
    program: &'a mut hir::Program,
    symbols: &'a Interner,
    sources: &'a SourceMap,
    table: Table,
    records: Vec<Option<usize>>,
    enumerations: Vec<Option<usize>>,
    active: HashSet<TyId>,
    remaining: usize,
}
impl<'a> Query<'a> {
    fn new(
        program: &'a mut hir::Program,
        target: TargetLayout,
        symbols: &'a Interner,
        sources: &'a SourceMap,
    ) -> Self {
        let mut records = vec![None; program.definitions.len()];
        let mut enumerations = vec![None; program.definitions.len()];
        for (index, record) in program.records.iter().enumerate() {
            records[record.definition.0 as usize] = Some(index);
        }
        for (index, enumeration) in program.enums.iter().enumerate() {
            enumerations[enumeration.definition.0 as usize] = Some(index);
        }
        Self {
            program,
            symbols,
            sources,
            records,
            enumerations,
            table: Table {
                target,
                entries: Vec::new(),
                indices: HashMap::new(),
            },
            active: HashSet::new(),
            remaining: 200_000,
        }
    }
    fn resolve(&mut self, ty: TyId, depth: usize) -> Result<usize, Error> {
        if let Some(&index) = self.table.indices.get(&ty) {
            return Ok(index);
        }
        if self.remaining == 0 || depth >= 128 {
            return Err(Error::new(ty, "layout query resource limit exceeded"));
        }
        if !self.active.insert(ty) {
            return Err(Error::new(ty, "recursive by-value layout"));
        }
        self.remaining -= 1;
        let result = self.layout(ty, depth + 1);
        self.active.remove(&ty);
        let layout = result?;
        self.check_size(ty, layout.size)?;
        let index = self.table.entries.len();
        self.table.entries.push(layout);
        self.table.indices.insert(ty, index);
        Ok(index)
    }
    fn layout(&mut self, ty: TyId, depth: usize) -> Result<Layout, Error> {
        let kind = self
            .program
            .types
            .values()
            .get(ty.0 as usize)
            .cloned()
            .ok_or_else(|| Error::new(ty, "invalid layout type ID"))?;
        match kind {
            Ty::Void => Ok(scalar(ty, 0, 1, false)),
            Ty::Bool => Ok(scalar(ty, 1, 1, true)),
            Ty::Char => Ok(scalar(ty, 4, 4, true)),
            Ty::Integer { bits, .. } => self.integer(ty, bits),
            Ty::Float { bits: 32 } => Ok(scalar(ty, 4, 4, true)),
            Ty::Float { bits: 64 } => Ok(scalar(ty, 8, 8, true)),
            Ty::Reference { inner, .. } => self.pointer(ty, inner, false),
            Ty::Pointer { inner, .. } => self.pointer(ty, inner, true),
            Ty::Function { .. } | Ty::ForAll { .. } => self.pointer(ty, TyId::VOID, false),
            Ty::Array { inner, length } => self.array(ty, inner, length, depth),
            Ty::SymbolicArray { inner, length } => self.symbolic_array(ty, inner, length, depth),
            Ty::Named {
                definition,
                arguments,
            } => {
                if Some(definition) == self.program.tasks.task {
                    Ok(Layout {
                        ty,
                        size: 16,
                        alignment: 8,
                        c_compatible: false,
                        kind: Kind::Pointer { words: 2 },
                    })
                } else {
                    self.named(ty, definition, &arguments, depth)
                }
            }
            Ty::Str | Ty::Slice(_) | Ty::Dynamic { .. } => Err(Error::new(
                ty,
                "unsized type has no standalone storage layout",
            )),
            Ty::Parameter { .. } => {
                Err(Error::new(ty, "layout requires concrete generic arguments"))
            }
            _ => Err(Error::new(
                ty,
                "type or constant length is not concrete for layout",
            )),
        }
    }
    fn integer(&self, ty: TyId, bits: u16) -> Result<Layout, Error> {
        let bits = if bits == 0 {
            self.table.target.pointer_bits
        } else {
            bits
        };
        if !matches!(bits, 8 | 16 | 32 | 64 | 128) {
            return Err(Error::new(ty, "unsupported integer storage width"));
        }
        let bytes = u64::from(bits / 8);
        let alignment = if bits == 128 {
            self.table.target.integer_128_alignment
        } else {
            bytes
        };
        Ok(scalar(ty, bytes, alignment, true))
    }
    fn pointer(&self, ty: TyId, inner: TyId, raw: bool) -> Result<Layout, Error> {
        let pointee = self
            .program
            .types
            .values()
            .get(inner.0 as usize)
            .ok_or_else(|| Error::new(ty, "pointer has an invalid pointee"))?;
        let words = if matches!(pointee, Ty::Str | Ty::Slice(_) | Ty::Dynamic { .. }) {
            2
        } else {
            1
        };
        let bytes = u64::from(self.table.target.pointer_bits / 8);
        Ok(Layout {
            ty,
            size: bytes * u64::from(words),
            alignment: bytes,
            c_compatible: raw && words == 1,
            kind: Kind::Pointer { words },
        })
    }
    fn array(
        &mut self,
        ty: TyId,
        element: TyId,
        count: u64,
        depth: usize,
    ) -> Result<Layout, Error> {
        let index = self.resolve(element, depth)?;
        let element_layout = &self.table.entries[index];
        let stride = align_up(ty, element_layout.size, element_layout.alignment)?;
        let size = stride
            .checked_mul(count)
            .ok_or_else(|| Error::new(ty, "array byte size overflows target object size"))?;
        Ok(Layout {
            ty,
            size,
            alignment: element_layout.alignment,
            c_compatible: element_layout.c_compatible,
            kind: Kind::Array {
                element,
                count,
                stride,
            },
        })
    }
    fn symbolic_array(
        &mut self,
        ty: TyId,
        inner: TyId,
        length: crate::types::ConstId,
        depth: usize,
    ) -> Result<Layout, Error> {
        let limits = crate::ctfe::Limits {
            pointer_bits: self.table.target.pointer_bits,
            ..crate::ctfe::Limits::default()
        };
        let length =
            crate::ctfe::evaluate_term(self.program, length, limits).map_err(|error| Error {
                ty,
                span: Some(error.span),
                message: error.message,
            })?;
        let length = self
            .program
            .types
            .const_usize(length)
            .ok_or_else(|| Error::new(ty, "array length is not a concrete usize"))?;
        self.array(ty, inner, length, depth)
    }
    fn named(
        &mut self,
        ty: TyId,
        definition: hir::DefId,
        arguments: &[GenericArg],
        depth: usize,
    ) -> Result<Layout, Error> {
        let declaration = self.program.definitions[definition].clone();
        let union = declaration.kind == hir::DefinitionKind::Union;
        let options = attributes::parse(
            self.program,
            attributes::Instance {
                owner: definition,
                declaration: &declaration,
                arguments,
            },
            self.table.target,
            self.symbols,
            self.sources,
        )
        .map_err(|mut error| {
            error.ty = ty;
            error
        })?;
        let limits = crate::ctfe::Limits {
            pointer_bits: self.table.target.pointer_bits,
            ..crate::ctfe::Limits::default()
        };
        crate::ctfe::check_assertions(self.program, definition, arguments, limits).map_err(
            |error| Error {
                ty,
                span: Some(error.span),
                message: error.message,
            },
        )?;
        if let Some(index) = self.records[definition.0 as usize] {
            let source: Vec<_> = self.program.records[index]
                .fields
                .iter()
                .map(|field| field.ty)
                .collect();
            let fields = self.substituted(&source, definition, arguments)?;
            return self.record(ty, &fields, options, union, depth);
        }
        if self.enumerations[definition.0 as usize].is_some() {
            return self.enumeration(ty, definition, arguments, options, depth);
        }
        Err(Error::new(
            ty,
            "nominal type has no concrete storage declaration",
        ))
    }
    fn substituted(
        &mut self,
        fields: &[TyId],
        owner: hir::DefId,
        arguments: &[GenericArg],
    ) -> Result<Vec<TyId>, Error> {
        fields
            .iter()
            .map(|&ty| {
                self.program
                    .types
                    .substitute_generics(ty, owner, arguments)
                    .map_err(|error| Error::new(ty, &error.to_string()))
            })
            .collect()
    }
    fn record(
        &mut self,
        ty: TyId,
        fields: &[TyId],
        options: attributes::Options,
        union: bool,
        depth: usize,
    ) -> Result<Layout, Error> {
        let aggregate = self.fields(ty, fields, options.packed, union, depth)?;
        if options.c && !aggregate.c_compatible {
            return Err(Error::new(
                ty,
                "repr(C) aggregate contains a non-C-compatible field",
            ));
        }
        let alignment = aggregate.alignment.max(options.alignment);
        let size = align_up(ty, aggregate.size, alignment)?;
        let kind = if union {
            Kind::Union {
                fields: aggregate.fields,
            }
        } else {
            Kind::Record {
                fields: aggregate.fields,
                packed: options.packed,
            }
        };
        Ok(Layout {
            ty,
            size,
            alignment,
            c_compatible: options.c && aggregate.c_compatible,
            kind,
        })
    }
    fn fields(
        &mut self,
        ty: TyId,
        types: &[TyId],
        packed: bool,
        union: bool,
        depth: usize,
    ) -> Result<Aggregate, Error> {
        let mut aggregate = Aggregate {
            fields: Vec::with_capacity(types.len()),
            size: 0,
            alignment: 1,
            c_compatible: true,
        };
        for (index, &field_ty) in types.iter().enumerate() {
            let child = self.resolve(field_ty, depth)?;
            let child = &self.table.entries[child];
            let alignment = if packed { 1 } else { child.alignment };
            let offset = if union {
                0
            } else {
                align_up(ty, aggregate.size, alignment)?
            };
            let end = offset
                .checked_add(child.size)
                .ok_or_else(|| Error::new(ty, "field byte offset overflows"))?;
            aggregate.size = aggregate.size.max(end);
            aggregate.alignment = aggregate.alignment.max(alignment);
            aggregate.c_compatible &= child.c_compatible;
            aggregate.fields.push(Field {
                index: index as u32,
                ty: field_ty,
                offset,
            });
        }
        aggregate.size = align_up(ty, aggregate.size, aggregate.alignment)?;
        Ok(aggregate)
    }
    fn enumeration(
        &mut self,
        ty: TyId,
        owner: hir::DefId,
        arguments: &[GenericArg],
        options: attributes::Options,
        depth: usize,
    ) -> Result<Layout, Error> {
        let index = self.enumerations[owner.0 as usize].expect("enum declaration index");
        if options.packed {
            return Err(Error::new(
                ty,
                "packed tagged-enum representation is not supported",
            ));
        }
        let declarations = self.program.enums[index].variants.clone();
        let limits = crate::ctfe::Limits {
            pointer_bits: self.table.target.pointer_bits,
            ..crate::ctfe::Limits::default()
        };
        let discriminants = crate::sema::enum_discriminants(self.program, owner, arguments, limits)
            .map_err(|error| Error {
                ty,
                span: Some(error.span),
                message: error.message,
            })?;
        let tag_bytes = tag_bytes(discriminants.iter().copied().max(), options.c)?;
        let mut variants = Vec::with_capacity(declarations.len());
        let mut payload_size = 0;
        let mut payload_align = 1;
        for (declaration, discriminant) in declarations.into_iter().zip(discriminants) {
            let fields = self.variant_fields(declaration, owner, arguments)?;
            let aggregate = self.fields(ty, &fields, false, false, depth)?;
            if options.c && !aggregate.c_compatible {
                return Err(Error::new(
                    ty,
                    "repr(C) enum contains a non-C-compatible payload",
                ));
            }
            payload_size = payload_size.max(aggregate.size);
            payload_align = payload_align.max(aggregate.alignment);
            variants.push(Variant {
                definition: declaration,
                discriminant,
                fields: aggregate.fields,
            });
        }
        let payload_offset = align_up(ty, u64::from(tag_bytes), payload_align)?;
        let alignment = payload_align
            .max(u64::from(tag_bytes))
            .max(options.alignment);
        let end = payload_offset
            .checked_add(payload_size)
            .ok_or_else(|| Error::new(ty, "enum payload byte size overflows"))?;
        let size = align_up(ty, end, alignment)?;
        Ok(Layout {
            ty,
            size,
            alignment,
            c_compatible: options.c,
            kind: Kind::Enum {
                tag_bytes,
                payload_offset,
                variants,
            },
        })
    }
    fn variant_fields(
        &mut self,
        variant: hir::DefId,
        owner: hir::DefId,
        arguments: &[GenericArg],
    ) -> Result<Vec<TyId>, Error> {
        let ty = self.program.definitions[variant].ty;
        let fields = match self.program.types.get(ty) {
            Ty::Function { parameters, .. } => parameters.clone(),
            _ => Vec::new(),
        };
        self.substituted(&fields, owner, arguments)
    }
    fn check_size(&self, ty: TyId, size: u64) -> Result<(), Error> {
        if size > self.table.target.maximum_object_size {
            return Err(Error::new(
                ty,
                "layout exceeds the target's maximum object size",
            ));
        }
        Ok(())
    }
}

struct Aggregate {
    fields: Vec<Field>,
    size: u64,
    alignment: u64,
    c_compatible: bool,
}

fn scalar(ty: TyId, size: u64, alignment: u64, c_compatible: bool) -> Layout {
    Layout {
        ty,
        size,
        alignment,
        c_compatible,
        kind: Kind::Scalar,
    }
}
fn align_up(ty: TyId, size: u64, alignment: u64) -> Result<u64, Error> {
    size.checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or_else(|| Error::new(ty, "alignment padding overflows target size"))
}
fn tag_bytes(maximum: Option<u64>, c: bool) -> Result<u8, Error> {
    if maximum.is_none() && c {
        return Err(Error::new(
            TyId::ERROR,
            "an empty enum has no C representation",
        ));
    }
    let Some(maximum) = maximum else {
        return Ok(0);
    };
    if c {
        if maximum > u64::from(u32::MAX) {
            return Err(Error::new(
                TyId::ERROR,
                "repr(C) enum tag exceeds its 32-bit representation",
            ));
        }
        return Ok(4);
    }
    Ok(if maximum <= u64::from(u8::MAX) {
        1
    } else if maximum <= u64::from(u16::MAX) {
        2
    } else if maximum <= u64::from(u32::MAX) {
        4
    } else {
        8
    })
}
