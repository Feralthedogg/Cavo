use crate::{
    hir,
    types::{Ty, TyId},
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Shape {
    pub raw_pointers: bool,
    pub references: bool,
    pub may_drop: bool,
}

pub(crate) struct Structural {
    values: Vec<Option<Shape>>,
    fields: Vec<Option<Vec<TyId>>>,
    record_fields: Vec<Option<Vec<TyId>>>,
    enum_fields: Vec<Option<(hir::DefId, Vec<TyId>)>>,
    variant_ranges: Vec<Option<(hir::DefId, std::ops::Range<usize>)>>,
    enum_variants: Vec<Option<Vec<hir::DefId>>>,
    remaining: usize,
    user_drop: Vec<bool>,
    unions: std::collections::HashSet<TyId>,
}

impl Structural {
    pub fn compute(program: &mut hir::Program) -> Self {
        let (fields, variant_ranges) = declared_fields(program);
        let mut enum_variants = vec![None; program.definitions.len()];
        for enumeration in &program.enums {
            enum_variants[enumeration.definition.0 as usize] = Some(enumeration.variants.clone());
        }
        let mut properties = Self {
            values: Vec::new(),
            fields,
            record_fields: Vec::new(),
            enum_fields: Vec::new(),
            variant_ranges,
            enum_variants,
            remaining: 200_000,
            user_drop: Vec::new(),
            unions: Default::default(),
        };
        let mut active = Vec::new();
        let original_types = program.types.values().len();
        for index in 0..original_types {
            properties.resolve(TyId(index as u32), program, &mut active);
        }
        properties
    }

    pub fn get(&self, ty: TyId) -> Shape {
        self.values
            .get(ty.0 as usize)
            .copied()
            .flatten()
            .unwrap_or(Shape {
                raw_pointers: false,
                references: true,
                may_drop: true,
            })
    }

    pub fn user_drop(&self, ty: TyId) -> bool {
        self.user_drop.get(ty.0 as usize).copied().unwrap_or(false)
    }
    pub fn union(&self, ty: TyId) -> bool {
        self.unions.contains(&ty)
    }

    pub fn record_field(&self, ty: TyId, index: u32, program: &hir::Program) -> bool {
        let Ty::Named { definition, .. } = program.types.get(ty) else {
            return false;
        };
        program.definitions[definition].kind == hir::DefinitionKind::Record
            && self.fields[definition.0 as usize]
                .as_ref()
                .is_some_and(|fields| (index as usize) < fields.len())
    }

    pub fn fields(&self, ty: TyId) -> Option<&[TyId]> {
        self.record_fields.get(ty.0 as usize)?.as_deref()
    }

    pub fn variant_fields(&self, ty: TyId, variant: hir::DefId) -> Option<&[TyId]> {
        let (owner, range) = self.variant_ranges.get(variant.0 as usize)?.as_ref()?;
        let (actual, fields) = self.enum_fields.get(ty.0 as usize)?.as_ref()?;
        (*owner == *actual).then(|| &fields[range.clone()])
    }

    pub fn enum_variants(&self, ty: TyId) -> Option<&[hir::DefId]> {
        let (definition, _) = self.enum_fields.get(ty.0 as usize)?.as_ref()?;
        self.enum_variants.get(definition.0 as usize)?.as_deref()
    }

    fn resolve(&mut self, ty: TyId, program: &mut hir::Program, active: &mut Vec<TyId>) -> Shape {
        if self.remaining == 0 || active.len() >= 64 || active.contains(&ty) {
            return Shape {
                raw_pointers: false,
                references: true,
                may_drop: true,
            };
        }
        if let Some(Some(value)) = self.values.get(ty.0 as usize) {
            return *value;
        }
        self.remaining -= 1;
        active.push(ty);
        let result = match program.types.get(ty).clone() {
            Ty::Void
            | Ty::Bool
            | Ty::Char
            | Ty::Integer { .. }
            | Ty::Float { .. }
            | Ty::Function { .. }
            | Ty::ForAll { .. } => Shape {
                raw_pointers: false,
                references: false,
                may_drop: false,
            },
            Ty::Pointer { .. } => Shape {
                raw_pointers: true,
                references: false,
                may_drop: false,
            },
            Ty::Reference { .. } => Shape {
                raw_pointers: false,
                references: true,
                may_drop: false,
            },
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                self.resolve(inner, program, active)
            }
            Ty::Named {
                definition,
                arguments,
            } => {
                let Some(fields) = self.fields[definition.0 as usize].clone() else {
                    active.pop();
                    return Shape {
                        raw_pointers: false,
                        references: true,
                        may_drop: true,
                    };
                };
                let mut result = Shape {
                    raw_pointers: false,
                    references: false,
                    may_drop: false,
                };
                let user_drop = hir::traits::has_drop(program, ty);
                self.user_drop.resize(program.types.values().len(), false);
                self.user_drop[ty.0 as usize] = user_drop;
                let mut resolved_fields = Vec::with_capacity(fields.len());
                for field in fields {
                    if program.types.nesting(field) > 128 {
                        result.references = true;
                        result.may_drop = true;
                        resolved_fields.push(field);
                        continue;
                    }
                    let field = program.types.substitute(field, definition, &arguments);
                    resolved_fields.push(field);
                    let property = self.resolve(field, program, active);
                    result.references |= property.references;
                    result.raw_pointers |= property.raw_pointers;
                    result.may_drop |= property.may_drop;
                }
                if matches!(
                    program.definitions[definition].kind,
                    hir::DefinitionKind::Record | hir::DefinitionKind::Union
                ) {
                    self.record_fields
                        .resize(program.types.values().len(), None);
                    self.record_fields[ty.0 as usize] = Some(resolved_fields);
                } else if program.definitions[definition].kind == hir::DefinitionKind::Enum {
                    self.enum_fields.resize(program.types.values().len(), None);
                    self.enum_fields[ty.0 as usize] = Some((definition, resolved_fields));
                }
                if program.definitions[definition].kind == hir::DefinitionKind::Union {
                    self.unions.insert(ty);
                }
                if user_drop {
                    result.may_drop = true;
                }
                if crate::tasks::task_arguments(program, ty).is_some() {
                    self.record_fields[ty.0 as usize] = None;
                    result.references = true;
                    result.may_drop = true;
                }
                result
            }
            Ty::Parameter { owner, index } => Shape {
                raw_pointers: false,
                references: true,
                may_drop: !hir::traits::parameter_has_role(
                    program,
                    owner,
                    index,
                    hir::traits::LanguageItem::Copy,
                ),
            },
            Ty::Error | Ty::Str | Ty::Dynamic { .. } => Shape {
                raw_pointers: false,
                references: true,
                may_drop: true,
            },
        };
        active.pop();
        self.values.resize(program.types.values().len(), None);
        self.values[ty.0 as usize] = Some(result);
        result
    }
}

type DeclaredFields = Vec<Option<Vec<TyId>>>;
type VariantRanges = Vec<Option<(hir::DefId, std::ops::Range<usize>)>>;

fn declared_fields(program: &hir::Program) -> (DeclaredFields, VariantRanges) {
    let mut fields = vec![None; program.definitions.len()];
    let mut variants = vec![None; program.definitions.len()];
    for record in &program.records {
        fields[record.definition.0 as usize] =
            Some(record.fields.iter().map(|field| field.ty).collect());
    }
    for enumeration in &program.enums {
        let mut payloads = Vec::new();
        for &variant in &enumeration.variants {
            let start = payloads.len();
            if let Ty::Function { parameters, .. } =
                program.types.get(program.definitions[variant].ty)
            {
                payloads.extend(parameters);
            }
            variants[variant.0 as usize] = Some((enumeration.definition, start..payloads.len()));
        }
        fields[enumeration.definition.0 as usize] = Some(payloads);
    }
    (fields, variants)
}
