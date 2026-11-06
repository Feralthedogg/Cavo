use super::*;
use crate::types::{ConstKind, ConstValue};

pub(super) struct Glues<'a> {
    pub(super) hir: &'a mut hir::Program,
    pub(super) properties: &'a Properties,
    pub(super) entries: Vec<Glue>,
    pub(super) indices: HashMap<TyId, GlueId>,
    pub(super) structural: HashMap<TyId, GlueId>,
    pub(super) destructors: HashMap<TyId, GlueId>,
    pub(super) tails: HashMap<TyId, GlueId>,
}
impl Glues<'_> {
    pub(super) fn resolve(&mut self, ty: TyId, depth: usize) -> Result<GlueId, Error> {
        if let Some(&id) = self.indices.get(&ty) {
            return Ok(id);
        }
        self.check_limit(depth)?;
        let structural = self.structure(ty, depth + 1)?;
        let kind = if let Some(destructor) = self.destructor_selection(ty)? {
            GlueKind::User {
                concrete: concrete_arguments(self.hir, &destructor.type_arguments),
                destructor,
                fields: structural,
            }
        } else {
            self.indices.insert(ty, structural);
            return Ok(structural);
        };
        let id = self.insert(ty, kind)?;
        self.indices.insert(ty, id);
        Ok(id)
    }
    pub(super) fn destructor(&mut self, ty: TyId) -> Result<Option<GlueId>, Error> {
        if let Some(&id) = self.destructors.get(&ty) {
            return Ok(Some(id));
        }
        let Some(destructor) = self.destructor_selection(ty)? else {
            return Ok(None);
        };
        let concrete = concrete_arguments(self.hir, &destructor.type_arguments);
        let id = self.insert(
            ty,
            GlueKind::Destructor {
                destructor,
                concrete,
            },
        )?;
        self.destructors.insert(ty, id);
        Ok(Some(id))
    }
    fn destructor_selection(
        &mut self,
        ty: TyId,
    ) -> Result<Option<hir::traits::MethodSelection>, Error> {
        let selected =
            hir::traits::select_drop(self.hir, ty).map_err(|error| Error(error.to_string()))?;
        if let Some(selected) = &selected {
            hir::traits::check_bounds(self.hir, selected.definition, &selected.type_arguments)
                .map_err(|error| Error(error.to_string()))?;
        }
        Ok(selected)
    }
    pub(super) fn tail(&mut self, ty: TyId) -> Result<GlueId, Error> {
        if let Some(&id) = self.tails.get(&ty) {
            return Ok(id);
        }
        let (inner, count) = match self.hir.types.get(ty).clone() {
            Ty::Array { inner, length } => (inner, ArrayLength::Concrete(length)),
            Ty::SymbolicArray { inner, length } => (inner, ArrayLength::Deferred(length)),
            _ => return Err(Error("array iterator has no array ownership type".into())),
        };
        let element = self.resolve(inner, 0)?;
        let id = self.insert(ty, GlueKind::ArrayTail { element, count })?;
        self.tails.insert(ty, id);
        Ok(id)
    }
    fn structure(&mut self, ty: TyId, depth: usize) -> Result<GlueId, Error> {
        if let Some(&id) = self.structural.get(&ty) {
            return Ok(id);
        }
        self.check_limit(depth)?;
        let kind = self.structural_kind(ty, depth + 1)?;
        let id = self.insert(ty, kind)?;
        self.structural.insert(ty, id);
        Ok(id)
    }
    fn structural_kind(&mut self, ty: TyId, depth: usize) -> Result<GlueKind, Error> {
        if crate::tasks::task_arguments(self.hir, ty).is_some() {
            return Ok(GlueKind::TaskHandle);
        }
        if !self.properties.get(ty).may_drop {
            return Ok(GlueKind::Trivial);
        }
        match self.hir.types.get(ty).clone() {
            Ty::Parameter { owner, index } => Ok(GlueKind::Parameter { owner, index }),
            Ty::Array { inner, length } => Ok(GlueKind::Array {
                element: self.resolve(inner, depth)?,
                count: length,
            }),
            Ty::SymbolicArray { inner, length } => Ok(GlueKind::SymbolicArray {
                element: self.resolve(inner, depth)?,
                count: length,
            }),
            Ty::Named {
                definition,
                arguments,
            } => self.named(ty, definition, &arguments, depth),
            _ => Ok(GlueKind::Manual),
        }
    }
    fn named(
        &mut self,
        ty: TyId,
        definition: hir::DefId,
        arguments: &[GenericArg],
        depth: usize,
    ) -> Result<GlueKind, Error> {
        if let Some(fields) = self.properties.fields(ty) {
            let mut plans = Vec::with_capacity(fields.len());
            for (index, &field) in fields.iter().enumerate() {
                plans.push(FieldGlue {
                    field: index as u32,
                    glue: self.resolve(field, depth)?,
                });
            }
            return Ok(GlueKind::Record(plans));
        }
        let Some(enumeration) = self
            .hir
            .enums
            .iter()
            .find(|enumeration| enumeration.definition == definition)
        else {
            return Ok(GlueKind::Manual);
        };
        let variants = enumeration.variants.clone();
        let mut plans = Vec::with_capacity(variants.len());
        for variant in variants {
            plans.push(self.variant(variant, definition, arguments, depth)?);
        }
        Ok(GlueKind::Enum(plans))
    }
    fn variant(
        &mut self,
        variant: hir::DefId,
        owner: hir::DefId,
        arguments: &[GenericArg],
        depth: usize,
    ) -> Result<VariantGlue, Error> {
        let ty = self.hir.definitions[variant].ty;
        let fields = match self.hir.types.get(ty) {
            Ty::Function { parameters, .. } => parameters.clone(),
            _ => Vec::new(),
        };
        let mut plans = Vec::with_capacity(fields.len());
        for field in fields {
            let field = self
                .hir
                .types
                .substitute_generics(field, owner, arguments)
                .map_err(|error| Error(error.to_string()))?;
            plans.push(self.resolve(field, depth)?);
        }
        Ok(VariantGlue {
            variant,
            fields: plans,
        })
    }
    fn insert(&mut self, ty: TyId, kind: GlueKind) -> Result<GlueId, Error> {
        self.check_limit(0)?;
        let id = GlueId(self.entries.len() as u32);
        self.entries.push(Glue { ty, kind });
        Ok(id)
    }
    fn check_limit(&self, depth: usize) -> Result<(), Error> {
        if depth >= 64 || self.entries.len() >= LIMIT {
            return Err(Error("drop glue resource limit exceeded".into()));
        }
        Ok(())
    }
}

fn concrete_arguments(program: &hir::Program, arguments: &[GenericArg]) -> bool {
    let mut pending = Vec::new();
    if !add_arguments(program, arguments, &mut pending) {
        return false;
    }
    let mut seen = HashSet::new();
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) {
            continue;
        }
        if seen.len() >= LIMIT {
            return false;
        }
        match program.types.get(ty) {
            Ty::Error | Ty::Parameter { .. } | Ty::SymbolicArray { .. } => return false,
            Ty::Reference { inner, .. }
            | Ty::Pointer { inner, .. }
            | Ty::Array { inner, .. }
            | Ty::Slice(inner)
            | Ty::ForAll { inner, .. } => pending.push(*inner),
            Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. }
                if !add_arguments(program, arguments, &mut pending) =>
            {
                return false;
            }
            Ty::Named { .. } | Ty::Dynamic { .. } => {}
            Ty::Function { parameters, result } => {
                pending.extend(parameters);
                pending.push(*result);
            }
            _ => {}
        }
    }
    true
}
fn add_arguments(
    program: &hir::Program,
    arguments: &[GenericArg],
    pending: &mut Vec<TyId>,
) -> bool {
    for argument in arguments {
        match argument {
            GenericArg::Type(ty) => pending.push(*ty),
            GenericArg::Const(value) => {
                if !matches!(
                    program.types.const_term(*value).kind,
                    ConstKind::Value(ConstValue::Usize(_))
                ) {
                    return false;
                }
            }
            GenericArg::Lifetime(_) => {}
        }
    }
    true
}
