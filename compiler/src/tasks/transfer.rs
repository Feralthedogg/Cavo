//! Auto traits are structural obligations, not promises supplied by their names.
use crate::{
    hir::{self, traits::LanguageItem},
    local::properties::Properties,
    types::{Ty, TyId},
};
use std::{collections::HashSet, fmt};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Property {
    Send,
    Sync,
    TaskTransfer,
    SuspendSafe,
}

impl Property {
    pub(crate) fn from_role(role: LanguageItem) -> Option<Self> {
        Some(match role {
            LanguageItem::Send => Self::Send,
            LanguageItem::Sync => Self::Sync,
            LanguageItem::TaskTransfer => Self::TaskTransfer,
            LanguageItem::SuspendSafe => Self::SuspendSafe,
            _ => return None,
        })
    }
    pub(crate) fn role(self) -> LanguageItem {
        match self {
            Self::Send => LanguageItem::Send,
            Self::Sync => LanguageItem::Sync,
            Self::TaskTransfer => LanguageItem::TaskTransfer,
            Self::SuspendSafe => LanguageItem::SuspendSafe,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailureKind {
    MissingBound,
    Identity,
    RawPointer,
    Opaque,
    Resource,
}

#[derive(Debug)]
pub(crate) struct Failure {
    pub kind: FailureKind,
    detail: String,
}
impl Failure {
    fn new(kind: FailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }
}
impl fmt::Display for Failure {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        out.write_str(&self.detail)
    }
}

pub(crate) fn check(
    program: &hir::Program,
    properties: &Properties,
    ty: TyId,
    property: Property,
) -> Result<(), Failure> {
    establish(program, properties, ty, property).map(|_| ())
}

pub(crate) fn establish(
    program: &hir::Program,
    properties: &Properties,
    ty: TyId,
    property: Property,
) -> Result<std::collections::BTreeSet<hir::DefId>, Failure> {
    Checker {
        program,
        properties,
        pending: vec![(ty, property)],
        visited: HashSet::new(),
        trusted: Default::default(),
    }
    .run()
}

struct Checker<'a> {
    program: &'a hir::Program,
    properties: &'a Properties,
    pending: Vec<(TyId, Property)>,
    visited: HashSet<(TyId, Property)>,
    trusted: std::collections::BTreeSet<hir::DefId>,
}
impl Checker<'_> {
    fn run(mut self) -> Result<std::collections::BTreeSet<hir::DefId>, Failure> {
        while let Some((ty, property)) = self.pending.pop() {
            if !self.visited.insert((ty, property)) {
                continue;
            }
            if self.visited.len() > 4096 {
                return Err(Failure::new(
                    FailureKind::Resource,
                    "task transfer analysis exceeded its type budget",
                ));
            }
            self.step(ty, property)?;
        }
        Ok(self.trusted)
    }

    fn step(&mut self, ty: TyId, property: Property) -> Result<(), Failure> {
        match self.program.types.get(ty) {
            Ty::Void
            | Ty::Bool
            | Ty::Char
            | Ty::Integer { .. }
            | Ty::Float { .. }
            | Ty::Function { .. }
            | Ty::ForAll { .. }
            | Ty::Str => {}
            Ty::Reference { mutable, inner, .. } => self.reference(*inner, *mutable, property),
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                self.pending.push((*inner, property))
            }
            Ty::Pointer { .. } => {
                return Err(Failure::new(
                    FailureKind::RawPointer,
                    "raw addresses need an owning wrapper and an explicit trusted transfer contract",
                ));
            }
            Ty::Parameter { owner, index } => {
                if !hir::traits::parameter_has_role(self.program, *owner, *index, property.role()) {
                    return Err(Failure::new(
                        FailureKind::MissingBound,
                        format!("type parameter requires the {property:?} bound"),
                    ));
                }
            }
            Ty::Named { definition, .. } => self.nominal(ty, *definition, property)?,
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => self.dynamic(*trait_definition, arguments, property)?,
            _ => {
                return Err(Failure::new(
                    FailureKind::Opaque,
                    "the opaque type's transfer representation is not established",
                ));
            }
        }
        Ok(())
    }

    fn reference(&mut self, inner: TyId, mutable: bool, property: Property) {
        if property == Property::TaskTransfer {
            self.pending.push((inner, Property::TaskTransfer));
        }
        let inner_property = if matches!(property, Property::Send | Property::TaskTransfer) {
            if mutable {
                Property::Send
            } else {
                Property::Sync
            }
        } else {
            property
        };
        self.pending.push((inner, inner_property));
    }

    fn nominal(
        &mut self,
        ty: TyId,
        definition: hir::DefId,
        property: Property,
    ) -> Result<(), Failure> {
        if self
            .program
            .tasks
            .forbidden
            .get(&definition)
            .is_some_and(|items| items.contains(&property))
        {
            return Err(Failure::new(
                FailureKind::Identity,
                format!("the type's declared identity forbids {property:?}"),
            ));
        }
        if crate::tasks::task_arguments(self.program, ty).is_some() {
            return if property == Property::TaskTransfer {
                Err(Failure::new(
                    FailureKind::Identity,
                    "a task observation belongs to its original scope and task",
                ))
            } else {
                Ok(())
            };
        }
        if let Some(trait_) = self
            .program
            .traits
            .iter()
            .find(|t| t.language_item == Some(property.role()))
        {
            let reference = hir::traits::TraitRef {
                definition: trait_.definition,
                arguments: Vec::new(),
            };
            if let Ok(Some((index, _))) = hir::traits::select_trait(self.program, ty, &reference) {
                let implementation = self.program.implementations[index].definition;
                if self.program.tasks.trusted.contains_key(&implementation) {
                    self.trusted.insert(implementation);
                    return Ok(());
                }
            }
        }
        if let Some(fields) = self.properties.fields(ty) {
            self.pending.extend(fields.iter().map(|&ty| (ty, property)));
        } else if let Some(variants) = self.properties.enum_variants(ty) {
            for &variant in variants {
                let fields = self.properties.variant_fields(ty, variant).ok_or_else(|| {
                    Failure::new(FailureKind::Opaque, "enum transfer shape is unavailable")
                })?;
                self.pending.extend(fields.iter().map(|&ty| (ty, property)));
            }
        } else {
            return Err(Failure::new(
                FailureKind::Opaque,
                "the owning type's transfer shape is unavailable",
            ));
        }
        Ok(())
    }

    fn dynamic(
        &self,
        definition: hir::DefId,
        _arguments: &[crate::types::GenericArg],
        property: Property,
    ) -> Result<(), Failure> {
        let mut pending = vec![definition];
        let mut visited = HashSet::new();
        while let Some(definition) = pending.pop() {
            if !visited.insert(definition) {
                continue;
            }
            if visited.len() > 4096 {
                return Err(Failure::new(
                    FailureKind::Resource,
                    "dynamic transfer trait budget exceeded",
                ));
            }
            let Some(item) = self
                .program
                .traits
                .iter()
                .find(|item| item.definition == definition)
            else {
                continue;
            };
            if item.language_item == Some(property.role()) {
                return Ok(());
            }
            pending.extend(item.supertraits.iter().map(|parent| parent.definition));
        }
        Err(Failure::new(
            FailureKind::Opaque,
            format!("dynamic trait requires a declared {property:?} supertrait"),
        ))
    }
}
