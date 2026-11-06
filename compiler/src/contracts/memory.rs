//! Finite memory facts. Joins keep only guarantees present on every incoming
//! edge; a forgotten fact is Unknown, never a definite-free witness.

use super::*;
use crate::mir::{LocalId, Place, Projection};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AllocationId {
    Local(u32),
    Input(u32),
    Heap(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Truth {
    Yes,
    No,
    Unknown,
}

impl Truth {
    pub fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::Unknown }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Basis {
    pub event: EventId,
    pub span: Span,
    pub trust: BTreeSet<Trust>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Allocation {
    pub initialized_type: Option<crate::types::TyId>,
    pub raw_touched: bool,
    pub live: Truth,
    pub initialized: Truth,
    pub initialized_ranges: BTreeSet<(u64, u64, u32)>,
    pub uninitialized_ranges: BTreeSet<(u64, u64)>,
    pub extent: Option<u64>,
    pub alignment: u64,
    pub owned: Truth,
    pub basis: Basis,
    pub invalidation: Option<Basis>,
    pub active_union: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Pointer {
    pub owned: Truth,
    pub ancestors: BTreeSet<EventId>,
    pub raw: bool,
    pub allocation: AllocationId,
    pub offset: Option<u64>,
    pub readable: Truth,
    pub writable: Truth,
    pub unaligned: bool,
    pub expired: bool,
    pub basis: Basis,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Value {
    pub opaque_references: bool,
    pub active_union: Option<u32>,
    pub trust: BTreeSet<Trust>,
    pub function: Option<hir::DefId>,
    pub pointer: Option<Pointer>,
    pub integer: Option<u64>,
    pub boolean: Option<bool>,
    pub fields: BTreeMap<Vec<u32>, Value>,
}

impl Value {
    pub fn aggregate(fields: BTreeMap<Vec<u32>, Value>, active_union: Option<u32>) -> Self {
        let trust = fields
            .values()
            .flat_map(|value| value.trust.iter().cloned())
            .collect();
        Self {
            fields,
            active_union,
            trust,
            ..Self::default()
        }
    }
    pub fn join(&mut self, other: &Self) {
        self.opaque_references |= other.opaque_references;
        if self.active_union != other.active_union {
            self.active_union = None;
        }
        self.trust.extend(other.trust.iter().cloned());
        if self.function != other.function {
            self.function = None;
        }
        if self.pointer != other.pointer {
            self.pointer = None;
        }
        if self.integer != other.integer {
            self.integer = None;
        }
        if self.boolean != other.boolean {
            self.boolean = None;
        }
        self.fields.retain(|path, value| {
            let Some(other) = other.fields.get(path) else {
                return false;
            };
            value.join(other);
            true
        });
    }

    pub fn havoc(&mut self) {
        self.opaque_references |= self.pointer.as_ref().is_some_and(|pointer| !pointer.raw);
        self.pointer = None;
        self.function = None;
        self.integer = None;
        self.boolean = None;
        self.active_union = None;
        for field in self.fields.values_mut() {
            field.havoc();
        }
    }

    pub fn expire(&mut self, allocation: AllocationId) {
        if let Some(pointer) = &mut self.pointer
            && pointer.allocation == allocation
        {
            pointer.expired = true;
        }
        for value in self.fields.values_mut() {
            value.expire(allocation);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct State {
    pub places: Vec<Option<CapturedPlace>>,
    pub scopes: Vec<crate::mir::ScopeId>,
    pub values: Vec<Value>,
    pub allocations: BTreeMap<AllocationId, Allocation>,
    pub assumptions: Vec<Fact>,
    pub contents: BTreeMap<(AllocationId, u64), Value>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FieldStep {
    Field(u32),
    UnionField(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CapturedPlace {
    Local {
        local: LocalId,
        steps: Vec<FieldStep>,
    },
    Indirect {
        pointer: Pointer,
        steps: Vec<FieldStep>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Fact {
    pub permissions: Freshness,
    pub contents: Freshness,
    pub scope: crate::mir::ScopeId,
    pub predicate: MemoryPredicate,
    pub value: Value,
    pub count: Option<u64>,
    pub ty: crate::types::TyId,
    pub basis: Basis,
    pub operands: Vec<Value>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Freshness {
    Current,
    Invalidated,
}

impl State {
    pub fn new_reference(&mut self) {
        for fact in &mut self.assumptions {
            fact.permissions = Freshness::Invalidated;
        }
    }
    pub fn memory_write(&mut self) {
        for fact in &mut self.assumptions {
            fact.contents = Freshness::Invalidated;
        }
    }
    pub fn memory_free(&mut self) {
        self.assumptions.retain(|fact| {
            matches!(
                fact.predicate,
                MemoryPredicate::Scalar | MemoryPredicate::NoRetain | MemoryPredicate::NoCallback
            )
        });
    }
    pub fn new(locals: usize) -> Self {
        Self {
            places: vec![None; locals],
            scopes: Vec::new(),
            values: vec![Value::default(); locals],
            allocations: BTreeMap::new(),
            assumptions: Vec::new(),
            contents: BTreeMap::new(),
        }
    }

    pub fn merge(&mut self, other: &Self) -> bool {
        let old = self.clone();
        for (place, other) in self.places.iter_mut().zip(&other.places) {
            if place != other {
                *place = None;
            }
        }
        for (value, other) in self.values.iter_mut().zip(&other.values) {
            value.join(other);
        }
        self.allocations.retain(|id, allocation| {
            let Some(right) = other.allocations.get(id) else {
                return false;
            };
            allocation.live = allocation.live.join(right.live);
            if allocation.initialized_type != right.initialized_type {
                allocation.initialized_type = None;
            }
            allocation.raw_touched |= right.raw_touched;
            allocation.initialized = allocation.initialized.join(right.initialized);
            allocation
                .initialized_ranges
                .retain(|range| right.initialized_ranges.contains(range));
            allocation
                .uninitialized_ranges
                .retain(|range| right.uninitialized_ranges.contains(range));
            allocation.owned = allocation.owned.join(right.owned);
            if allocation.extent != right.extent {
                allocation.extent = None;
            }
            if allocation.active_union != right.active_union {
                allocation.active_union = None;
            }
            if allocation.invalidation != right.invalidation {
                allocation.invalidation = None;
            }
            allocation
                .basis
                .trust
                .extend(right.basis.trust.iter().cloned());
            true
        });
        self.assumptions
            .retain(|fact| other.assumptions.contains(fact));
        self.contents.retain(|key, value| {
            let Some(right) = other.contents.get(key) else {
                return false;
            };
            value.join(right);
            true
        });
        *self != old
    }

    pub fn expire(&mut self, id: AllocationId, basis: Basis) {
        if let Some(allocation) = self.allocations.get_mut(&id) {
            allocation.live = Truth::No;
            allocation.owned = Truth::No;
            allocation.invalidation = Some(basis);
        }
        for value in &mut self.values {
            value.expire(id);
        }
        for value in self.contents.values_mut() {
            value.expire(id);
        }
        self.assumptions.retain(|fact| {
            fact.value
                .pointer
                .as_ref()
                .is_none_or(|p| p.allocation != id)
        });
    }

    pub fn local(&self, local: LocalId) -> &Value {
        &self.values[local.0 as usize]
    }
    pub fn local_mut(&mut self, local: LocalId) -> &mut Value {
        &mut self.values[local.0 as usize]
    }
    pub fn local_storage(&mut self, local: LocalId) -> (&mut Value, Option<&mut Allocation>) {
        (
            &mut self.values[local.0 as usize],
            self.allocations.get_mut(&AllocationId::Local(local.0)),
        )
    }

    pub fn read(&self, place: &Place) -> Value {
        if place.projection.first() == Some(&Projection::Deref)
            && let Some(capture) = &self.places[place.local.0 as usize]
        {
            return self.project(self.read_capture(capture), &place.projection[1..]);
        }
        let mut value = self.local(place.local).clone();
        value = self.project(value, &place.projection);
        value
    }

    pub fn read_capture(&self, place: &CapturedPlace) -> Value {
        let (mut value, steps) = match place {
            CapturedPlace::Local { local, steps } => (self.local(*local).clone(), steps),
            CapturedPlace::Indirect { pointer, steps } => {
                let value = match pointer.allocation {
                    AllocationId::Local(local) if pointer.offset == Some(0) => {
                        self.values[local as usize].clone()
                    }
                    _ => pointer
                        .offset
                        .and_then(|offset| self.contents.get(&(pointer.allocation, offset)))
                        .cloned()
                        .unwrap_or_default(),
                };
                (value, steps)
            }
        };
        if let CapturedPlace::Indirect { pointer, .. } = place {
            value.trust.extend(pointer.basis.trust.iter().cloned());
        }
        for step in steps {
            let inherited = value.trust.clone();
            let (FieldStep::Field(field) | FieldStep::UnionField(field)) = step;
            value = value.fields.get(&vec![*field]).cloned().unwrap_or_default();
            value.trust.extend(inherited);
        }
        value
    }

    fn project(&self, mut value: Value, projections: &[Projection]) -> Value {
        for projection in projections {
            let mut inherited = value.trust.clone();
            if let Some(pointer) = &value.pointer {
                inherited.extend(pointer.basis.trust.iter().cloned());
            }
            match projection {
                Projection::Field(field) => {
                    value = value.fields.get(&vec![*field]).cloned().unwrap_or_default()
                }
                Projection::Downcast(_) => {}
                Projection::Deref => {
                    value = value
                        .pointer
                        .as_ref()
                        .and_then(|p| {
                            if p.expired {
                                return None;
                            }
                            match p.allocation {
                                AllocationId::Local(local) if p.offset == Some(0) => {
                                    self.values.get(local as usize)
                                }
                                _ => p
                                    .offset
                                    .and_then(|offset| self.contents.get(&(p.allocation, offset))),
                            }
                        })
                        .cloned()
                        .unwrap_or_default();
                }
                Projection::Index(index) => {
                    let key = self
                        .local(*index)
                        .integer
                        .and_then(|value| u32::try_from(value).ok());
                    value = key
                        .and_then(|key| value.fields.get(&vec![key]).cloned())
                        .unwrap_or_default();
                }
            }
            value.trust.extend(inherited);
        }
        value
    }
}
