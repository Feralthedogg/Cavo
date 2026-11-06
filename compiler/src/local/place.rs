use super::{cfg, properties::Properties};
use crate::{
    hir::{self, LocalId},
    types::{Ty, TyId},
};
use std::{collections::HashMap, ops::Range};

const MAX_PLACES: usize = 65_536;
const MAX_DEPTH: u16 = 128;

/// Function-local identity, meaningful only inside its FunctionReport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlaceId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldProjection {
    pub base: PlaceId,
    pub index: u32,
}

/// A root local or a resolved record field, without a runtime address/layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Place {
    pub owner: LocalId,
    pub projection: Option<FieldProjection>,
    /// Abstract memory reached through a reference input, not its stack slot.
    pub input: Option<PlaceId>,
}

pub(super) struct Places {
    values: Vec<Place>,
    depths: Vec<u16>,
    fields: HashMap<(PlaceId, u32), PlaceId>,
    types: Vec<TyId>,
    children: Vec<Vec<PlaceId>>,
    ranges: Vec<Range<usize>>,
    leaves: Vec<PlaceId>,
    frozen: bool,
    roots: Vec<PlaceId>,
    inputs: HashMap<PlaceId, PlaceId>,
    owned_cells: Vec<Vec<usize>>,
}

impl Places {
    pub fn new(slots: usize) -> Self {
        Self {
            values: (0..slots)
                .map(|index| Place {
                    owner: LocalId(index as u32),
                    projection: None,
                    input: None,
                })
                .collect(),
            depths: vec![0; slots],
            fields: HashMap::new(),
            types: vec![TyId::ERROR; slots],
            children: vec![Vec::new(); slots],
            ranges: vec![0..0; slots],
            leaves: Vec::new(),
            frozen: false,
            roots: (0..slots).map(|i| PlaceId(i as u32)).collect(),
            inputs: HashMap::new(),
            owned_cells: vec![Vec::new(); slots],
        }
    }

    pub fn build(
        function: &hir::Function,
        graph: &cfg::Graph,
        properties: &Properties,
        program: &hir::Program,
    ) -> Option<Self> {
        let mut places = Self::new(graph.slots);
        for (index, local) in function.locals.iter().enumerate() {
            places.types[index] = local.ty;
        }
        for block in &graph.blocks {
            for operation in &block.operations {
                if let cfg::Operation::IterationStart { slot, value, .. } = *operation {
                    places.types[slot.0 as usize] = function.expressions[value.0 as usize].ty;
                }
            }
        }
        let mut active = Vec::new();
        for index in 0..graph.slots {
            places.expand(PlaceId(index as u32), properties, &mut active)?;
        }
        for index in 0..graph.slots {
            places.number_leaves(PlaceId(index as u32));
        }
        for &parameter in &function.parameters {
            let mut references: Vec<_> = places
                .leaves(Self::root(parameter))
                .map(|i| places.leaf(i))
                .collect();
            let mut cursor = 0;
            while let Some(&source) = references.get(cursor) {
                cursor += 1;
                if let Ty::Reference { inner, .. } = *program.types.get(places.ty(source)) {
                    // Recursive indirections stay opaque. Do not manufacture an
                    // infinite collection of apparently disjoint allocations.
                    let mut ancestor = source;
                    let mut depth = 0;
                    let mut recursive = false;
                    while let Some(parent) = places.input_source(ancestor) {
                        depth += 1;
                        if let Ty::Reference {
                            inner: previous, ..
                        } = *program.types.get(places.ty(parent))
                            && previous == inner
                        {
                            recursive = true;
                            break;
                        }
                        ancestor = parent;
                    }
                    if recursive {
                        continue;
                    }
                    if depth >= MAX_DEPTH as usize {
                        return None;
                    }
                    if places.values.len() >= MAX_PLACES {
                        return None;
                    }
                    let root = PlaceId(places.values.len() as u32);
                    places.values.push(Place {
                        owner: places.owner(source),
                        projection: None,
                        input: Some(source),
                    });
                    places.depths.push(0);
                    places.types.push(inner);
                    places.children.push(Vec::new());
                    places.ranges.push(0..0);
                    places.roots.push(root);
                    places.inputs.insert(source, root);
                    places.expand(root, properties, &mut active)?;
                    places.number_leaves(root);
                    references.extend(places.leaves(root).map(|i| places.leaf(i)));
                }
            }
        }
        for (index, &place) in places.leaves.iter().enumerate() {
            let owner = places.owner(place).0 as usize;
            places.owned_cells[owner].push(index);
        }
        if graph
            .blocks
            .len()
            .saturating_mul(places.leaves.len().max(1))
            > 250_000
        {
            return None;
        }
        places.frozen = true;
        Some(places)
    }

    fn expand(
        &mut self,
        id: PlaceId,
        properties: &Properties,
        active: &mut Vec<TyId>,
    ) -> Option<()> {
        let ty = self.ty(id);
        if let Some(fields) = properties.fields(ty) {
            if active.contains(&ty) || active.len() >= MAX_DEPTH as usize {
                return None;
            }
            active.push(ty);
            for (index, &field_ty) in fields.iter().enumerate() {
                let field = self.field(id, index as u32)?;
                self.types[field.0 as usize] = field_ty;
                self.expand(field, properties, active)?;
            }
            active.pop();
        }
        Some(())
    }

    fn number_leaves(&mut self, id: PlaceId) {
        let start = self.leaves.len();
        if self.children[id.0 as usize].is_empty() {
            self.leaves.push(id);
        } else {
            for index in 0..self.children[id.0 as usize].len() {
                self.number_leaves(self.children[id.0 as usize][index]);
            }
        }
        self.ranges[id.0 as usize] = start..self.leaves.len();
    }

    pub fn leaf_count(&self) -> usize {
        self.leaves.len()
    }
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn leaves(&self, id: PlaceId) -> Range<usize> {
        self.ranges[id.0 as usize].clone()
    }
    pub fn leaf(&self, index: usize) -> PlaceId {
        self.leaves[index]
    }
    pub fn ty(&self, id: PlaceId) -> TyId {
        self.types[id.0 as usize]
    }
    pub fn parent(&self, id: PlaceId) -> Option<PlaceId> {
        self.values[id.0 as usize]
            .projection
            .map(|projection| projection.base)
    }
    pub fn children(&self, id: PlaceId) -> &[PlaceId] {
        &self.children[id.0 as usize]
    }
    pub fn input(&self, source: PlaceId) -> Option<PlaceId> {
        self.inputs.get(&source).copied()
    }
    pub fn input_source(&self, id: PlaceId) -> Option<PlaceId> {
        self.values[self.roots[id.0 as usize].0 as usize].input
    }
    pub fn owned_cells(&self, local: LocalId) -> &[usize] {
        &self.owned_cells[local.0 as usize]
    }
    pub fn region_path(&self, mut root: PlaceId, path: &[super::RegionStep]) -> Option<PlaceId> {
        for step in path {
            root = match *step {
                super::RegionStep::Field(index) => *self.fields.get(&(root, index))?,
                super::RegionStep::Deref => self.input(root)?,
            };
        }
        Some(root)
    }
    pub fn memory_path(&self, mut place: PlaceId) -> Option<(PlaceId, Vec<u32>)> {
        let mut fields = Vec::new();
        while let Some(projection) = self.values[place.0 as usize].projection {
            fields.push(projection.index);
            place = projection.base;
        }
        fields.reverse();
        Some((self.values[place.0 as usize].input?, fields))
    }
    pub fn projected(&self, mut place: PlaceId, fields: &[u32]) -> Option<PlaceId> {
        for &field in fields {
            place = *self.fields.get(&(place, field))?;
        }
        Some(place)
    }
    pub fn direct(
        &self,
        function: &hir::Function,
        program: &hir::Program,
        id: hir::ExprId,
    ) -> Option<(PlaceId, bool)> {
        self.direct_inner(function, program, id, 0)
    }

    fn direct_inner(
        &self,
        function: &hir::Function,
        program: &hir::Program,
        id: hir::ExprId,
        depth: usize,
    ) -> Option<(PlaceId, bool)> {
        if depth >= MAX_DEPTH as usize {
            return None;
        }
        match function.expressions[id.0 as usize].kind {
            hir::ExprKind::Local(local) => Some((Self::root(local), true)),
            hir::ExprKind::Group(inner) => self.direct_inner(function, program, inner, depth + 1),
            hir::ExprKind::Field { base, .. } | hir::ExprKind::Index { base, .. } => {
                if matches!(
                    program.types.get(function.expressions[base.0 as usize].ty),
                    Ty::Reference { .. }
                ) {
                    return None;
                }
                let (place, precise) = self.direct_inner(function, program, base, depth + 1)?;
                match function.expressions[id.0 as usize].kind {
                    hir::ExprKind::Field { index, .. } if precise => {
                        Some((*self.fields.get(&(place, index))?, true))
                    }
                    _ => Some((place, false)),
                }
            }
            _ => None,
        }
    }

    pub fn root(local: LocalId) -> PlaceId {
        PlaceId(local.0)
    }

    pub fn owner(&self, id: PlaceId) -> LocalId {
        self.values[id.0 as usize].owner
    }

    pub fn field(&mut self, base: PlaceId, index: u32) -> Option<PlaceId> {
        if let Some(&id) = self.fields.get(&(base, index)) {
            return Some(id);
        }
        let depth = self.depths[base.0 as usize];
        if self.frozen || self.values.len() >= MAX_PLACES || depth >= MAX_DEPTH {
            return None;
        }
        let id = PlaceId(self.values.len() as u32);
        self.values.push(Place {
            owner: self.owner(base),
            projection: Some(FieldProjection { base, index }),
            input: None,
        });
        self.depths.push(depth + 1);
        self.roots.push(self.roots[base.0 as usize]);
        self.types.push(TyId::ERROR);
        self.children.push(Vec::new());
        self.ranges.push(0..0);
        self.children[base.0 as usize].push(id);
        self.fields.insert((base, index), id);
        Some(id)
    }

    pub fn overlaps(&self, mut left: PlaceId, mut right: PlaceId) -> bool {
        if self.roots[left.0 as usize] != self.roots[right.0 as usize] {
            return false;
        }
        // Distinct record fields are disjoint; a parent overlaps every child.
        // Array/index uncertainty is coarsened before a field is interned.
        while self.depths[left.0 as usize] > self.depths[right.0 as usize] {
            left = self.values[left.0 as usize].projection.unwrap().base;
        }
        while self.depths[right.0 as usize] > self.depths[left.0 as usize] {
            right = self.values[right.0 as usize].projection.unwrap().base;
        }
        left == right
    }

    pub fn into_values(self) -> Vec<Place> {
        self.values
    }

    pub fn validate(values: &[Place], slots: usize) -> Result<(), hir::InvariantError> {
        let fail = || hir::InvariantError("invalid local place arena".into());
        if values.len() < slots || values.len() > MAX_PLACES {
            return Err(fail());
        }
        let mut depths = Vec::with_capacity(values.len());
        let mut fields = HashMap::new();
        let mut inputs = HashMap::new();
        let mut indirections = Vec::new();
        for (index, place) in values.iter().enumerate() {
            let depth = if index < slots {
                if place.owner != LocalId(index as u32)
                    || place.projection.is_some()
                    || place.input.is_some()
                {
                    return Err(fail());
                }
                0u16
            } else if let Some(source) = place.input {
                if place.projection.is_some()
                    || source.0 as usize >= index
                    || values[source.0 as usize].owner != place.owner
                    || inputs.insert(source, ()).is_some()
                {
                    return Err(fail());
                }
                0
            } else {
                let projection = place.projection.ok_or_else(fail)?;
                let parent = projection.base.0 as usize;
                if parent >= index
                    || values[parent].owner != place.owner
                    || fields
                        .insert((projection.base, projection.index), ())
                        .is_some()
                    || depths[parent] >= MAX_DEPTH
                {
                    return Err(fail());
                }
                depths[parent] + 1
            };
            depths.push(depth);
            let indirection = if let Some(source) = place.input {
                indirections[source.0 as usize] + 1u16
            } else if let Some(projection) = place.projection {
                indirections[projection.base.0 as usize]
            } else {
                0
            };
            if indirection > MAX_DEPTH {
                return Err(fail());
            }
            indirections.push(indirection);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlap_matches_a_prefix_model_for_nested_paths_and_different_owners() {
        let mut places = Places::new(2);
        let mut model = vec![(0, Vec::<u32>::new()), (1, Vec::new())];
        let mut ids = vec![PlaceId(0), PlaceId(1)];
        let mut current = vec![0, 1];
        for _ in 0..4 {
            let mut next = Vec::new();
            for parent in current {
                for field in 0..2 {
                    let id = places.field(ids[parent], field).unwrap();
                    let mut path = model[parent].1.clone();
                    path.push(field);
                    next.push(ids.len());
                    ids.push(id);
                    model.push((model[parent].0, path));
                }
            }
            current = next;
        }
        for (left, (owner, path)) in model.iter().enumerate() {
            for (right, (other_owner, other_path)) in model.iter().enumerate() {
                let expected = owner == other_owner
                    && (path.starts_with(other_path) || other_path.starts_with(path));
                assert_eq!(places.overlaps(ids[left], ids[right]), expected);
            }
        }
        Places::validate(&places.into_values(), 2).unwrap();
    }

    #[test]
    fn place_depth_and_arena_capacity_are_bounded_without_losing_existing_paths() {
        let mut places = Places::new(1);
        let mut parent = PlaceId(0);
        for _ in 0..MAX_DEPTH {
            parent = places.field(parent, 0).unwrap();
        }
        assert!(places.field(parent, 0).is_none());
        Places::validate(&places.into_values(), 1).unwrap();

        let mut places = Places::new(1);
        for field in 0..MAX_PLACES - 1 {
            places.field(PlaceId(0), field as u32).unwrap();
        }
        assert!(places.field(PlaceId(0), MAX_PLACES as u32).is_none());
        assert!(places.field(PlaceId(0), 0).is_some());
        Places::validate(&places.into_values(), 1).unwrap();
    }
}
