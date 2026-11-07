use super::*;
use std::collections::BTreeMap;
mod calls;
mod capture;
mod intrinsics;
mod task_scopes;
use super::summary::Step as Key;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Root {
    Local(u32),
    External(u32),
    Static,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Location {
    root: Root,
    path: Vec<Key>,
}
type Locations = BTreeSet<Location>;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Value {
    task_fields: BTreeMap<TaskSlot, BTreeSet<Vec<Key>>>,
    task_paths: BTreeMap<TaskSlot, BTreeSet<Vec<Key>>>,
    parameters: BTreeMap<Vec<Key>, BTreeSet<summary::ParameterOrigin>>,
    opaque: bool,
    tasks: BTreeSet<TaskSlot>,
    fields: BTreeMap<Vec<Key>, Loans>,
    unknown: bool,
    functions: BTreeSet<hir::DefId>,
    vtables: BTreeSet<u32>,
}
impl Value {
    fn loan(loan: LoanId) -> Self {
        Self {
            fields: BTreeMap::from([(Vec::new(), Loans::from([loan]))]),
            parameters: BTreeMap::new(),
            opaque: false,
            tasks: BTreeSet::new(),
            task_fields: BTreeMap::new(),
            task_paths: BTreeMap::new(),
            unknown: false,
            functions: BTreeSet::new(),
            vtables: BTreeSet::new(),
        }
    }
    fn unknown() -> Self {
        Self {
            unknown: true,
            ..Self::default()
        }
    }
    fn loans(&self) -> Loans {
        self.fields.values().flatten().copied().collect()
    }
    fn merge(&mut self, other: Self) {
        self.opaque |= other.opaque;
        for (path, sources) in other.parameters {
            self.parameters.entry(path).or_default().extend(sources);
        }
        self.tasks.extend(other.tasks);
        for (site, paths) in other.task_paths {
            self.task_paths.entry(site).or_default().extend(paths);
        }
        for (site, paths) in other.task_fields {
            self.task_fields.entry(site).or_default().extend(paths);
        }
        self.unknown |= other.unknown;
        self.functions.extend(other.functions);
        self.vtables.extend(other.vtables);
        for (path, loans) in other.fields {
            self.fields.entry(path).or_default().extend(loans);
        }
    }
    fn project(&self, path: &[Key]) -> Self {
        let mut fields: BTreeMap<Vec<Key>, Loans> = self
            .fields
            .iter()
            .filter_map(|(field, loans)| {
                field
                    .strip_prefix(path)
                    .map(|suffix| (suffix.to_vec(), loans.clone()))
            })
            .collect();
        if self.unknown && !path.is_empty() {
            // An imprecise aggregate may hold a known loan in any projected
            // field. Keep it instead of turning missing shape into no origin.
            fields.entry(Vec::new()).or_default().extend(self.loans());
        }
        let task_paths: BTreeMap<_, _> = self
            .task_paths
            .iter()
            .filter_map(|(site, paths)| {
                let paths: BTreeSet<_> = paths
                    .iter()
                    .filter_map(|field| field.strip_prefix(path).map(<[Key]>::to_vec))
                    .collect();
                (!paths.is_empty()).then_some((*site, paths))
            })
            .collect();
        Self {
            fields,
            parameters: project_parameters(&self.parameters, path),
            opaque: self.opaque,
            tasks: task_paths.keys().copied().collect(),
            task_paths,
            task_fields: self
                .task_fields
                .iter()
                .filter_map(|(site, paths)| {
                    let paths: BTreeSet<_> = paths
                        .iter()
                        .filter_map(|field| {
                            if path.starts_with(field) {
                                Some(Vec::new())
                            } else {
                                field.strip_prefix(path).map(<[Key]>::to_vec)
                            }
                        })
                        .collect();
                    (!paths.is_empty()).then_some((*site, paths))
                })
                .collect(),
            unknown: self.unknown,
            functions: self.functions.clone(),
            vtables: self.vtables.clone(),
        }
    }
    fn insert(&mut self, prefix: &[Key], value: Self) {
        self.opaque |= value.opaque;
        for (suffix, origins) in value.parameters {
            self.parameters
                .entry(prefix.iter().chain(&suffix).copied().collect())
                .or_default()
                .extend(origins);
        }
        self.tasks.extend(&value.tasks);
        for (site, paths) in value.task_paths {
            self.task_paths.entry(site).or_default().extend(
                paths
                    .into_iter()
                    .map(|path| prefix.iter().chain(&path).copied().collect()),
            );
        }
        for (site, paths) in value.task_fields {
            self.task_fields.entry(site).or_default().extend(
                paths
                    .into_iter()
                    .map(|path| prefix.iter().chain(&path).copied().collect()),
            );
        }
        self.unknown |= value.unknown;
        self.functions.extend(value.functions);
        self.vtables.extend(value.vtables);
        for (suffix, loans) in value.fields {
            let path = prefix.iter().chain(&suffix).copied().collect();
            self.fields.entry(path).or_default().extend(loans);
        }
    }
    fn clear(&mut self, path: &[Key]) {
        if !path.is_empty()
            && self.opaque
            && self
                .parameters
                .keys()
                .any(|ancestor| path.starts_with(ancestor))
        {
            self.unknown = true;
        }
        self.parameters
            .retain(|field, _| !field.starts_with(path) && !path.starts_with(field));
        for paths in self.task_fields.values_mut() {
            paths.retain(|field| !field.starts_with(path));
        }
        self.task_fields.retain(|_, paths| !paths.is_empty());
        self.tasks
            .retain(|site| self.task_fields.contains_key(site));
        self.fields.retain(|field, _| !field.starts_with(path));
        if path.is_empty() {
            self.opaque = false;
            self.tasks.clear();
            self.task_fields.clear();
            self.task_paths.clear();
            self.unknown = false;
            self.functions.clear();
            self.vtables.clear();
        }
    }

    fn observe(&mut self, site: TaskSlot) {
        let Some(paths) = self.task_fields.remove(&site) else {
            return;
        };
        self.fields
            .retain(|field, _| !paths.iter().any(|path| field.starts_with(path)));
        self.parameters
            .retain(|field, _| !paths.iter().any(|path| field.starts_with(path)));
        self.tasks.remove(&site);
        self.task_paths.remove(&site);
    }
}

fn project_parameters(
    parameters: &BTreeMap<Vec<Key>, BTreeSet<summary::ParameterOrigin>>,
    path: &[Key],
) -> BTreeMap<Vec<Key>, BTreeSet<summary::ParameterOrigin>> {
    let mut result: BTreeMap<Vec<Key>, BTreeSet<summary::ParameterOrigin>> = BTreeMap::new();
    for (field, origins) in parameters {
        if let Some(suffix) = field.strip_prefix(path) {
            result
                .entry(suffix.to_vec())
                .or_default()
                .extend(origins.iter().cloned());
        } else if let Some(suffix) = path.strip_prefix(field.as_slice()) {
            result
                .entry(Vec::new())
                .or_default()
                .extend(origins.iter().map(|source| {
                    let mut source = source.clone();
                    source.path.extend_from_slice(suffix);
                    source
                }));
        }
    }
    result
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Resolved {
    locations: Locations,
    via: Loans,
    /// Actual reference dereferences governing this access. Loan ancestry also
    /// retains nested capabilities, which must not change a cell's permissions.
    permissions: Loans,
    unknown: bool,
}
impl Resolved {
    fn local(local: LocalId) -> Self {
        Self {
            locations: Locations::from([Location {
                root: Root::Local(local.0),
                path: Vec::new(),
            }]),
            ..Self::default()
        }
    }
    fn merge(&mut self, other: Self) {
        self.locations.extend(other.locations);
        self.via.extend(other.via);
        self.permissions.extend(other.permissions);
        self.unknown |= other.unknown;
    }
    fn project(&mut self, key: Key) {
        self.locations = std::mem::take(&mut self.locations)
            .into_iter()
            .map(|mut location| {
                location.path.push(key);
                location
            })
            .collect();
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LoanState {
    targets: Locations,
    parents: Loans,
    unknown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct State {
    task_slots: BTreeMap<TaskSlot, TaskCount>,
    values: Vec<Value>,
    captures: Vec<Resolved>,
    loans: Vec<LoanState>,
    live: Vec<bool>,
    memory: Vec<Value>,
    writes: BTreeMap<Location, bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TaskSlot {
    registry: LocalId,
    spawn: BlockId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum TaskCount {
    AtMostOne,
    MayBeMany,
}
impl State {
    pub fn initial(context: &Context<'_>) -> Self {
        let frame = context.summaries.frames[context.body.definition.0 as usize]
            .as_ref()
            .unwrap();
        let mut state = Self {
            task_slots: BTreeMap::new(),
            values: vec![Value::default(); context.body.locals.len()],
            captures: vec![Resolved::default(); context.body.locals.len()],
            loans: vec![LoanState::default(); context.loans.len()],
            live: vec![false; context.body.locals.len()],
            memory: vec![Value::default(); frame.inputs.len()],
            writes: BTreeMap::new(),
        };
        for (index, input) in frame.inputs.iter().enumerate() {
            state.memory[index].parameters.insert(
                Vec::new(),
                BTreeSet::from([summary::ParameterOrigin {
                    parameter: input.parameter,
                    path: input.path.iter().copied().chain([Key::Deref]).collect(),
                }]),
            );
            state.memory[index].opaque = true;
            let loan = context.sites.inputs[index];
            state.loans[loan.0 as usize].targets.insert(Location {
                root: Root::External(index as u32),
                path: Vec::new(),
            });
            if let summary::Storage::Pointee { input, path } = &input.storage {
                state.memory[*input as usize].insert(path, Value::loan(loan));
            }
        }
        if let Some(loan) = context.sites.static_loan {
            state.loans[loan.0 as usize].targets.insert(Location {
                root: Root::Static,
                path: Vec::new(),
            });
        }
        state
    }
    pub fn merge(&mut self, other: Self) -> bool {
        let mut changed = self.merge_writes(&other.writes);
        for (site, many) in other.task_slots {
            let old = self.task_slots.get(&site).copied();
            let merged = old.unwrap_or(TaskCount::AtMostOne).max(many);
            changed |= old != Some(merged);
            self.task_slots.insert(site, merged);
        }
        for (old, new) in self.memory.iter_mut().zip(other.memory) {
            let before = old.clone();
            old.merge(new);
            changed |= *old != before;
        }
        for (old, new) in self.values.iter_mut().zip(other.values) {
            let before = old.clone();
            old.merge(new);
            changed |= *old != before;
        }
        for (old, new) in self.captures.iter_mut().zip(other.captures) {
            let before = old.clone();
            old.merge(new);
            changed |= *old != before;
        }
        for (old, new) in self.loans.iter_mut().zip(other.loans) {
            let before = old.clone();
            old.targets.extend(new.targets);
            old.parents.extend(new.parents);
            old.unknown |= new.unknown;
            changed |= *old != before;
        }
        for (old, new) in self.live.iter_mut().zip(other.live) {
            changed |= !*old && new;
            *old |= new;
        }
        changed
    }
    fn merge_writes(&mut self, other: &BTreeMap<Location, bool>) -> bool {
        let mut changed = false;
        for (location, definite) in &mut self.writes {
            let joined = *definite && other.get(location).copied().unwrap_or(false);
            changed |= joined != *definite;
            *definite = joined;
        }
        for location in other.keys() {
            if !self.writes.contains_key(location) {
                self.writes.insert(location.clone(), false);
                changed = true;
            }
        }
        changed
    }
    pub fn bounded(&self) -> bool {
        self.writes.len() <= 1024
            && self.task_slots.len() <= ORIGIN_LIMIT
            && self.values.iter().chain(&self.memory).all(|value| {
                value.tasks.len() <= ORIGIN_LIMIT
                    && value.task_fields.len() <= ORIGIN_LIMIT
                    && value.task_fields.values().all(|paths| {
                        paths.len() <= ORIGIN_LIMIT && paths.iter().all(|path| path.len() <= 128)
                    })
                    && value.task_paths.len() <= ORIGIN_LIMIT
                    && value.task_paths.values().all(|paths| {
                        paths.len() <= ORIGIN_LIMIT && paths.iter().all(|path| path.len() <= 128)
                    })
                    && value.parameters.len() <= ORIGIN_LIMIT
                    && value.parameters.iter().all(|(path, sources)| {
                        path.len() <= 128
                            && sources.len() <= ORIGIN_LIMIT
                            && sources.iter().all(|source| source.path.len() <= 128)
                    })
                    && value.functions.len() <= ORIGIN_LIMIT
                    && value.vtables.len() <= ORIGIN_LIMIT
                    && value.fields.len() <= ORIGIN_LIMIT
                    && value.fields.keys().all(|path| path.len() <= 128)
                    && value
                        .fields
                        .values()
                        .all(|loans| loans.len() <= ORIGIN_LIMIT)
            })
            && self.captures.iter().all(|capture| {
                capture.locations.len() <= ORIGIN_LIMIT
                    && capture.via.len() <= ORIGIN_LIMIT
                    && capture.permissions.len() <= ORIGIN_LIMIT
                    && capture
                        .locations
                        .iter()
                        .all(|location| location.path.len() <= 128)
            })
            && self.loans.iter().all(|loan| {
                loan.targets.len() <= ORIGIN_LIMIT
                    && loan.parents.len() <= ORIGIN_LIMIT
                    && loan
                        .targets
                        .iter()
                        .all(|location| location.path.len() <= 128)
            })
    }
    pub fn weight(&self) -> usize {
        self.values.len()
            + self.loans.len()
            + self
                .values
                .iter()
                .chain(&self.memory)
                .map(|value| {
                    value.functions.len()
                        + value.vtables.len()
                        + value
                            .fields
                            .iter()
                            .map(|(path, loans)| path.len() + loans.len())
                            .sum::<usize>()
                })
                .sum::<usize>()
            + self
                .captures
                .iter()
                .map(|capture| {
                    location_weight(&capture.locations)
                        + capture.via.len()
                        + capture.permissions.len()
                })
                .sum::<usize>()
            + self
                .loans
                .iter()
                .map(|loan| location_weight(&loan.targets) + loan.parents.len())
                .sum::<usize>()
    }
    fn active(&self, live: &live::Live) -> Loans {
        let mut active = Loans::new();
        for &local in live {
            active.extend(self.values[local].loans());
            active.extend(&self.captures[local].via);
        }
        // A reference to a reference-bearing place keeps the inner capability
        // alive too, including hidden defer captures and record projections.
        let mut queue: VecDeque<_> = active.iter().copied().collect();
        while let Some(loan) = queue.pop_front() {
            let state = &self.loans[loan.0 as usize];
            let mut nested = state.parents.clone();
            for target in &state.targets {
                match target.root {
                    Root::Local(local) => {
                        nested.extend(self.values[local as usize].project(&target.path).loans())
                    }
                    Root::External(input) => {
                        nested.extend(self.memory[input as usize].project(&target.path).loans())
                    }
                    Root::Static => {}
                }
            }
            for child in nested {
                if active.insert(child) {
                    queue.push_back(child);
                }
            }
        }
        active
    }
}

#[derive(Clone, Copy)]
enum Update {
    Strong,
    Weak,
}

#[derive(Clone, Copy)]
enum Access {
    Read,
    Write,
    Move,
    Borrow(bool),
    End,
}
impl Access {
    fn exclusive(self) -> bool {
        matches!(
            self,
            Self::Write | Self::Move | Self::Borrow(true) | Self::End
        )
    }
}

pub(super) struct Evaluator<'a, 'b, R> {
    context: &'a Context<'a>,
    reporter: &'b mut R,
    point: Point,
    active: Loans,
}

impl<'a, 'b, R: Reporter> Evaluator<'a, 'b, R> {
    pub fn new(
        context: &'a Context<'a>,
        reporter: &'b mut R,
        point: Point,
        live: &live::Live,
        state: &State,
    ) -> Self {
        // One operation owns all its operands until it commits. Moving an early
        // argument must not end its loan before checking a later argument.
        Self {
            context,
            reporter,
            point,
            active: state.active(live),
        }
    }
    fn gap(&mut self, kind: GapKind) {
        self.reporter.gap(self.point, kind);
    }
    fn finding(&mut self, kind: FindingKind, loan: Option<LoanId>) {
        self.reporter.finding(self.point, kind, loan);
    }

    fn place_type(&self, place: &Place) -> TyId {
        let local = self.context.body.local(place.local);
        let mut ty = local.ty;
        let mut variant = None;
        for (index, projection) in place.projection.iter().enumerate() {
            if index == 0 && local.kind == LocalKind::Address && *projection == Projection::Deref {
                continue;
            }
            ty = self.project_type(ty, *projection, variant);
            variant = if let Projection::Downcast(id) = projection {
                Some(*id)
            } else {
                None
            };
        }
        ty
    }
    fn project_type(&self, ty: TyId, projection: Projection, variant: Option<hir::DefId>) -> TyId {
        match projection {
            Projection::Deref => match self.context.hir.types.get(ty) {
                Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                _ => unreachable!("validated dereference"),
            },
            Projection::Downcast(_) => ty,
            Projection::Field(field) => {
                let fields = variant.map_or_else(
                    || self.context.properties.fields(ty),
                    |variant| self.context.properties.variant_fields(ty, variant),
                );
                fields.expect("validated field")[field as usize]
            }
            Projection::Index(_) => match self.context.hir.types.get(ty) {
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    *inner
                }
                _ => unreachable!("validated index"),
            },
        }
    }

    fn resolve(&mut self, place: &Place, state: &State) -> Resolved {
        let local = self.context.body.local(place.local);
        let mut ty = local.ty;
        let mut variant = None;
        let mut resolved = Resolved::local(place.local);
        for (index, projection) in place.projection.iter().enumerate() {
            if index == 0 && local.kind == LocalKind::Address && *projection == Projection::Deref {
                resolved = state.captures[place.local.0 as usize].clone();
                continue;
            }
            match projection {
                Projection::Deref => resolved = self.dereference(resolved, ty, state),
                Projection::Downcast(variant) => resolved.project(Key::Variant(*variant)),
                Projection::Field(field) => resolved.project(Key::Field(*field)),
                Projection::Index(_) => resolved.project(Key::Element),
            }
            ty = self.project_type(ty, *projection, variant);
            variant = if let Projection::Downcast(id) = projection {
                Some(*id)
            } else {
                None
            };
        }
        if resolved.unknown {
            self.gap(GapKind::UnknownOrigin);
        }
        resolved
    }
    fn dereference(&mut self, resolved: Resolved, ty: TyId, state: &State) -> Resolved {
        let value = self.read_value(&resolved, ty, state);
        if matches!(self.context.hir.types.get(ty), Ty::Pointer { .. }) && value.fields.is_empty() {
            self.gap(GapKind::RawPointer);
            return Resolved {
                unknown: true,
                ..Resolved::default()
            };
        }
        let mut target = Resolved {
            via: resolved.via,
            permissions: resolved.permissions,
            unknown: value.unknown,
            ..Resolved::default()
        };
        for loan in value.loans() {
            let origin = &state.loans[loan.0 as usize];
            target.locations.extend(origin.targets.iter().cloned());
            target.via.insert(loan);
            target.via.extend(&origin.parents);
            target.permissions.insert(loan);
            target.unknown |= origin.unknown;
        }
        if target.locations.is_empty() {
            target.unknown = true;
        }
        target
    }
    fn read_value(&mut self, resolved: &Resolved, ty: TyId, state: &State) -> Value {
        let mut value = Value {
            unknown: resolved.unknown,
            ..Value::default()
        };
        for location in &resolved.locations {
            match location.root {
                Root::Local(local) => {
                    value.merge(state.values[local as usize].project(&location.path))
                }
                Root::External(input) => {
                    value.merge(state.memory[input as usize].project(&location.path))
                }
                Root::Static => value.unknown |= self.context.properties.get(ty).references,
            }
        }
        if !self.context.properties.carries_origins(ty)
            && !matches!(self.context.hir.types.get(ty), Ty::Pointer { .. })
        {
            value.fields.clear();
            value.tasks.clear();
            if !matches!(
                self.context.hir.types.get(ty),
                Ty::Function { .. } | Ty::ForAll { .. }
            ) {
                value.unknown = false;
            }
        }
        if matches!(self.context.hir.types.get(ty), Ty::Reference { .. })
            && value.fields.is_empty()
            && value.parameters.is_empty()
        {
            value.unknown = true;
        }
        if value.unknown {
            self.gap(GapKind::UnknownOrigin);
        }
        value
    }

    fn check(&mut self, resolved: &Resolved, access: Access, state: &State) {
        if resolved.unknown {
            self.gap(GapKind::UnknownOrigin);
        }
        for target in &resolved.locations {
            if let Root::External(input) = target.root {
                self.reporter.access(summary::Access {
                    target: summary::Footprint {
                        input,
                        path: target.path.clone(),
                    },
                    write: access.exclusive(),
                });
            }
            if let Root::Local(local) = target.root
                && !state.live[local as usize]
            {
                self.finding(FindingKind::DanglingReference, None);
            }
        }
        if access.exclusive() {
            self.check_permissions(resolved);
        }
        for loan in self.active.clone() {
            if resolved.via.contains(&loan) {
                continue;
            }
            let origin = &state.loans[loan.0 as usize];
            if (access.exclusive() || self.context.loans[loan.0 as usize].mutable)
                && conflicts(resolved, origin)
            {
                self.finding(FindingKind::Conflict, Some(loan));
            }
        }
    }
    fn check_permissions(&mut self, resolved: &Resolved) {
        for loan in &resolved.permissions {
            if !self.context.loans[loan.0 as usize].mutable {
                self.finding(FindingKind::SharedWrite, Some(*loan));
                return;
            }
        }
    }
    fn check_parent_move(&mut self, value: &Value, state: &State) {
        let parents = value.loans();
        for loan in self.active.clone() {
            if !state.loans[loan.0 as usize].parents.is_disjoint(&parents) {
                self.finding(FindingKind::Conflict, Some(loan));
            }
        }
    }

    fn consume(&mut self, operand: &Operand, state: &mut State) -> Value {
        let (place, access) = match operand {
            Operand::Copy(place) => (place, Access::Read),
            Operand::Move(place) => (place, Access::Move),
            Operand::Function { definition, .. } => {
                return Value {
                    functions: BTreeSet::from([*definition]),
                    ..Value::default()
                };
            }
            Operand::Constant {
                value: hir::Constant::String(_),
                ..
            } => return Value::loan(self.context.sites.static_loan.expect("static source site")),
            Operand::Constant { .. } | Operand::ConstTerm { .. } | Operand::Unit => {
                return Value::default();
            }
        };
        let target = self.resolve(place, state);
        self.check(&target, access, state);
        let value = self.read_value(&target, self.place_type(place), state);
        if matches!(access, Access::Move) {
            self.check_parent_move(&value, state);
            clear_value(&target, state);
        }
        value
    }

    fn evaluate(&mut self, value: &Rvalue, state: &mut State) -> Value {
        match value {
            Rvalue::Use(value) | Rvalue::ArrayToSlice(value) => self.consume(value, state),
            Rvalue::Unary { operand, .. } => {
                self.consume(operand, state);
                Value::default()
            }
            Rvalue::Binary { left, right, .. } => {
                self.consume(left, state);
                self.consume(right, state);
                Value::default()
            }
            Rvalue::Borrow { mutable, place } => self.borrow(*mutable, place, state),
            Rvalue::AddressOf(_) => unreachable!("captures have separate value semantics"),
            Rvalue::DynCoerce { value, vtable } => {
                let mut value = self.consume(value, state);
                value.vtables.insert(*vtable);
                value
            }
            Rvalue::Length(place) | Rvalue::IsVariant { place, .. } => {
                let target = self.resolve(place, state);
                self.check(&target, Access::Read, state);
                Value::default()
            }
            Rvalue::Record { fields, .. } => self.record(fields, state),
            Rvalue::Array(values) => self.sequence(values, Key::Element, state),
            Rvalue::Variant { definition, fields } => self.variant(*definition, fields, state),
            Rvalue::Repeat { value, .. } | Rvalue::RepeatConst { value, .. } => {
                let value = self.consume(value, state);
                let mut result = Value::default();
                result.insert(&[Key::Element], value);
                result
            }
        }
    }
    fn borrow(&mut self, mutable: bool, place: &Place, state: &mut State) -> Value {
        let target = self.resolve(place, state);
        if target.unknown && self.has_raw_projection(place) {
            self.finding(FindingKind::UntrackedOwner, None);
        }
        self.check(&target, Access::Borrow(mutable), state);
        let loan = self.context.sites.borrows[self.point.block.0 as usize]
            [self.point.statement.expect("borrow statement") as usize]
            .expect("borrow site");
        if self.active.contains(&loan) {
            self.gap(GapKind::BorrowGeneration);
        }
        let nested = self
            .read_value(&target, self.place_type(place), state)
            .loans();
        let mut parents = target.via;
        parents.extend(nested);
        state.loans[loan.0 as usize] = LoanState {
            targets: target.locations,
            parents,
            unknown: target.unknown,
        };
        Value::loan(loan)
    }
    fn record(&mut self, fields: &[(u32, Operand)], state: &mut State) -> Value {
        let mut value = Value::default();
        for (field, operand) in fields {
            value.insert(&[Key::Field(*field)], self.consume(operand, state));
        }
        value
    }
    fn variant(&mut self, variant: hir::DefId, values: &[Operand], state: &mut State) -> Value {
        let mut value = Value::default();
        for (index, operand) in values.iter().enumerate() {
            value.insert(
                &[Key::Variant(variant), Key::Field(index as u32)],
                self.consume(operand, state),
            );
        }
        value
    }
    fn sequence(&mut self, values: &[Operand], key: Key, state: &mut State) -> Value {
        let mut value = Value::default();
        for operand in values {
            value.insert(&[key], self.consume(operand, state));
        }
        value
    }

    fn assign(&mut self, destination: &Place, value: &Rvalue, state: &mut State) {
        if let Rvalue::AddressOf(place) = value {
            state.captures[destination.local.0 as usize] = self.resolve(place, state);
            return;
        }
        let target = self.resolve(destination, state);
        let value = self.evaluate(value, state);
        self.check(&target, Access::Write, state);
        self.store(&target, value, state);
    }
    fn store(&mut self, target: &Resolved, value: Value, state: &mut State) {
        let update = if precise(target) {
            Update::Strong
        } else {
            Update::Weak
        };
        self.store_with_update(target, value, state, update);
    }
    fn store_with_update(
        &mut self,
        target: &Resolved,
        value: Value,
        state: &mut State,
        update: Update,
    ) {
        let strong = matches!(update, Update::Strong) && precise(target);
        for location in &target.locations {
            match location.root {
                Root::Local(local) => {
                    let old = &mut state.values[local as usize];
                    if strong {
                        old.clear(&location.path);
                    }
                    old.insert(&location.path, value.clone());
                }
                Root::External(input) => {
                    self.check_store_region(location, &value, state);
                    let old = &mut state.memory[input as usize];
                    if strong {
                        old.clear(&location.path);
                    }
                    old.insert(&location.path, value.clone());
                    state
                        .writes
                        .entry(location.clone())
                        .and_modify(|old| *old |= strong)
                        .or_insert(strong);
                }
                Root::Static => self.finding(FindingKind::SharedWrite, None),
            }
        }
    }
    fn argument(&mut self, local: LocalId, state: &mut State) {
        let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
            .as_ref()
            .unwrap();
        let position =
            self.context.sites.parameter_positions[local.0 as usize].expect("parameter position");
        state.values[local.0 as usize].parameters.insert(
            Vec::new(),
            BTreeSet::from([summary::ParameterOrigin {
                parameter: position,
                path: Vec::new(),
            }]),
        );
        for (index, input) in frame.inputs.iter().enumerate() {
            if let summary::Storage::Parameter { parameter, path } = &input.storage
                && *parameter == position
            {
                state.values[local.0 as usize]
                    .insert(path, Value::loan(self.context.sites.inputs[index]));
            }
        }
        if !frame.complete {
            self.gap(GapKind::UnknownOrigin);
            state.values[local.0 as usize].opaque = true;
        }
    }
    fn end_storage(&mut self, local: LocalId, state: &mut State) {
        self.check(&Resolved::local(local), Access::End, state);
        state.values[local.0 as usize] = Value::default();
        state.captures[local.0 as usize] = Resolved::default();
        state.live[local.0 as usize] = false;
    }
    pub fn statement(&mut self, statement: &StatementKind, state: &mut State) {
        match statement {
            StatementKind::RegistryStart(local) => {
                state.values[local.0 as usize] = Value::default()
            }
            StatementKind::Contract(contract) => {
                for argument in &contract.atom.arguments {
                    self.consume(argument, state);
                }
            }
            StatementKind::Assign { destination, value } => self.assign(destination, value, state),
            StatementKind::Argument(local) => self.argument(*local, state),
            StatementKind::IteratorStart { iterator, value } => {
                let value = self.consume(value, state);
                state.values[iterator.0 as usize] = value;
            }
            StatementKind::StorageLive(local) => {
                state.live[local.0 as usize] = true;
                state.values[local.0 as usize] = Value::default();
                state.captures[local.0 as usize] = Resolved::default();
            }
            StatementKind::StorageDead(local) => self.end_storage(*local, state),
            StatementKind::EnterScope(_) | StatementKind::ExitScope(_) => {}
        }
    }

    pub fn terminator(
        &mut self,
        terminator: &Terminator,
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        match terminator {
            Terminator::Spawn { .. } => self.spawn(terminator, state),
            Terminator::TaskDrain { registry, next, .. } => {
                self.drain(*registry, &mut state);
                vec![(*next, state)]
            }
            Terminator::Call { .. } | Terminator::DynCall { .. } => self.call(terminator, state),
            Terminator::IteratorNext {
                iterator,
                destination,
                some,
                none,
            } => self.iterator_next(*iterator, destination, (*some, *none), state),
            Terminator::Checked {
                value,
                destination,
                normal,
                trap,
            } => {
                let value = self.evaluate(value, &mut state);
                let target = self.resolve(destination, &state);
                self.check(&target, Access::Write, &state);
                let failure = state.clone();
                self.store(&target, value, &mut state);
                vec![(*normal, state), (*trap, failure)]
            }
            Terminator::Drop { place, .. } => {
                self.drop_value(place, &mut state);
                edges(terminator, state)
            }
            Terminator::Switch { condition, .. } => {
                self.consume(condition, &mut state);
                edges(terminator, state)
            }
            Terminator::Bounds { base, index, .. } => {
                let target = self.resolve(base, &state);
                self.check(&target, Access::Read, &state);
                self.consume(&Operand::Copy(Place::local(*index)), &mut state);
                edges(terminator, state)
            }
            Terminator::Return => {
                self.returned(&state);
                self.reporter.exit(ExitKind::Normal, self.context, &state);
                Vec::new()
            }
            Terminator::Resume(reason) => {
                self.reporter.exit(*reason, self.context, &state);
                Vec::new()
            }
            _ => edges(terminator, state),
        }
    }
    fn iterator_next(
        &mut self,
        iterator: LocalId,
        destination: &Place,
        exits: (BlockId, BlockId),
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let mut exhausted = state.clone();
        exhausted.values[iterator.0 as usize] = Value::default();
        if matches!(
            self.context
                .hir
                .types
                .get(self.context.body.local(iterator).ty),
            Ty::Array { length: 0, .. }
        ) {
            return vec![(exits.1, exhausted)];
        }
        let mut value = state.values[iterator.0 as usize].project(&[Key::Element]);
        for (path, &fresh) in &self.context.sites.iterations[self.point.block.0 as usize] {
            let origins = value.project(path).loans();
            let mut target = LoanState {
                unknown: value.unknown,
                ..LoanState::default()
            };
            for loan in origins {
                target
                    .targets
                    .extend(state.loans[loan.0 as usize].targets.iter().cloned());
                target.parents.extend(&state.loans[loan.0 as usize].parents);
                target.parents.insert(loan);
            }
            if self.active.contains(&fresh) {
                self.gap(GapKind::BorrowGeneration);
            }
            state.loans[fresh.0 as usize] = target;
            value.clear(path);
            value.insert(path, Value::loan(fresh));
        }
        let target = self.resolve(destination, &state);
        self.check(&target, Access::Write, &state);
        self.store(&target, value, &mut state);
        // The abstract tail keeps possible remaining origins; exhaustion clears
        // them. Escaped mutable generations cannot be merged into a proof.
        vec![(exits.0, state), (exits.1, exhausted)]
    }
    fn drop_value(&mut self, place: &Place, state: &mut State) {
        let target = self.resolve(place, state);
        self.check(&target, Access::End, state);
        let value = self.read_value(&target, self.place_type(place), state);
        if self.context.properties.get(self.place_type(place)).may_drop {
            if let Some(assumptions) = summary::drops::known(self.place_type(place), self.context) {
                for assumption in assumptions {
                    self.reporter.assumption(assumption);
                }
            } else {
                self.gap(GapKind::OpaqueDrop);
            }
            for loan in drop_loans(&value, state) {
                let borrowed = Resolved {
                    locations: state.loans[loan.0 as usize].targets.clone(),
                    via: ancestors(loan, state),
                    permissions: Loans::from([loan]),
                    unknown: value.unknown || state.loans[loan.0 as usize].unknown,
                };
                // A user destructor can use its retained mutable capabilities.
                // Treating them as read-only would permit a live shared child
                // loan to overlap the destructor's writes.
                let access = if self.context.loans[loan.0 as usize].mutable {
                    Access::Write
                } else {
                    Access::Read
                };
                self.check(&borrowed, access, state);
            }
        }
        clear_value(&target, state);
    }
    fn returned(&mut self, state: &State) {
        let value = &state.values[self.context.body.return_local.0 as usize];
        self.check_escape(value, state);
        let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
            .as_ref()
            .unwrap();
        for requirement in &frame.result {
            self.check_requirement(value, requirement, state);
        }
        if !frame.complete {
            self.gap(GapKind::ReturnRegion);
        }
    }
    fn check_store_region(&mut self, location: &Location, value: &Value, state: &State) {
        self.check_escape(value, state);
        let Root::External(input) = location.root else {
            return;
        };
        let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
            .as_ref()
            .unwrap();
        let target = summary::Footprint {
            input,
            path: location.path.clone(),
        };
        if let Some(cell) = frame.reference_cell(&target) {
            for requirement in &frame.stores[cell] {
                self.check_requirement(value, requirement, state);
            }
        } else if !value.fields.is_empty() {
            self.gap(GapKind::ExternalReferenceStore);
        }
    }
    fn check_requirement(
        &mut self,
        value: &Value,
        requirement: &summary::Requirement,
        state: &State,
    ) {
        let mut value = value.clone();
        for &step in &requirement.path {
            if step == Key::Deref {
                let target = self.value_target(&value, state);
                value = self.read_value(&target, TyId::ERROR, state);
            } else {
                value = value.project(&[step]);
            }
        }
        self.check_region(&value, requirement.region, state);
        if requirement.invariant {
            let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
                .as_ref()
                .unwrap();
            for loan in value.loans() {
                for target in &state.loans[loan.0 as usize].targets {
                    let actual = match target.root {
                        Root::External(input) => frame.inputs[input as usize].region,
                        Root::Static => crate::types::Region::Static,
                        Root::Local(_) => continue,
                    };
                    if !frame.region_outlives(requirement.region, actual) {
                        self.finding(FindingKind::RegionMismatch, Some(loan));
                    }
                }
            }
        }
    }
    fn check_region(&mut self, value: &Value, region: crate::types::Region, state: &State) {
        if value.unknown && value.loans().is_empty() && value.parameters.is_empty() {
            self.finding(FindingKind::UnknownRegion, None);
        }
        let frame = self.context.summaries.frames[self.context.body.definition.0 as usize]
            .as_ref()
            .unwrap();
        for loan in value.loans() {
            for target in &state.loans[loan.0 as usize].targets {
                match target.root {
                    Root::External(input) if !frame.outlives(input, region) => {
                        self.finding(FindingKind::RegionMismatch, Some(loan))
                    }
                    Root::Local(_) => self.finding(FindingKind::LocalEscape, Some(loan)),
                    _ => {}
                }
            }
        }
        if value.unknown {
            self.gap(GapKind::UnknownOrigin);
        }
    }

    fn has_raw_projection(&self, place: &Place) -> bool {
        let mut ty = self.context.body.local(place.local).ty;
        let mut variant = None;
        for (index, projection) in place.projection.iter().enumerate() {
            if index == 0
                && self.context.body.local(place.local).kind == LocalKind::Address
                && *projection == Projection::Deref
            {
                continue;
            }
            if *projection == Projection::Deref
                && matches!(self.context.hir.types.get(ty), Ty::Pointer { .. })
            {
                return true;
            }
            ty = self.project_type(ty, *projection, variant);
            variant = if let Projection::Downcast(id) = projection {
                Some(*id)
            } else {
                None
            };
        }
        false
    }
    fn check_escape(&mut self, value: &Value, state: &State) {
        if !value.tasks.is_empty() {
            self.finding(FindingKind::TaskEscape, None);
        }
        for loan in value.loans() {
            if state.loans[loan.0 as usize]
                .targets
                .iter()
                .any(|target| matches!(target.root, Root::Local(_)))
            {
                self.finding(FindingKind::LocalEscape, Some(loan));
            }
        }
    }
}

fn drop_loans(value: &Value, state: &State) -> Loans {
    let mut result = value.loans();
    let mut pending: Vec<_> = result.iter().copied().collect();
    while let Some(loan) = pending.pop() {
        for target in &state.loans[loan.0 as usize].targets {
            let nested = match target.root {
                Root::Local(local) => state.values[local as usize].project(&target.path).loans(),
                Root::External(input) => state.memory[input as usize].project(&target.path).loans(),
                Root::Static => Loans::new(),
            };
            for loan in nested {
                if result.insert(loan) {
                    pending.push(loan);
                }
            }
        }
    }
    result
}

fn ancestors(loan: LoanId, state: &State) -> Loans {
    let mut result = Loans::from([loan]);
    let mut pending = vec![loan];
    while let Some(loan) = pending.pop() {
        for &parent in &state.loans[loan.0 as usize].parents {
            if result.insert(parent) {
                pending.push(parent);
            }
        }
    }
    result
}

fn overlap(a: &Location, b: &Location) -> bool {
    if a.root != b.root {
        return false;
    }
    a.path
        .iter()
        .zip(&b.path)
        .all(|(a, b)| a == b || *a == Key::Element || *b == Key::Element)
}
fn conflicts(access: &Resolved, loan: &LoanState) -> bool {
    !loan.parents.is_disjoint(&access.via)
        || access.locations.iter().any(|target| {
            loan.targets
                .iter()
                .any(|borrowed| overlap(target, borrowed))
        })
}
fn precise(target: &Resolved) -> bool {
    !target.unknown
        && target.locations.len() == 1
        && target
            .locations
            .iter()
            .all(|location| !location.path.contains(&Key::Element))
}
fn location_weight(locations: &Locations) -> usize {
    locations
        .iter()
        .map(|location| location.path.len() + 1)
        .sum()
}
fn clear_value(target: &Resolved, state: &mut State) {
    if !precise(target) {
        return;
    }
    for location in &target.locations {
        match location.root {
            Root::Local(local) => state.values[local as usize].clear(&location.path),
            Root::External(input) => state.memory[input as usize].clear(&location.path),
            Root::Static => {}
        }
    }
}
fn edges(terminator: &Terminator, state: State) -> Vec<(BlockId, State)> {
    live::successors(terminator)
        .into_iter()
        .map(|target| (target, state.clone()))
        .collect()
}
