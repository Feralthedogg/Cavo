use super::*;
use std::collections::VecDeque;

mod paths;
mod sites;
mod transfer;
use paths::Paths;
use sites::{Site, Sites};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Init {
    No,
    Yes,
    Maybe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    registries: Vec<Registry>,
    live: Vec<bool>,
    init: Vec<Init>,
    moves: Vec<Option<MoveCause>>,
    captures: Vec<Option<usize>>,
    predicates: Vec<Option<usize>>,
    scopes: Vec<ScopeId>,
    bounds: HashSet<(Place, LocalId)>,
    variants: HashSet<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Registry {
    Closed,
    Empty,
    MayOwn,
    Drained,
    Inconsistent,
}

impl MoveCause {
    fn join(left: Option<Self>, right: Option<Self>) -> Option<Self> {
        match (left, right) {
            (Some(left), Some(right)) => Some(Self {
                span: if span_key(left.span) <= span_key(right.span) {
                    left.span
                } else {
                    right.span
                },
                certainty: if left.certainty == MoveCertainty::Definite
                    && right.certainty == MoveCertainty::Definite
                {
                    MoveCertainty::Definite
                } else {
                    MoveCertainty::Possible
                },
            }),
            (Some(cause), None) | (None, Some(cause)) => Some(Self {
                certainty: MoveCertainty::Possible,
                ..cause
            }),
            (None, None) => None,
        }
    }
}

impl Registry {
    fn join(self, other: Self) -> Self {
        if self == other {
            self
        } else if matches!(
            (self, other),
            (Self::Empty, Self::MayOwn) | (Self::MayOwn, Self::Empty)
        ) {
            Self::MayOwn
        } else {
            Self::Inconsistent
        }
    }
}

impl State {
    fn new(body: &Body, paths: &Paths) -> Self {
        Self {
            registries: vec![Registry::Closed; body.locals.len()],
            live: vec![false; body.locals.len()],
            init: vec![Init::No; paths.leaves],
            moves: vec![None; paths.leaves],
            captures: vec![None; body.locals.len()],
            predicates: vec![None; body.locals.len()],
            scopes: Vec::new(),
            bounds: HashSet::new(),
            variants: HashSet::new(),
        }
    }
    fn merge(&mut self, other: Self) -> Result<bool, InvariantError> {
        require(
            self.scopes == other.scopes,
            "inconsistent scope stack at CFG join",
        )?;
        require(
            self.live == other.live,
            "inconsistent storage lifetime at CFG join",
        )?;
        let mut changed = false;
        for (left, right) in self.registries.iter_mut().zip(other.registries) {
            let merged = left.join(right);
            changed |= *left != merged;
            *left = merged;
        }
        for (old, new) in self.init.iter_mut().zip(other.init) {
            let joined = if *old == new { new } else { Init::Maybe };
            changed |= *old != joined;
            *old = joined;
        }
        // A definite cause must hold on both paths, even when both are Init::No:
        // one path can be moved while the other was never initialized. Evidence
        // never changes the initialization lattice; strong writes clear it.
        for (old, new) in self.moves.iter_mut().zip(other.moves) {
            let joined = MoveCause::join(*old, new);
            changed |= *old != joined;
            *old = joined;
        }
        changed |= intersect_slots(&mut self.captures, other.captures);
        changed |= intersect_slots(&mut self.predicates, other.predicates);
        let before = self.bounds.len() + self.variants.len();
        self.bounds.retain(|fact| other.bounds.contains(fact));
        self.variants.retain(|fact| other.variants.contains(fact));
        Ok(changed || before != self.bounds.len() + self.variants.len())
    }
    fn forget_guards(&mut self) {
        self.bounds.clear();
        self.variants.clear();
        self.predicates.fill(None);
    }
}

fn span_key(span: Span) -> (crate::source::FileId, u32, u32) {
    (span.file, span.start, span.end)
}

fn intersect_slots(slots: &mut [Option<usize>], other: Vec<Option<usize>>) -> bool {
    let mut changed = false;
    for (old, new) in slots.iter_mut().zip(other) {
        if *old != new && old.is_some() {
            *old = None;
            changed = true;
        }
    }
    changed
}

#[derive(Clone, Debug)]
struct Access {
    node: Option<usize>,
    indexed: bool,
    borrowed: bool,
    protected: bool,
    tags: Vec<usize>,
}
impl Access {
    fn owned(node: usize) -> Self {
        Self {
            node: Some(node),
            indexed: false,
            borrowed: false,
            protected: false,
            tags: Vec::new(),
        }
    }
}

type Edges = Vec<(BlockId, State)>;
struct Worklist {
    inputs: Vec<Option<State>>,
    queue: VecDeque<BlockId>,
    queued: Vec<bool>,
    remaining: usize,
    width: usize,
    retained: usize,
}
impl Worklist {
    fn new(body: &Body, paths: &Paths) -> Self {
        let width = paths.leaves * 2 + body.locals.len() * 3 + body.scopes.len();
        let mut inputs = vec![None; body.blocks.len()];
        inputs[body.entry.0 as usize] = Some(State::new(body, paths));
        let mut queued = vec![false; body.blocks.len()];
        queued[body.entry.0 as usize] = true;
        Self {
            inputs,
            queue: VecDeque::from([body.entry]),
            queued,
            remaining: WORK_LIMIT,
            width,
            retained: width,
        }
    }
    fn charge(&mut self, cost: usize) -> Result<(), InvariantError> {
        self.remaining = self
            .remaining
            .checked_sub(cost)
            .ok_or_else(|| InvariantError::new("MIR verifier work budget exceeded".into()))?;
        Ok(())
    }
    fn push(&mut self, body: &Body, target: BlockId, state: State) -> Result<(), InvariantError> {
        self.charge(self.width + state.bounds.len() + state.variants.len())?;
        let block = body.block(target);
        if matches!(block.terminator, Terminator::Abort) && block.statements.is_empty() {
            return Ok(());
        }
        let index = target.0 as usize;
        let changed = if let Some(previous) = &mut self.inputs[index] {
            previous.merge(state)?
        } else {
            self.retained = self
                .retained
                .saturating_add(self.width + state.bounds.len() + state.variants.len());
            require(
                self.retained <= STATE_LIMIT,
                "MIR verifier state budget exceeded",
            )?;
            self.inputs[index] = Some(state);
            true
        };
        if changed && !self.queued[index] {
            self.queued[index] = true;
            self.queue.push_back(target);
        }
        Ok(())
    }
}

struct Flow<'a, 'p> {
    verifier: &'a Verifier<'p>,
    paths: Paths,
    sites: Sites<'p>,
    source_span: Span,
}
impl Verifier<'_> {
    pub(super) fn flow(&self) -> Result<(), InvariantError> {
        Flow {
            verifier: self,
            paths: Paths::build(self.body, self.properties)?,
            sites: Sites::build(self.body),
            source_span: self.source.body.span,
        }
        .run()
    }
}

impl Flow<'_, '_> {
    fn run(mut self) -> Result<(), InvariantError> {
        let body = self.verifier.body;
        let mut work = Worklist::new(body, &self.paths);
        require(
            work.width <= STATE_LIMIT,
            "MIR verifier state budget exceeded",
        )?;
        let projection_cost = self
            .sites
            .captures
            .iter()
            .map(|place| place.projection.len())
            .max()
            .unwrap_or(1)
            .max(1);
        let mut rejected = None;
        while let Some(id) = work.queue.pop_front() {
            work.queued[id.0 as usize] = false;
            let block = body.block(id);
            let cost = work
                .width
                .saturating_mul(block.statements.len() + 1)
                .saturating_mul(projection_cost);
            work.charge(cost)?;
            let mut state = work.inputs[id.0 as usize]
                .as_ref()
                .expect("queued state")
                .clone();
            let edges = match self.transfer(id, block, &mut state) {
                Ok(edges) => edges,
                Err(error) if error.user_code().is_some() => {
                    // Rejection is sticky and an invalid operation contributes
                    // no successors. Finish other reaching paths so a first
                    // visited path cannot masquerade as a definite move.
                    if rejected.as_ref().is_none_or(|(block, _)| *block == id) {
                        rejected = Some((id, error.context(format!("bb{}", id.0))));
                    }
                    continue;
                }
                Err(error) => return Err(error.context(format!("bb{}", id.0))),
            };
            for (target, state) in edges {
                work.push(body, target, state)?;
            }
        }
        rejected.map_or(Ok(()), |(_, error)| Err(error))
    }

    fn guards(&self, place: &Place, state: &State) -> Result<(), InvariantError> {
        if !place
            .projection
            .iter()
            .any(|projection| matches!(projection, Projection::Index(_) | Projection::Downcast(_)))
        {
            return Ok(());
        }
        let mut base = Place {
            local: place.local,
            projection: Vec::with_capacity(place.projection.len()),
        };
        for projection in &place.projection {
            match projection {
                Projection::Index(element) => require(
                    state.bounds.contains(&(base.clone(), *element)),
                    "indexed access has no current dominating bounds check",
                )?,
                Projection::Downcast(variant) => {
                    let established = self
                        .sites
                        .test(&base, *variant)
                        .is_some_and(|test| state.variants.contains(&test));
                    require(
                        established,
                        "variant projection has no current dominating discriminant check",
                    )?;
                }
                _ => {}
            }
            base.projection.push(*projection);
        }
        Ok(())
    }

    fn access(&self, place: &Place, state: &State, depth: usize) -> Result<Access, InvariantError> {
        require(depth < 64, "place capture cycle or depth limit exceeded")?;
        if depth == 0 {
            self.guards(place, state)?;
        }
        let root = place.local.0 as usize;
        require(state.live[root], "access to dead local storage")?;
        let mut access = Access::owned(self.paths.roots[root]);
        for (index, projection) in place.projection.iter().enumerate() {
            if *projection == Projection::Deref
                && index == 0
                && self.verifier.body.local(place.local).kind == LocalKind::Address
            {
                require(
                    self.paths.initialized(self.paths.roots[root], state),
                    "uninitialized internal address",
                )?;
                let capture = state.captures[root].ok_or_else(|| {
                    InvariantError::new(
                        "internal address has no current established capture".into(),
                    )
                })?;
                let mut captured = self.sites.captures[capture].clone();
                captured
                    .projection
                    .extend_from_slice(&place.projection[1..]);
                return self.access(&captured, state, depth + 1);
            }
            self.project(&mut access, *projection, state)?;
        }
        Ok(access)
    }

    fn project(
        &self,
        access: &mut Access,
        projection: Projection,
        state: &State,
    ) -> Result<(), InvariantError> {
        match projection {
            Projection::Deref => {
                if let Some(node) = access.node {
                    self.initialized(
                        node,
                        state,
                        "dereference of an uninitialized or moved value",
                    )?;
                }
                access.node = None;
                access.indexed = false;
                access.borrowed = true;
            }
            Projection::Field(field) => {
                if let Some(node) = access.node {
                    access.protected |= self.paths.protected(node);
                    if !access.indexed {
                        access.node = Some(self.paths.field(node, field)?);
                    }
                }
            }
            Projection::Downcast(variant) => {
                if let Some(node) = access.node {
                    require(
                        !access.indexed,
                        "indexed enum projections require a captured reference",
                    )?;
                    self.initialized_tag(node, state)?;
                    access.protected |= self.paths.protected(node);
                    access.tags.push(node);
                    access.node = Some(self.paths.variant(node, variant)?);
                }
            }
            Projection::Index(index) => {
                let index = index.0 as usize;
                require(
                    state.live[index] && self.paths.initialized(self.paths.roots[index], state),
                    "index uses an uninitialized or dead local",
                )?;
                access.indexed = true;
            }
        }
        Ok(())
    }

    fn read(&self, place: &Place, state: &State) -> Result<Access, InvariantError> {
        let access = self.access(place, state, 0)?;
        if let Some(node) = access.node {
            self.initialized(node, state, "read of an uninitialized or moved value")?;
        }
        Ok(access)
    }
    fn read_tag(&self, place: &Place, state: &State) -> Result<(), InvariantError> {
        let access = self.access(place, state, 0)?;
        if let Some(node) = access.node {
            self.initialized_tag(node, state)?;
        }
        Ok(())
    }
    fn initialized(&self, node: usize, state: &State, message: &str) -> Result<(), InvariantError> {
        if self.paths.initialized(node, state) {
            Ok(())
        } else {
            Err(InvariantError::unavailable(
                message,
                self.paths.moved_at(node, state),
            ))
        }
    }
    fn initialized_tag(&self, node: usize, state: &State) -> Result<(), InvariantError> {
        if self.paths.tag_initialized(node, state) {
            Ok(())
        } else {
            Err(InvariantError::unavailable(
                "read of an uninitialized or moved variant tag",
                self.paths.tag_move(node, state),
            ))
        }
    }
    fn consume(&self, operand: &Operand, state: &mut State) -> Result<(), InvariantError> {
        match operand {
            Operand::Copy(place) => {
                self.read(place, state)?;
            }
            Operand::Move(place) => {
                let access = self.read(place, state)?;
                require(
                    !access.protected,
                    "move would partially invalidate a value with user Drop",
                )?;
                if !self
                    .verifier
                    .properties
                    .get(self.verifier.place(place)?)
                    .copy
                {
                    require(
                        !access.borrowed && access.node.is_some() && !access.indexed,
                        "non-Copy move requires direct owned storage",
                    )?;
                }
                self.invalidate_captures(&access, state);
                self.paths.set(&access, state, Init::No);
                self.paths.moved(&access, state, self.source_span);
            }
            Operand::Constant { .. }
            | Operand::ConstTerm { .. }
            | Operand::Function { .. }
            | Operand::Unit => {}
        }
        Ok(())
    }

    fn evaluate(&self, value: &Rvalue, state: &mut State) -> Result<(), InvariantError> {
        match value {
            Rvalue::Use(operand)
            | Rvalue::Unary { operand, .. }
            | Rvalue::Repeat { value: operand, .. }
            | Rvalue::RepeatConst { value: operand, .. }
            | Rvalue::ArrayToSlice(operand)
            | Rvalue::DynCoerce { value: operand, .. } => self.consume(operand, state)?,
            Rvalue::Binary { left, right, .. } => {
                self.consume(left, state)?;
                self.consume(right, state)?;
            }
            Rvalue::Borrow { place, .. } | Rvalue::Length(place) => {
                self.read(place, state)?;
            }
            Rvalue::AddressOf(place) => {
                self.access(place, state, 0)?;
            }
            Rvalue::IsVariant { place, .. } => self.read_tag(place, state)?,
            Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
                for value in values {
                    self.consume(value, state)?;
                }
            }
            Rvalue::Record { fields, .. } => {
                for (_, value) in fields {
                    self.consume(value, state)?;
                }
            }
        }
        Ok(())
    }

    fn initialize(&self, destination: &Place, state: &mut State) -> Result<(), InvariantError> {
        let access = self.access(destination, state, 0)?;
        if let Some(node) = access.node
            && self
                .verifier
                .properties
                .get(self.verifier.place(destination)?)
                .may_drop
        {
            require(
                !self.paths.may_live(node, state),
                "assignment overwrites an initialized value requiring Drop",
            )?;
        }
        self.paths.set(&access, state, Init::Yes);
        Ok(())
    }

    fn invalidate_captures(&self, written: &Access, state: &mut State) {
        let invalid: Vec<_> = state
            .captures
            .iter()
            .enumerate()
            .filter_map(|(local, capture)| {
                let capture = capture.as_ref()?;
                let access = self.access(self.sites.captures[*capture], state, 1).ok()?;
                let affected = if let Some(written) = written.node.filter(|_| !written.indexed) {
                    access
                        .tags
                        .iter()
                        .any(|&tag| self.paths.contains_tag(written, tag))
                } else {
                    !access.tags.is_empty() || guarded(self.sites.captures[*capture])
                };
                affected.then_some(local)
            })
            .collect();
        for local in invalid {
            state.captures[local] = None;
        }
    }

    fn invalidate_write(&self, destination: &Place, fresh: bool, state: &mut State) {
        state.bounds.clear();
        let indirect = destination.projection.contains(&Projection::Deref);
        let keep = |id: &usize| {
            let place = self.sites.tests[*id].place;
            !indirect
                && place.local != destination.local
                && !place
                    .projection
                    .contains(&Projection::Index(destination.local))
                && (fresh || !place.projection.contains(&Projection::Deref))
        };
        state.variants.retain(keep);
        for predicate in &mut state.predicates {
            if predicate.is_some_and(|id| !keep(&id)) {
                *predicate = None;
            }
        }
    }
}

fn guarded(place: &Place) -> bool {
    place
        .projection
        .iter()
        .any(|projection| matches!(projection, Projection::Downcast(_)))
}
