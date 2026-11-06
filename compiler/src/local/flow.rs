use super::{
    Assessment, EventId, Evidence, EvidenceId, Finding, FunctionReport, LoanId, PlaceId, Point,
    Predicate, Reborrow, RegionContract, RegionStep, RegionTerm,
    cfg::{BlockId, Exit, Graph, Operation},
    memory::{Calls, Inferred, MemorySummary},
    nll::{Live, Liveness},
    place::Places,
    properties::Properties,
};
use crate::arena::Access as _;
use crate::{
    diagnostic::{Diagnostic, report},
    hir::{self, ExprId, ExprKind as H},
    source::Span,
    syntax::ast::{BinaryOp, UnaryOp},
    types::{Region, Ty},
};
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

mod memory;
mod report;
use report::{Check, Problem, Reporter};

const AVAILABLE: u8 = 1;
const UNINITIALIZED: u8 = 2;
const MOVED: u8 = 4;
const DEAD: u8 = 8;
const POISON: u8 = 16;
const MAX_ORIGINS: usize = 64;
const MAX_RETURN_VALUE_COST: usize = 4096;
const MAX_RETURN_STATE_COST: usize = 250_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Update {
    Strong,
    Weak,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Written {
    Unwritten,
    Definite,
    Maybe,
}
impl Written {
    fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::Maybe }
    }
    fn may_write(self) -> bool {
        self != Self::Unwritten
    }
    fn definite(self) -> bool {
        self == Self::Definite
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct LoanSetId(u32);

struct LoanSets {
    values: Vec<Vec<LoanId>>,
    index: HashMap<Vec<LoanId>, LoanSetId>,
}
impl LoanSets {
    fn new() -> Self {
        Self {
            values: vec![Vec::new()],
            index: HashMap::from([(Vec::new(), LoanSetId(0))]),
        }
    }
    fn contains(&self, set: LoanSetId, loan: LoanId) -> bool {
        self.values[set.0 as usize].binary_search(&loan).is_ok()
    }
    fn derive(
        &mut self,
        set: LoanSetId,
        add: Option<LoanId>,
        remove: Option<LoanId>,
    ) -> Option<LoanSetId> {
        let mut value = self.values[set.0 as usize].clone();
        if let Some(add) = add {
            value.push(add);
        }
        value.sort_unstable();
        value.dedup();
        if let Some(remove) = remove {
            value.retain(|loan| *loan != remove);
        }
        self.intern(value)
    }
    fn intern(&mut self, mut value: Vec<LoanId>) -> Option<LoanSetId> {
        value.sort_unstable();
        value.dedup();
        if let Some(&id) = self.index.get(&value) {
            return Some(id);
        }
        if self.values.len() >= 8192 || value.len() > 128 {
            return None;
        }
        let id = LoanSetId(self.values.len() as u32);
        self.values.push(value.clone());
        self.index.insert(value, id);
        Some(id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Origin {
    Borrow {
        place: PlaceId,
        // Indexing coarsens to an enclosing place; later projections must not
        // recover precision that was lost before this reference was created.
        precise: bool,
        event: EventId,
        mutable: bool,
        loan: LoanId,
        parents: LoanSetId,
    },
    OpaqueInput(u32),
    Static,
}
type Origins = BTreeSet<Origin>;
type Causes = BTreeSet<EventId>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Slot {
    // Powerset of possible concrete availability states, not independent flags.
    // Only the singleton AVAILABLE establishes availability at a CFG point.
    flags: u8,
    origins: Origins,
    causes: Causes,
    functions: BTreeSet<hir::DefId>,
    written: Written,
}
struct PlaceState {
    flags: u8,
    origins: Origins,
    causes: Causes,
    functions: BTreeSet<hir::DefId>,
}
impl Default for Slot {
    fn default() -> Self {
        Self {
            flags: DEAD,
            origins: Origins::new(),
            causes: Causes::new(),
            functions: BTreeSet::new(),
            written: Written::Unwritten,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    slots: Vec<Slot>,
    temporaries: Vec<Origins>,
    drop_temporaries: Origins,
    normal: bool,
    /// Prepared before cleanup and retained across any cleanup CFG branches.
    returned: Option<Value>,
}
impl State {
    fn merge(&mut self, other: &Self) -> bool {
        // Join alternatives; absence of a normal exit contributes no state.
        // Origins/functions union, and a write is definite only on every path.
        if !other.normal {
            return false;
        }
        if !self.normal {
            *self = other.clone();
            return true;
        }
        let mut changed = false;
        for (left, right) in self.slots.iter_mut().zip(&other.slots) {
            let before = (
                left.flags,
                left.origins.len(),
                left.causes.len(),
                left.functions.len(),
                left.written,
            );
            left.flags |= right.flags;
            left.written = left.written.join(right.written);
            left.functions.extend(&right.functions);
            left.origins.extend(right.origins.iter().cloned());
            left.causes.extend(right.causes.iter().copied());
            changed |= before
                != (
                    left.flags,
                    left.origins.len(),
                    left.causes.len(),
                    left.functions.len(),
                    left.written,
                );
        }
        debug_assert_eq!(self.temporaries, other.temporaries);
        let before = self.drop_temporaries.len();
        self.drop_temporaries
            .extend(other.drop_temporaries.iter().cloned());
        changed |= before != self.drop_temporaries.len();
        changed |= self.merge_return(other.returned.as_ref());
        changed
    }
    fn merge_return(&mut self, other: Option<&Value>) -> bool {
        match (&mut self.returned, other) {
            (Some(value), Some(other)) => memory::join_value(value, other),
            (None, Some(other)) => {
                let mut value = other.clone();
                value.valid = false;
                self.returned = Some(value);
                true
            }
            (Some(value), None) => std::mem::replace(&mut value.valid, false),
            (None, None) => false,
        }
    }
    fn bounded(&self) -> bool {
        self.drop_temporaries.len() <= MAX_ORIGINS
            && self.slots.iter().all(|slot| {
                slot.origins.len() <= MAX_ORIGINS
                    && slot.causes.len() <= 128
                    && slot.functions.len() <= 64
            })
    }
    fn returned_cost(&self) -> Option<usize> {
        self.returned.as_ref().map_or(Some(0), Value::cost)
    }
    fn active_borrows(
        &self,
        place: PlaceId,
        places: &Places,
        live: &Live,
    ) -> BTreeSet<(LoanId, EventId, bool)> {
        let mut visited = vec![false; self.slots.len()];
        let mut pending: Vec<_> = self
            .temporaries
            .iter()
            .flat_map(|v| v.iter())
            .chain(&self.drop_temporaries)
            .chain(self.returned.iter().flat_map(|value| &value.origins))
            .collect();
        for index in live.iter() {
            visited[index] = true;
            if self.slots[index].flags & AVAILABLE != 0 {
                pending.extend(&self.slots[index].origins);
            }
        }
        for (index, slot) in self.slots.iter().enumerate() {
            if slot.written.may_write()
                && slot.flags & AVAILABLE != 0
                && places.input_source(places.leaf(index)).is_some()
            {
                pending.extend(&slot.origins);
            }
        }
        let mut result = BTreeSet::new();
        while let Some(origin) = pending.pop() {
            if let Origin::Borrow {
                place: found,
                event,
                mutable,
                loan,
                ..
            } = origin
            {
                if places.overlaps(*found, place) {
                    result.insert((*loan, *event, *mutable));
                }
                // A live reference to a reference/record also keeps the value's
                // contained loans live, even without a later direct local use.
                for index in places.leaves(*found) {
                    if !visited[index] {
                        visited[index] = true;
                        if self.slots[index].flags & AVAILABLE != 0 {
                            pending.extend(&self.slots[index].origins);
                        }
                    }
                }
            }
        }
        result
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Value {
    valid: bool,
    origins: Origins,
    causes: Causes,
    fields: Option<Vec<Value>>,
    functions: BTreeSet<hir::DefId>,
}
impl Value {
    fn cost(&self) -> Option<usize> {
        let mut pending = vec![self];
        let mut cost = 0usize;
        while let Some(value) = pending.pop() {
            if value.origins.len() > MAX_ORIGINS
                || value.causes.len() > 128
                || value.functions.len() > 64
            {
                return None;
            }
            cost += 1 + value.origins.len() + value.causes.len() + value.functions.len();
            let remaining = MAX_RETURN_VALUE_COST.checked_sub(cost)?;
            if let Some(fields) = &value.fields {
                if fields.len().saturating_add(pending.len()) > remaining {
                    return None;
                }
                pending.extend(fields);
            }
        }
        Some(cost)
    }
    fn scalar() -> Self {
        Self {
            valid: true,
            ..Self::default()
        }
    }
    fn combine(&mut self, other: &Self) {
        self.valid &= other.valid;
        self.origins.extend(other.origins.iter().cloned());
        self.causes.extend(other.causes.iter().copied());
        self.functions.extend(&other.functions);
        self.fields = None;
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Value,
    Inspect { write: bool },
    Move(EventId),
}
#[derive(Clone, Copy)]
enum Access {
    Read,
    Write,
    BorrowShared,
    BorrowExclusive,
    Transfer,
}

#[derive(Clone)]
enum Target {
    // `precise` controls update strength, `projected` marks non-root access, and
    // `mutable` is the granted capability. A direct local is exact; an indirect
    // or indexed access may retain only an enclosing footprint.
    Place {
        place: PlaceId,
        precise: bool,
        via: LoanSetId,
        projected: bool,
        mutable: bool,
    },
    Static,
    Opaque,
    Invalid,
}

struct Evaluator<'a, R: Reporter> {
    function: &'a hir::Function,
    graph: &'a Graph,
    program: &'a hir::Program,
    properties: &'a Properties,
    contracts: &'a [Option<RegionContract>],
    external: &'a crate::external::Bindings,
    summaries: &'a [Inferred],
    input_positions: &'a [Option<usize>],
    loans: &'a mut LoanSets,
    places: &'a mut Places,
    liveness: &'a Liveness,
    live_expression: Option<ExprId>,
    after_store: bool,
    point: Point,
    reporter: &'a mut R,
    normal_exit: bool,
    visits: usize,
    budget: usize,
    exhausted: bool,
    depth: usize,
    place_depth: usize,
    expression_frames: usize,
}

pub(super) struct Run {
    pub report: FunctionReport,
}
pub(super) struct SummaryRun {
    pub memory: Option<MemorySummary>,
    pub work: usize,
    pub dependencies: BTreeSet<hir::DefId>,
}
#[derive(Clone, Copy)]
struct Analysis<'a> {
    function: &'a hir::Function,
    graph: &'a Graph,
    program: &'a hir::Program,
    properties: &'a Properties,
    calls: Calls<'a>,
}
struct Prepared {
    places: Places,
    liveness: Liveness,
    input_positions: Vec<Option<usize>>,
}
struct Converged {
    prepared: Prepared,
    loans: LoanSets,
    incoming: Vec<Option<State>>,
    work: usize,
    limited: bool,
}
struct Trace {
    exit: Option<(State, Value)>,
    work: usize,
    limited: bool,
}

/// Prepared returns are an additional persistent payload, not part of local
/// slot width. Account their retained cells and copy/join work separately.
struct ReturnBudget {
    costs: Vec<usize>,
    retained: usize,
}
impl ReturnBudget {
    fn new(blocks: usize) -> Self {
        Self {
            costs: vec![0; blocks],
            retained: 0,
        }
    }
    fn retain(&mut self, block: BlockId, state: &State) -> bool {
        let Some(cost) = state.returned_cost() else {
            return false;
        };
        let index = block.0 as usize;
        let retained = self.retained - self.costs[index] + cost;
        if retained > MAX_RETURN_STATE_COST {
            return false;
        }
        self.costs[index] = cost;
        self.retained = retained;
        true
    }
    fn charge(&self, block: BlockId, added: usize, remaining: &mut usize) -> bool {
        let Some(next) = remaining.checked_sub(self.costs[block.0 as usize] + added) else {
            return false;
        };
        *remaining = next;
        true
    }
}

impl<'a, R: Reporter> Evaluator<'a, R> {
    fn new(
        context: Analysis<'a>,
        prepared: &'a mut Prepared,
        loans: &'a mut LoanSets,
        reporter: &'a mut R,
        block: BlockId,
        budget: usize,
    ) -> Self {
        Self {
            function: context.function,
            graph: context.graph,
            program: context.program,
            properties: context.properties,
            contracts: context.calls.regions,
            external: context.calls.external,
            summaries: context.calls.memory,
            input_positions: &prepared.input_positions,
            loans,
            places: &mut prepared.places,
            liveness: &prepared.liveness,
            live_expression: None,
            after_store: false,
            point: Point {
                block,
                operation: 0,
                evaluation: 0,
            },
            reporter,
            normal_exit: false,
            visits: 0,
            budget,
            exhausted: false,
            depth: 0,
            place_depth: 0,
            expression_frames: 0,
        }
    }
}
fn solve(context: Analysis<'_>) -> Option<Converged> {
    let function = context.function;
    let graph = context.graph;
    let places = Places::build(function, graph, context.properties, context.program)?;
    let liveness = Liveness::compute(
        function,
        graph,
        context.program,
        &places,
        context.properties,
    )?;
    let mut input_positions = vec![None; places.len()];
    let contract = context.calls.regions[function.definition.0 as usize]
        .as_ref()
        .expect("function region contract");
    for (index, input) in contract.inputs.iter().enumerate() {
        if let Some(&local) = function.parameters.get(input.parameter as usize)
            && let Some(place) = places.region_path(Places::root(local), &input.path)
        {
            input_positions[place.0 as usize] = Some(index);
        }
    }
    let mut prepared = Prepared {
        places,
        liveness,
        input_positions,
    };
    let mut loans = LoanSets::new();
    let width = prepared.places.leaf_count().max(1);
    let mut incoming = vec![None; graph.blocks.len()];
    incoming[0] = Some(State {
        slots: vec![Slot::default(); prepared.places.leaf_count()],
        temporaries: Vec::new(),
        drop_temporaries: Origins::new(),
        normal: true,
        returned: None,
    });
    let mut queue = VecDeque::from([BlockId(0)]);
    let mut queued = vec![false; graph.blocks.len()];
    queued[0] = true;
    let mut remaining = 2_000_000usize;
    let mut returns = ReturnBudget::new(graph.blocks.len());
    let mut limited = false;
    while let Some(block) = queue.pop_front() {
        queued[block.0 as usize] = false;
        if !returns.charge(block, 0, &mut remaining) {
            limited = true;
            break;
        }
        let mut state = incoming[block.0 as usize].as_ref().unwrap().clone();
        let cost = (graph.blocks[block.0 as usize].operations.len() + 1).saturating_mul(width);
        let Some(next) = remaining.checked_sub(cost) else {
            limited = true;
            break;
        };
        remaining = next;
        let mut discard = report::Discard;
        let mut evaluator = Evaluator::new(
            context,
            &mut prepared,
            &mut loans,
            &mut discard,
            block,
            (remaining / width).min(100_000),
        );
        let successors = evaluator.block(block, &mut state);
        remaining = remaining.saturating_sub(evaluator.visits.saturating_mul(width));
        let return_cost = state.returned_cost();
        if evaluator.exhausted || !state.bounded() || return_cost.is_none() {
            limited = true;
            break;
        }
        for successor in successors {
            if !returns.charge(
                successor,
                return_cost.expect("bounded prepared return"),
                &mut remaining,
            ) {
                limited = true;
                break;
            }
            let target = &mut incoming[successor.0 as usize];
            let changed = if let Some(old) = target {
                old.merge(&state)
            } else {
                *target = Some(state.clone());
                true
            };
            if target
                .as_ref()
                .is_some_and(|s| !s.bounded() || !returns.retain(successor, s))
            {
                limited = true;
                break;
            }
            if changed && !queued[successor.0 as usize] {
                queue.push_back(successor);
                queued[successor.0 as usize] = true;
            }
        }
        if limited {
            break;
        }
    }
    Some(Converged {
        prepared,
        loans,
        incoming,
        work: 2_000_000 - remaining,
        limited,
    })
}
fn trace<R: Reporter>(context: Analysis<'_>, converged: &mut Converged, reporter: &mut R) -> Trace {
    let mut output = Trace {
        exit: None,
        work: converged.work,
        limited: converged.limited,
    };
    if output.limited {
        return output;
    }
    let width = converged.prepared.places.leaf_count().max(1);
    // A single transfer implementation runs over converged states. The sink
    // receives immutable facts and cannot influence any state transition.
    for (index, state) in std::mem::take(&mut converged.incoming)
        .into_iter()
        .enumerate()
    {
        let Some(mut state) = state else {
            continue;
        };
        let mut evaluator = Evaluator::new(
            context,
            &mut converged.prepared,
            &mut converged.loans,
            reporter,
            BlockId(index as u32),
            100_000,
        );
        evaluator.block(BlockId(index as u32), &mut state);
        let return_cost = state.returned_cost();
        output.work += evaluator.visits + width + return_cost.unwrap_or(MAX_RETURN_VALUE_COST);
        if evaluator.exhausted || !state.bounded() || return_cost.is_none() {
            output.limited = true;
            break;
        }
        if evaluator.normal_exit {
            let returned = state.returned.take().unwrap_or_else(Value::scalar);
            if let Some((previous, value)) = &mut output.exit {
                previous.merge(&state);
                memory::join_value(value, &returned);
            } else {
                output.exit = Some((state, returned));
            }
        }
    }
    output
}
fn finish_memory(
    context: Analysis<'_>,
    converged: &Converged,
    trace: &Trace,
    failed: bool,
) -> Option<MemorySummary> {
    if trace.limited || failed {
        return None;
    }
    let contract = context.calls.regions[context.function.definition.0 as usize]
        .as_ref()
        .unwrap();
    memory::capture(
        trace.exit.as_ref(),
        &converged.prepared.places,
        &converged.prepared.input_positions,
        &converged.loans,
    )
    .filter(|m| m.valid(contract.inputs.len(), context.program.definitions.len()))
}
pub(super) fn summarize(
    function: &hir::Function,
    graph: &Graph,
    program: &hir::Program,
    properties: &Properties,
    calls: Calls<'_>,
) -> SummaryRun {
    let context = Analysis {
        function,
        graph,
        program,
        properties,
        calls,
    };
    let Some(mut converged) = solve(context) else {
        return SummaryRun {
            memory: None,
            work: 1,
            dependencies: BTreeSet::new(),
        };
    };
    let mut reporter = report::Summary::default();
    let traced = trace(context, &mut converged, &mut reporter);
    let memory = finish_memory(context, &converged, &traced, reporter.failed);
    SummaryRun {
        memory,
        work: traced.work,
        dependencies: reporter.dependencies,
    }
}
pub(super) fn analyze(
    function: &hir::Function,
    graph: Graph,
    program: &hir::Program,
    properties: &Properties,
    calls: Calls<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Run {
    let context = Analysis {
        function,
        graph: &graph,
        program,
        properties,
        calls,
    };
    let Some(mut converged) = solve(context) else {
        report(
            diagnostics,
            Diagnostic::error(
                "E-LOCAL-LIMIT",
                "move paths or NLL analysis exceed their resource limit",
                function.body.span,
            )
            .note("no local safety result was approved from the unfinished analysis")
            .help("split this function or its record types into smaller parts"),
        );
        let places = Places::new(context.graph.slots).into_values();
        return Run {
            report: FunctionReport {
                definition: function.definition,
                cfg: graph,
                places,
                nll: None,
                evidence: Vec::new(),
                findings: Vec::new(),
                local_complete: false,
                reborrows: Vec::new(),
                assumptions: Vec::new(),
                memory: None,
            },
        };
    };
    let mut reporter = report::Diagnostics::new(&graph);
    let traced = trace(context, &mut converged, &mut reporter);
    let memory = finish_memory(context, &converged, &traced, reporter.status.failed);
    let mut complete = !traced.limited
        && !reporter.status.unsupported
        && calls.regions[function.definition.0 as usize]
            .as_ref()
            .unwrap()
            .valid;
    if traced.limited {
        report(
            diagnostics,
            Diagnostic::error(
                "E-LOCAL-LIMIT",
                "local analysis exceeds its evaluation or replay budget",
                function.body.span,
            )
            .note("no local safety result was approved from the unfinished analysis")
            .help("split this function into smaller functions"),
        );
        reporter.findings.clear();
        reporter.reborrows.clear();
        reporter.evidence.truncate(graph.events.len());
    }
    if memory.is_none() && complete && !reporter.status.failed {
        complete = false;
        report(
            diagnostics,
            Diagnostic::error(
                "E-MEMORY-SUMMARY",
                "normal-return memory effects cannot be represented within this analysis stage",
                function.body.span,
            )
            .note("no memory transformer was approved for callers"),
        );
    }
    let mut seen = HashSet::new();
    for diagnostic in reporter.diagnostics {
        if seen.insert((
            diagnostic.code,
            diagnostic.primary.file.0,
            diagnostic.primary.start,
            diagnostic.primary.end,
        )) {
            report(diagnostics, diagnostic);
        }
    }
    let report::Diagnostics {
        evidence,
        findings,
        reborrows,
        ..
    } = reporter;
    Run {
        report: FunctionReport {
            definition: function.definition,
            cfg: graph,
            places: converged.prepared.places.into_values(),
            nll: Some(converged.prepared.liveness.report),
            evidence,
            findings,
            local_complete: complete,
            reborrows,
            assumptions: Vec::new(),
            memory,
        },
    }
}

impl<R: Reporter> Evaluator<'_, R> {
    fn lineage(
        &mut self,
        set: LoanSetId,
        add: Option<LoanId>,
        remove: Option<LoanId>,
    ) -> LoanSetId {
        let cost = self.loans.values[set.0 as usize].len() + 1;
        let Some(budget) = self.budget.checked_sub(cost) else {
            self.exhausted = true;
            return LoanSetId(0);
        };
        self.budget = budget;
        self.visits += cost;
        self.loans.derive(set, add, remove).unwrap_or_else(|| {
            self.exhausted = true;
            LoanSetId(0)
        })
    }

    fn argument_path(
        &mut self,
        argument: &Value,
        path: &[RegionStep],
        state: &State,
        span: Span,
    ) -> (Value, bool) {
        let mut value = argument.clone();
        let mut exact = true;
        for step in path {
            match *step {
                RegionStep::Field(field) => {
                    if let Some(child) = value.fields.as_ref().and_then(|v| v.get(field as usize)) {
                        value = child.clone();
                    } else {
                        exact = false;
                    }
                }
                RegionStep::Deref => {
                    let mut next = Value::scalar();
                    let mut first = true;
                    for origin in &value.origins {
                        if let Origin::Borrow { place, precise, .. } = origin {
                            let data = self.value(*place, state);
                            if first {
                                next = data;
                                first = false;
                            } else {
                                next.combine(&data);
                            }
                            exact &= *precise;
                        } else {
                            self.unsupported("an opaque nested call input", span);
                            next.valid = false;
                        }
                    }
                    if first {
                        next.valid = false;
                    }
                    value = next;
                }
            }
        }
        (value, exact)
    }

    fn origin_region(&self, origin: &Origin) -> Option<RegionTerm> {
        match origin {
            Origin::Static => Some(RegionTerm::Declared(Region::Static)),
            Origin::Borrow { place, .. } => {
                let source = self.places.input_source(*place)?;
                let index = self.input_positions[source.0 as usize]?;
                self.contracts[self.function.definition.0 as usize]
                    .as_ref()?
                    .inputs[index]
                    .term
                    .into()
            }
            Origin::OpaqueInput(_) => None,
        }
    }

    fn typed_regions(
        &mut self,
        ty: crate::types::TyId,
        value: &Value,
        state: &State,
        span: Span,
        code: &'static str,
        depth: usize,
    ) -> bool {
        if !value.valid {
            return false;
        }
        if let Ty::Reference {
            mutable: true,
            inner,
            ..
        } = *self.program.types.get(ty)
            && self.contains_callable(inner)
        {
            for origin in &value.origins {
                if let Origin::Borrow { place, .. } = origin
                    && !self
                        .program
                        .types
                        .region_invariant(self.places.ty(*place), inner)
                {
                    self.reporter.problem(Problem::CallableInvariant(span));
                    return false;
                }
            }
        }
        if !self.constrained(ty) {
            return !self.exhausted;
        }
        if depth >= 128 || self.budget == 0 {
            self.exhausted = true;
            return false;
        }
        self.budget -= 1;
        self.visits += 1;
        match *self.program.types.get(ty) {
            Ty::Reference {
                region,
                inner,
                mutable,
            } => {
                let required = !matches!(region, Region::Infer(_));
                let mut valid = !required
                    || value.origins.iter().all(|origin| {
                        let actual = self.origin_region(origin);
                        actual.is_some_and(|actual| {
                            self.contracts[self.function.definition.0 as usize]
                                .as_ref()
                                .unwrap()
                                .outlives(actual, RegionTerm::Declared(region))
                        })
                    });
                if !valid {
                    self.reporter.problem(Problem::Region { code, span });
                }
                // An inner named/static region is a separate obligation. Never
                // validate it by the outer pointer's type alone.
                if self.constrained(inner) {
                    for origin in &value.origins {
                        if let Origin::Borrow { place, .. } = origin {
                            if mutable
                                && !self
                                    .program
                                    .types
                                    .region_invariant(self.places.ty(*place), inner)
                            {
                                valid = false;
                                self.reporter.problem(Problem::ReferenceInvariant(span));
                                continue;
                            }
                            let data = self.value(*place, state);
                            valid &= self.typed_regions(inner, &data, state, span, code, depth + 1);
                        } else {
                            self.unsupported("this nested reference region", span);
                            valid = false;
                        }
                    }
                }
                valid
            }
            Ty::Array { inner, .. } | Ty::Slice(inner) => {
                self.typed_regions(inner, value, state, span, code, depth + 1)
            }
            _ => {
                let mut valid = true;
                if let Some(fields) = self.properties.fields(ty) {
                    let count = fields.len();
                    for index in 0..count {
                        let field_ty = self.properties.fields(ty).unwrap()[index];
                        let data = value
                            .fields
                            .as_ref()
                            .and_then(|v| v.get(index))
                            .unwrap_or(value);
                        valid &= self.typed_regions(field_ty, data, state, span, code, depth + 1);
                    }
                }
                valid
            }
        }
    }

    fn constrained(&mut self, ty: crate::types::TyId) -> bool {
        if !self.properties.get(ty).references {
            return false;
        }
        let mut pending = vec![ty];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if self.budget == 0 || seen.len() > 4096 {
                self.exhausted = true;
                return true;
            }
            self.budget -= 1;
            self.visits += 1;
            match *self.program.types.get(ty) {
                Ty::Reference { region, inner, .. } => {
                    if !matches!(region, Region::Infer(_)) {
                        return true;
                    }
                    pending.push(inner);
                }
                Ty::Array { inner, .. } | Ty::Slice(inner) => pending.push(inner),
                _ => {
                    if let Some(fields) = self.properties.fields(ty) {
                        pending.extend(fields.iter().copied());
                    }
                }
            }
        }
        false
    }

    fn check_return(&mut self, value: &Value, state: &State, span: Span) {
        let contracts = self.contracts;
        let contract = contracts[self.function.definition.0 as usize]
            .as_ref()
            .expect("function contract");
        if !contract.valid {
            return;
        }
        let mut valid = value.valid;
        if contract.reference_result {
            for origin in &value.origins {
                let allowed = match origin {
                    Origin::Static => true,
                    Origin::Borrow { place, .. } => self
                        .places
                        .input_source(*place)
                        .and_then(|source| self.input_positions[source.0 as usize])
                        .is_some_and(|input| contract.return_inputs.contains(&input)),
                    Origin::OpaqueInput(_) => {
                        self.unsupported("the returned reference's opaque input region", span);
                        false
                    }
                };
                valid &= allowed;
            }
            let diagnostic = (!valid && value.valid).then(|| Problem::RegionReturn {
                span,
                signature: self.program.definitions[self.function.definition].span,
            });
            self.finding(
                Predicate::ReturnRegion,
                span,
                valid,
                value.causes.clone(),
                diagnostic,
            );
        }
        self.typed_regions(
            self.function.result,
            value,
            state,
            span,
            "E-REGION-RETURN",
            0,
        );
    }
    fn live(&self) -> &Live {
        if let Some(id) = self.live_expression {
            self.liveness.expression(id)
        } else {
            self.liveness
                .operation(self.point.block, self.point.operation, self.after_store)
        }
    }
    fn block(&mut self, block: BlockId, state: &mut State) -> Vec<BlockId> {
        let graph = self.graph;
        for (index, operation) in graph.blocks[block.0 as usize].operations.iter().enumerate() {
            self.point.operation = index as u32;
            self.point.evaluation = 0;
            self.live_expression = None;
            self.after_store = false;
            state.temporaries.clear();
            state.drop_temporaries.clear();
            self.operation(operation, state);
            state.temporaries.clear();
            state.drop_temporaries.clear();
            if !state.normal {
                return Vec::new();
            }
            if self.exhausted || !state.bounded() {
                self.exhausted = true;
                return Vec::new();
            }
        }
        self.point.operation = graph.blocks[block.0 as usize].operations.len() as u32;
        self.point.evaluation = 0;
        match graph.blocks[block.0 as usize].exit {
            Exit::Goto(target) => vec![target],
            Exit::Branch { condition, yes, no } => {
                if let Some(condition) = condition {
                    self.eval(condition, Mode::Value, state);
                    state.temporaries.clear();
                    state.drop_temporaries.clear();
                    if !state.normal {
                        return Vec::new();
                    }
                    match self.boolean(condition) {
                        Some(true) => vec![yes],
                        Some(false) => vec![no],
                        None => vec![yes, no],
                    }
                } else {
                    vec![yes]
                }
            }
            Exit::Iterate { yes, no } => vec![yes, no],
            Exit::Stop => {
                self.normal_exit = state.normal;
                Vec::new()
            }
        }
    }

    fn operation(&mut self, operation: &Operation, state: &mut State) {
        match *operation {
            Operation::Parameter { local, event } => {
                for &index in self.places.owned_cells(local) {
                    let place = self.places.leaf(index);
                    let ty = self.places.ty(place);
                    let origins = match self.program.types.get(ty) {
                        Ty::Reference { mutable, .. } if self.places.input(place).is_some() => {
                            Origins::from([Origin::Borrow {
                                place: self.places.input(place).unwrap(),
                                precise: true,
                                event,
                                mutable: *mutable,
                                loan: LoanId::Input(place),
                                parents: LoanSetId(0),
                            }])
                        }
                        _ if self.properties.get(ty).references => {
                            Origins::from([Origin::OpaqueInput(place.0)])
                        }
                        _ => Origins::new(),
                    };
                    state.slots[index] = Slot {
                        flags: AVAILABLE,
                        origins,
                        causes: Causes::from([event]),
                        functions: BTreeSet::new(),
                        written: Written::Unwritten,
                    };
                }
            }
            Operation::Declare {
                local,
                initializer,
                event,
            } => {
                let mut value = initializer.map(|value| self.eval(value, Mode::Value, state));
                if !state.normal {
                    return;
                }
                if let Some(value) = &mut value {
                    value.valid &= self.typed_regions(
                        self.function.locals[local].ty,
                        value,
                        state,
                        self.function.locals[local].span,
                        "E-REGION-STORE",
                        0,
                    );
                }
                self.bind(
                    Places::root(local),
                    value.as_ref(),
                    event,
                    state,
                    Update::Strong,
                );
            }
            Operation::Evaluate(value) => {
                self.eval(value, Mode::Value, state);
            }
            Operation::Assign {
                target,
                value,
                compound,
                event,
            } => self.assign(target, value, compound, event, state),
            Operation::EndStorage { local, event } => {
                for index in self.places.leaves(Places::root(local)) {
                    state.slots[index] = Slot {
                        flags: DEAD,
                        origins: Origins::new(),
                        causes: Causes::from([event]),
                        functions: BTreeSet::new(),
                        written: Written::Unwritten,
                    };
                }
                let loans: BTreeSet<_> = state
                    .active_borrows(Places::root(local), self.places, self.live())
                    .into_iter()
                    .map(|(_, event, _)| event)
                    .collect();
                let span = self.graph.event(event).span;
                let diagnostic = loans
                    .first()
                    .map(|&loan| Problem::StorageEnd { span, loan });
                self.finding(
                    Predicate::StorageMayEnd(local),
                    span,
                    loans.is_empty(),
                    loans.into_iter().chain([event]).collect(),
                    diagnostic,
                );
            }
            Operation::Return { value, span } => {
                if let Some(value) = value {
                    let value = self.eval(value, Mode::Value, state);
                    if !state.normal {
                        return;
                    }
                    let local = value.origins.iter().find_map(|origin| match origin {
                        Origin::Borrow { place, event, .. }
                            if self.places.input_source(*place).is_none() =>
                        {
                            Some((self.places.owner(*place).0, *event))
                        }
                        _ => None,
                    });
                    let diagnostic = local.map(|(owner, event)| Problem::LocalReturn {
                        span,
                        storage: self.function.locals[owner as usize].span,
                        borrow: self.graph.event(event).span,
                    });
                    self.finding(
                        Predicate::ReturnDoesNotBorrowLocalStorage,
                        span,
                        value.valid && local.is_none(),
                        value.causes.clone(),
                        diagnostic,
                    );
                    if local.is_none() {
                        self.check_return(&value, state, span);
                    }
                    state.returned = Some(value);
                } else {
                    state.returned = Some(Value::scalar());
                }
            }
            Operation::IterationStart { slot, value, event } => {
                let supported = self
                    .properties
                    .get(self.function.expressions[value].ty)
                    .copy;
                if !supported {
                    self.unsupported("iteration of a non-Copy iterable", self.expr_span(value));
                }
                let mut value = self.eval(value, Mode::Value, state);
                if !state.normal {
                    return;
                }
                value.valid &= supported;
                self.bind(
                    Places::root(slot),
                    Some(&value),
                    event,
                    state,
                    Update::Strong,
                );
            }
            Operation::IterationValue { slot, local, event } => {
                let supported = self.properties.get(self.function.locals[local].ty).copy;
                if !supported {
                    self.unsupported(
                        "iteration of non-Copy elements",
                        self.function.locals[local].span,
                    );
                }
                let source = self.summary(Places::root(slot), state);
                let value = Value {
                    valid: source.flags == AVAILABLE && supported,
                    origins: if self
                        .properties
                        .get(self.function.locals[local].ty)
                        .references
                    {
                        source.origins
                    } else {
                        Origins::new()
                    },
                    causes: source.causes,
                    fields: None,
                    functions: source.functions,
                };
                self.bind(
                    Places::root(local),
                    Some(&value),
                    event,
                    state,
                    Update::Strong,
                );
            }
        }
    }

    /// A store validates its actual destination type, then chooses exact or
    /// conservative updates. RHS loans are live before the destination changes.
    fn assign(
        &mut self,
        target: ExprId,
        value: ExprId,
        compound: bool,
        event: EventId,
        state: &mut State,
    ) {
        let target_span = self.expr_span(target);
        let targets = self.place(target, true, state);
        let mut target_valid = true;
        if compound && let Some(targets) = &targets {
            target_valid = self
                .load(target, targets, Mode::Inspect { write: true }, state)
                .valid;
        }
        let mut value = self.eval(value, Mode::Value, state);
        if !state.normal {
            return;
        }
        value.valid &= target_valid;
        value.valid &= self.typed_regions(
            self.function.expressions[target].ty,
            &value,
            state,
            target_span,
            "E-REGION-STORE",
            0,
        );
        // A reference produced by the RHS is already live at the store.
        // Otherwise `owner.field = &owner` could evade the conflict check.
        state.temporaries.push(value.origins.clone());
        self.after_store = true;
        if let Some(targets) = targets {
            for target in &targets {
                value.valid &= self.access(target, Access::Write, target_span, state);
                if let Target::Place { place, .. } = target {
                    value.valid &= self.typed_regions(
                        self.places.ty(*place),
                        &value,
                        state,
                        target_span,
                        "E-REGION-STORE",
                        0,
                    );
                    value.valid &= self.input_store(*place, &value, target_span);
                }
            }
            let strong = targets.len() == 1;
            for target in targets {
                match target {
                    Target::Place {
                        place,
                        precise: true,
                        ..
                    } => {
                        let live_storage = self
                            .places
                            .leaves(place)
                            .all(|i| state.slots[i].flags & DEAD == 0);
                        if !live_storage {
                            self.available(place, target_span, state);
                            continue;
                        }
                        self.bind(
                            place,
                            Some(&value),
                            event,
                            state,
                            if strong { Update::Strong } else { Update::Weak },
                        );
                    }
                    Target::Place { place, .. } => {
                        if !self.available(place, target_span, state) {
                            continue;
                        }
                        self.bind(place, Some(&value), event, state, Update::Weak);
                    }
                    _ if !value.origins.is_empty() => self.unsupported(
                        "storing borrowed values through an indirect place",
                        target_span,
                    ),
                    _ => {}
                }
            }
        } else {
            self.unsupported("this assignment place", target_span);
        }
    }

    fn bind(
        &self,
        place: PlaceId,
        value: Option<&Value>,
        event: EventId,
        state: &mut State,
        update: Update,
    ) {
        let children = self.places.children(place);
        if !children.is_empty() {
            for (index, &child) in children.iter().enumerate() {
                let field = value.map(|value| {
                    if value.valid {
                        value
                            .fields
                            .as_ref()
                            .and_then(|f| f.get(index))
                            .unwrap_or(value)
                    } else {
                        value
                    }
                });
                self.bind(child, field, event, state, update);
            }
            return;
        }
        let mut slot = match value {
            Some(value) => Slot {
                flags: if value.valid { AVAILABLE } else { POISON },
                origins: if self.properties.get(self.places.ty(place)).references {
                    value.origins.clone()
                } else {
                    Origins::new()
                },
                causes: value.causes.clone(),
                functions: value.functions.clone(),
                written: if self.places.input_source(place).is_some() {
                    Written::Definite
                } else {
                    Written::Unwritten
                },
            },
            None => Slot {
                flags: UNINITIALIZED,
                origins: Origins::new(),
                causes: Causes::new(),
                functions: BTreeSet::new(),
                written: Written::Unwritten,
            },
        };
        slot.causes.insert(event);
        let index = self.places.leaves(place).start;
        if update == Update::Weak {
            // The selected address/path is uncertain. Retain the untouched
            // state, including its loans and callable targets, as an alternative.
            state.slots[index].flags |= slot.flags;
            state.slots[index].written = state.slots[index].written.join(slot.written);
            state.slots[index].functions.extend(slot.functions);
            state.slots[index].origins.extend(slot.origins);
            state.slots[index].causes.extend(slot.causes);
        } else {
            state.slots[index] = slot;
        }
    }

    fn summary(&mut self, place: PlaceId, state: &State) -> PlaceState {
        let mut result = PlaceState {
            flags: 0,
            origins: Origins::new(),
            causes: Causes::new(),
            functions: BTreeSet::new(),
        };
        for index in self.places.leaves(place) {
            let slot = &state.slots[index];
            result.flags |= slot.flags;
            result.functions.extend(&slot.functions);
            result.origins.extend(slot.origins.iter().cloned());
            result.causes.extend(slot.causes.iter().copied());
            if result.origins.len() > MAX_ORIGINS || result.causes.len() > 128 {
                self.exhausted = true;
                result.flags = POISON;
                break;
            }
        }
        result
    }

    fn value(&mut self, place: PlaceId, state: &State) -> Value {
        let slot = self.summary(place, state);
        let fields = if self.properties.get(self.places.ty(place)).references
            && !self.places.children(place).is_empty()
        {
            let count = self.places.children(place).len();
            Some(
                (0..count)
                    .map(|index| {
                        let child = self.places.children(place)[index];
                        self.value(child, state)
                    })
                    .collect(),
            )
        } else {
            None
        };
        Value {
            valid: slot.flags == AVAILABLE,
            origins: slot.origins,
            causes: slot.causes,
            fields,
            functions: slot.functions,
        }
    }

    fn eval(&mut self, id: ExprId, mode: Mode, state: &mut State) -> Value {
        if !state.normal {
            return Value::default();
        }
        if self.budget == 0 || self.depth >= 128 || self.expression_frames >= 256 {
            self.exhausted = true;
            return Value::default();
        }
        self.budget -= 1;
        self.visits += 1;
        let nested = usize::from(!matches!(
            self.function.expressions[id].kind,
            H::Binary { .. }
        ));
        self.depth += nested;
        self.expression_frames += 1;
        let base = state.temporaries.len();
        let previous = self.live_expression.replace(id);
        let mut value = self.eval_inner(id, mode, state);
        if self
            .properties
            .get(self.function.expressions[id].ty)
            .may_drop
        {
            // Unconsumed aggregate/rvalue cleanup may use these references at
            // the full-expression boundary; NLL must not end them mid-expression.
            state.drop_temporaries.extend(value.origins.iter().cloned());
            if state.drop_temporaries.len() > MAX_ORIGINS {
                self.exhausted = true;
            }
        }
        self.live_expression = previous;
        if value.origins.len() > MAX_ORIGINS || value.causes.len() > 128 {
            self.exhausted = true;
            value.valid = false;
        }
        state.temporaries.truncate(base);
        self.depth -= nested;
        self.expression_frames -= 1;
        value
    }

    fn eval_inner(&mut self, id: ExprId, mode: Mode, state: &mut State) -> Value {
        let function = self.function;
        let node = &function.expressions[id];
        match &node.kind {
            H::Constant(value) => {
                let mut result = Value::scalar();
                if matches!(value, hir::Constant::String(_)) {
                    result.origins.insert(Origin::Static);
                }
                result
            }
            H::Definition(definition) => {
                let def = &self.program.definitions[definition];
                if def.kind == hir::DefinitionKind::Function
                    && (!self.contracts[definition.0 as usize]
                        .as_ref()
                        .is_some_and(|c| c.has_body)
                        || def.foreign_abi.is_some())
                {
                    self.unsupported(
                        "a managed callable value without a checked Cavo body",
                        node.span,
                    );
                    Value::default()
                } else {
                    let mut value = Value::scalar();
                    if def.kind == hir::DefinitionKind::Function {
                        value.functions.insert(*definition);
                    }
                    value
                }
            }
            H::Group(inner) | H::CoerceArrayToSlice(inner) => self.eval(*inner, mode, state),
            H::Unary {
                op: UnaryOp::Move,
                operand,
            } => self.eval(
                *operand,
                Mode::Move(self.graph.expression_events[id.0 as usize].expect("move event")),
                state,
            ),
            H::Unary {
                op: UnaryOp::Borrow | UnaryOp::BorrowMut,
                operand,
            } => {
                let mutable = matches!(
                    node.kind,
                    H::Unary {
                        op: UnaryOp::BorrowMut,
                        ..
                    }
                );
                let event = self.graph.expression_events[id.0 as usize].expect("borrow event");
                let mut value = Value::scalar();
                if let Some(targets) = self.place(*operand, mutable, state) {
                    if !state.normal {
                        return Value::default();
                    }
                    for target in targets {
                        if let Target::Place {
                            place,
                            precise,
                            via,
                            ..
                        } = target
                        {
                            if self.places.input_source(place).is_none() {
                                value.valid &= self.available(place, node.span, state);
                                value.causes.extend(self.summary(place, state).causes);
                            }
                            value.valid &= self.access(
                                &target,
                                if mutable {
                                    Access::BorrowExclusive
                                } else {
                                    Access::BorrowShared
                                },
                                node.span,
                                state,
                            );
                            // Borrowing a container must also respect the
                            // capabilities it exposes. A frozen parent &mut
                            // cannot be smuggled into another call via &&mut.
                            let contained = self.value(place, state);
                            value.valid &= self.capabilities(
                                &contained.origins,
                                mutable,
                                false,
                                node.span,
                                state,
                            );
                            let parents = self.lineage(via, None, Some(LoanId::Borrow(event)));
                            if via != LoanSetId(0) {
                                self.reporter.reborrow(
                                    self.point,
                                    LoanId::Borrow(event),
                                    event,
                                    &self.loans.values[parents.0 as usize],
                                );
                            }
                            value.origins.insert(Origin::Borrow {
                                place,
                                precise,
                                event,
                                mutable,
                                loan: LoanId::Borrow(event),
                                parents,
                            });
                        } else if matches!(target, Target::Static) && !mutable {
                            value.origins.insert(Origin::Static);
                        } else {
                            self.unsupported("this reborrow's provenance", node.span);
                            value.valid = false;
                        }
                    }
                } else {
                    self.unsupported("borrowing temporary storage", node.span);
                    value.valid = false;
                }
                value.causes.insert(event);
                value
            }
            H::Local(_)
            | H::Field { .. }
            | H::Index { .. }
            | H::Unary {
                op: UnaryOp::Dereference,
                ..
            } => {
                let property = self.properties.get(node.ty);
                let write = matches!(mode, Mode::Inspect { write: true })
                    || (matches!(mode, Mode::Move(_)) && !property.copy);
                if let Some(targets) = self.place(id, write, state) {
                    self.load(id, &targets, mode, state)
                } else if let H::Field { base, .. } | H::Index { base, .. } = node.kind {
                    let mut value = self.eval(base, Mode::Value, state);
                    state.temporaries.push(value.origins.clone());
                    if let H::Index { index, .. } = node.kind {
                        let index = self.eval(index, Mode::Value, state);
                        value.valid &= index.valid;
                    } else if let H::Field { index, .. } = node.kind
                        && let Some(fields) = value.fields.take()
                    {
                        let valid = value.valid;
                        if let Some(field) = fields.into_iter().nth(index as usize) {
                            value = field;
                            value.valid &= valid;
                        } else {
                            self.unsupported("this temporary record field's identity", node.span);
                            value.valid = false;
                        }
                    }
                    state.temporaries.pop();
                    if !property.references {
                        value.origins.clear();
                    }
                    value
                } else {
                    self.unsupported("this reference/place expression", node.span);
                    Value::default()
                }
            }
            H::Unary { operand, .. } => self.eval(*operand, Mode::Value, state),
            H::Binary { op, left, right } => {
                let condition = self.boolean(*left);
                let left = self.eval(*left, Mode::Value, state);
                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                    let skip = matches!(
                        (op, condition),
                        (BinaryOp::And, Some(false)) | (BinaryOp::Or, Some(true))
                    );
                    if skip {
                        return left;
                    }
                    let before = state.clone();
                    let right = self.eval(*right, Mode::Value, state);
                    if !state.normal && condition.is_none() {
                        // Only the skipped RHS path can return normally. A
                        // diverging alternative must not poison that value.
                        *state = before;
                        return left;
                    }
                    if condition.is_none() {
                        state.merge(&before);
                    }
                    let mut value = left;
                    value.combine(&right);
                    value.origins.clear();
                    value
                } else {
                    state.temporaries.push(left.origins.clone());
                    let right = self.eval(*right, Mode::Value, state);
                    state.temporaries.pop();
                    let mut value = left;
                    value.combine(&right);
                    value.origins.clear();
                    value
                }
            }
            H::Call {
                callee,
                arguments,
                parameter_types,
                ..
            } => self.eval_call(id, callee, arguments, parameter_types, state),
            H::Array(elements) => self.aggregate(elements.iter().copied(), state),
            H::Repeat { value, .. } => self.eval(*value, Mode::Value, state),
            H::Record { fields, .. } => {
                let Some(types) = self.properties.fields(node.ty) else {
                    self.unsupported("this record initializer's move paths", node.span);
                    return Value::default();
                };
                let mut parts = vec![Value::default(); types.len()];
                let mut result = Value::scalar();
                let base = state.temporaries.len();
                state.temporaries.push(Origins::new());
                for &(index, expression) in fields {
                    let value = self.eval(expression, Mode::Value, state);
                    result.combine(&value);
                    let Some(part) = parts.get_mut(index as usize) else {
                        self.unsupported("this record initializer's field identity", node.span);
                        result.valid = false;
                        break;
                    };
                    *part = value;
                    state.temporaries[base] = result.origins.clone();
                    if self.exhausted
                        || result.origins.len() > MAX_ORIGINS
                        || result.causes.len() > 128
                    {
                        self.exhausted = true;
                        break;
                    }
                }
                state.temporaries.truncate(base);
                result.fields = Some(parts);
                result
            }
            H::Old(_)
            | H::Spawn { .. }
            | H::Error
            | H::ConstTerm(_)
            | H::RepeatConst { .. }
            | H::Match { .. }
            | H::BlockValue { .. }
            | H::IsVariant { .. }
            | H::VariantField { .. }
            | H::DynCoerce { .. }
            | H::DynCall { .. } => {
                self.unsupported("this expression in local ownership analysis", node.span);
                Value::default()
            }
        }
    }

    /// Evaluate arguments in source order and keep their loans until the call
    /// finishes. Entry snapshots are resolved before any caller memory update.
    fn eval_call(
        &mut self,
        id: ExprId,
        callee: &ExprId,
        arguments: &[ExprId],
        parameter_types: &[crate::types::TyId],
        state: &mut State,
    ) -> Value {
        let function = self.function;
        let node = &function.expressions[id];
        let result_property = self.properties.get(node.ty);

        let direct = self.definition(*callee);
        let callee_value = if direct.is_some() {
            Value::scalar()
        } else {
            self.eval(*callee, Mode::Value, state)
        };
        let mut value = Value::scalar();
        value.valid &= callee_value.valid;
        let base = state.temporaries.len();
        state.temporaries.push(Origins::new());
        let mut actual = Vec::with_capacity(arguments.len());
        for &argument in arguments {
            let argument = self.eval(argument, Mode::Value, state);
            value.combine(&argument);
            state.temporaries[base] = value.origins.clone();
            actual.push(argument);
            if self.exhausted || value.origins.len() > MAX_ORIGINS || value.causes.len() > 128 {
                self.exhausted = true;
                break;
            }
        }
        for (&ty, actual) in parameter_types.iter().zip(&actual) {
            value.valid &= self.typed_regions(ty, actual, state, node.span, "E-REGION-ARG", 0);
        }
        if !value.valid {
            state.temporaries.truncate(base);
            return Value::default();
        }
        let known = direct.is_some_and(|definition| {
            self.contracts[definition.0 as usize]
                .as_ref()
                .is_some_and(|c| c.has_body)
                || self
                    .external
                    .functions
                    .get(definition.0 as usize)
                    .is_some_and(Option::is_some)
                || matches!(
                    self.program.definitions[definition].kind,
                    hir::DefinitionKind::Variant { .. }
                )
        }) || direct.is_none();
        let indirect_contract = direct.is_none().then(|| {
            let (contract, problem) = super::regions::signature(
                super::regions::Signature {
                    definition: self.function.definition,
                    parameters: parameter_types,
                    result: node.ty,
                    span: node.span,
                    has_body: true,
                },
                self.program,
                self.properties,
            );
            if let Some(problem) = problem {
                self.unsupported_problem(node.span, Problem::Signature(problem));
            }
            contract
        });
        if !known {
            if let Some(summary) =
                direct.and_then(|id| self.external.reports.iter().find(|s| s.function == id))
                && summary.status == crate::external::SummaryStatus::Untrusted
            {
                self.unsupported_problem(
                    node.span,
                    Problem::Untrusted {
                        span: node.span,
                        summary,
                    },
                );
            } else {
                self.unsupported(
                    "calls without an analyzed Cavo body or a supported trusted summary",
                    node.span,
                );
            }
            value.valid = false;
        }
        let mut targets = BTreeSet::new();
        if let Some(id) = direct {
            if self.contracts[id.0 as usize]
                .as_ref()
                .is_some_and(|c| c.has_body)
                || self
                    .external
                    .functions
                    .get(id.0 as usize)
                    .and_then(Option::as_ref)
                    .is_some_and(|b| b.memory.is_some())
            {
                targets.insert(id);
            }
        } else {
            targets.extend(&callee_value.functions);
        }
        if !targets.is_empty() {
            let before = state.clone();
            let mut after = None;
            let mut returned = None;
            let event = self.graph.expression_events[id.0 as usize].expect("call event");
            for target in targets {
                self.reporter.dependency(target);
                let mut branch = before.clone();
                let memory = if let Some(binding) = self
                    .external
                    .functions
                    .get(target.0 as usize)
                    .and_then(Option::as_ref)
                {
                    binding.memory.as_ref()
                } else {
                    match &self.summaries[target.0 as usize] {
                        Inferred::Ready(summary) => Some(summary),
                        Inferred::Unknown => None,
                    }
                };
                let result = match (memory, self.contracts[target.0 as usize].as_ref()) {
                    (Some(summary), Some(contract)) => self.apply_memory(
                        summary,
                        contract,
                        &actual,
                        memory::Invocation {
                            event,
                            target,
                            span: node.span,
                        },
                        &mut branch,
                    ),
                    _ => {
                        self.unsupported("an unresolved source memory effect summary", node.span);
                        Value::default()
                    }
                };
                if branch.normal {
                    if let Some(previous) = &mut after {
                        State::merge(previous, &branch);
                    } else {
                        after = Some(branch);
                    }
                    if let Some(previous) = &mut returned {
                        memory::join_value(previous, &result);
                    } else {
                        returned = Some(result);
                    }
                }
            }
            if let Some(after) = after {
                *state = after;
            } else {
                state.normal = false;
            }
            let mut result = returned.unwrap_or_default();
            result.valid &= value.valid;
            // Precise pointer writes do not certify opaque Drop. Keep
            // the previous conservative cleanup footprint until that
            // effect analysis exists, including rvalue cleanup uses.
            if result_property.may_drop {
                result.origins.extend(value.origins.iter().cloned());
                result.causes.extend(&value.causes);
            }
            result.valid &=
                self.typed_regions(node.ty, &result, state, node.span, "E-REGION-CALL", 0);
            state.temporaries.truncate(base);
            return result;
        }
        if direct.is_none()
            && indirect_contract.as_ref().is_some_and(|c| {
                c.inputs.iter().any(|i| {
                    i.mutable == Some(true)
                        && i.pointee.is_some_and(|ty| {
                            self.properties.get(ty).references || self.contains_callable(ty)
                        })
                })
            })
        {
            self.unsupported(
                "a callable parameter with unknown reference or function-pointer write effects",
                node.span,
            );
            value.valid = false;
        }
        if direct.is_none()
            && let Some(contract) = &indirect_contract
            && contract.reference_result
        {
            let event = self.graph.expression_events[id.0 as usize].expect("call event");
            let mut result = self.callable_reference(
                contract,
                &actual,
                memory::Invocation {
                    event,
                    target: self.function.definition,
                    span: node.span,
                },
                state,
                node.ty,
            );
            result.valid &= value.valid;
            result.valid &=
                self.typed_regions(node.ty, &result, state, node.span, "E-REGION-CALL", 0);
            state.temporaries.truncate(base);
            return result;
        }
        if direct.is_none()
            && let Some(contract) = &indirect_contract
        {
            let effects = self.scalar_callback_effects(contract);
            let event = self.graph.expression_events[id.0 as usize].expect("call event");
            let result = self.apply_memory(
                &effects,
                contract,
                &actual,
                memory::Invocation {
                    event,
                    target: self.function.definition,
                    span: node.span,
                },
                state,
            );
            value.valid &= result.valid;
        }
        if result_property.references {
            if known
                && let Some(contract) = direct
                    .and_then(|id| self.contracts[id.0 as usize].as_ref())
                    .or(indirect_contract.as_ref())
            {
                value.valid &= contract.valid;
                if contract.reference_result {
                    value.origins.clear();
                    let mutable = matches!(
                        self.program.types.get(node.ty),
                        Ty::Reference { mutable: true, .. }
                    );
                    for &index in &contract.return_inputs {
                        let input = &contract.inputs[index];
                        if let Some(argument) = actual.get(input.parameter as usize) {
                            let (argument, exact) =
                                self.argument_path(argument, &input.path, state, node.span);
                            let shape = input
                                .pointee
                                .zip(contract.result_pointee)
                                .is_some_and(|(a, b)| self.program.types.compatible(a, b));
                            for origin in &argument.origins {
                                let mut origin = origin.clone();
                                if let Origin::Borrow {
                                    mutable: permission,
                                    precise,
                                    ..
                                } = &mut origin
                                {
                                    *permission &= mutable;
                                    *precise &= shape && exact;
                                }
                                value.origins.insert(origin);
                            }
                        }
                    }
                    if contract.return_inputs.is_empty() && contract.static_result {
                        value.origins.insert(Origin::Static);
                    }
                }
                if value.origins.is_empty() && contract.inputs.is_empty() {
                    value.origins.insert(Origin::Static);
                }
            }
            if value.origins.is_empty() {
                self.unsupported("a call result's reference origin", node.span);
                value.valid = false;
            }
            value.valid &=
                self.typed_regions(node.ty, &value, state, node.span, "E-REGION-CALL", 0);
        } else {
            value.origins.clear();
        }
        state.temporaries.truncate(base);
        value
    }

    fn aggregate(&mut self, values: impl Iterator<Item = ExprId>, state: &mut State) -> Value {
        let base = state.temporaries.len();
        let mut result = Value::scalar();
        state.temporaries.push(Origins::new());
        for value in values {
            let value = self.eval(value, Mode::Value, state);
            result.combine(&value);
            if self.exhausted || result.origins.len() > MAX_ORIGINS || result.causes.len() > 128 {
                self.exhausted = true;
                result.valid = false;
                break;
            }
            state.temporaries[base] = result.origins.clone();
        }
        state.temporaries.truncate(base);
        result
    }

    fn place(&mut self, id: ExprId, write: bool, state: &mut State) -> Option<Vec<Target>> {
        if self.place_depth >= 128 {
            self.exhausted = true;
            return Some(vec![Target::Invalid]);
        }
        self.place_depth += 1;
        let result = self.place_inner(id, write, state);
        self.place_depth -= 1;
        result
    }
    fn place_inner(&mut self, id: ExprId, write: bool, state: &mut State) -> Option<Vec<Target>> {
        let function = self.function;
        match function.expressions[id].kind {
            H::Local(owner) => Some(vec![Target::Place {
                place: Places::root(owner),
                precise: true,
                via: LoanSetId(0),
                projected: false,
                mutable: true,
            }]),
            H::Group(inner) => self.place(inner, write, state),
            H::Field { base, .. } | H::Index { base, .. } => {
                let reference = matches!(
                    self.program.types.get(function.expressions[base].ty),
                    Ty::Reference { .. }
                );
                let mut targets = if reference {
                    Some(self.reference_targets(base, write, state))
                } else {
                    self.place(base, write, state)
                };
                if let H::Index { index, .. } = function.expressions[id].kind
                    && let Some(targets) = &mut targets
                    && !self.eval(index, Mode::Value, state).valid
                {
                    targets.push(Target::Invalid);
                }
                if let Some(targets) = &mut targets {
                    if let H::Field { index, .. } = function.expressions[id].kind {
                        let mut ty = function.expressions[base].ty;
                        if let Ty::Reference { inner, .. } = self.program.types.get(ty) {
                            ty = *inner;
                        }
                        if !self.properties.record_field(ty, index, self.program) {
                            self.unsupported("this record field's identity", self.expr_span(id));
                            return Some(vec![Target::Invalid]);
                        }
                    }
                    for target in targets {
                        if let Target::Place {
                            place,
                            precise,
                            projected,
                            ..
                        } = target
                        {
                            *projected = true;
                            match function.expressions[id].kind {
                                H::Field { index, .. } if *precise => {
                                    let Some(field) = self.places.field(*place, index) else {
                                        self.exhausted = true;
                                        return Some(vec![Target::Invalid]);
                                    };
                                    *place = field;
                                }
                                H::Index { .. } => *precise = false,
                                _ => {}
                            }
                        }
                    }
                }
                targets
            }
            H::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => Some(self.reference_targets(operand, write, state)),
            _ => None,
        }
    }

    fn reference_targets(&mut self, id: ExprId, write: bool, state: &mut State) -> Vec<Target> {
        let value = self.eval(id, Mode::Inspect { write }, state);
        if !value.valid {
            return vec![Target::Invalid];
        }
        if value.origins.is_empty() {
            self.unsupported("this reference's origin", self.expr_span(id));
            return vec![Target::Opaque];
        }
        state.temporaries.push(value.origins.clone());
        // Keep a non-Copy reference handle alive while its destination/index is
        // evaluated. Reading the handle is allowed; moving/replacing it is not.
        if !self.properties.get(self.function.expressions[id].ty).copy
            && let Some((place, event)) = self.handle_place(id)
        {
            state.temporaries.push(Origins::from([Origin::Borrow {
                place,
                precise: true,
                event,
                mutable: false,
                loan: LoanId::Borrow(event),
                parents: LoanSetId(0),
            }]));
        }
        value
            .origins
            .into_iter()
            .map(|origin| match origin {
                Origin::Borrow {
                    place,
                    precise,
                    loan,
                    parents,
                    mutable,
                    ..
                } => {
                    let via = self.lineage(parents, Some(loan), None);
                    Target::Place {
                        place,
                        precise,
                        via,
                        projected: true,
                        mutable,
                    }
                }
                Origin::Static => Target::Static,
                Origin::OpaqueInput(_) => Target::Opaque,
            })
            .collect()
    }

    fn load(&mut self, id: ExprId, targets: &[Target], mode: Mode, state: &mut State) -> Value {
        let node = &self.function.expressions[id];
        let property = self.properties.get(node.ty);
        let mut result = Value::scalar();
        let mut copied_value = false;
        for target in targets {
            let moving = matches!(mode, Mode::Move(_)) && !property.copy;
            result.valid &= self.access(
                target,
                if moving || matches!(mode, Mode::Inspect { write: true }) {
                    Access::Write
                } else {
                    Access::Read
                },
                node.span,
                state,
            );
            match target {
                Target::Place {
                    place,
                    via,
                    projected,
                    precise,
                    ..
                } => {
                    result.valid &= self.available(*place, node.span, state);
                    let value = self.value(*place, state);
                    let valid = result.valid;
                    if !copied_value {
                        result = value;
                        copied_value = true;
                    } else {
                        result.combine(&value);
                    }
                    result.valid &= valid;
                    if !property.references {
                        result.origins.clear();
                        result.fields = None;
                    }
                    if matches!(mode, Mode::Value) && !property.copy {
                        self.finding(
                            Predicate::ExplicitMove,
                            node.span,
                            false,
                            result.causes.clone(),
                            Some(Problem::ExplicitMove(node.span)),
                        );
                        result.valid = false;
                    }
                    if moving {
                        if !self.move_preserves_drop(*place, node.span, &result.causes) {
                            result.valid = false;
                        } else if *via != LoanSetId(0) {
                            self.unsupported(
                                "moving a non-Copy value out of a reference",
                                node.span,
                            );
                            result.valid = false;
                        } else if !precise {
                            self.unsupported("moving a non-Copy indexed value", node.span);
                            result.valid = false;
                        } else if let Mode::Move(event) = mode {
                            for index in self.places.leaves(*place) {
                                let slot = &mut state.slots[index];
                                slot.flags = (slot.flags & !AVAILABLE) | MOVED;
                                slot.origins.clear();
                                slot.causes = Causes::from([event]);
                            }
                            result.causes.insert(event);
                        }
                    }
                    if *projected
                        && !precise
                        && property.references
                        && matches!(mode, Mode::Inspect { .. })
                        && !property.copy
                    {
                        self.unsupported("inspecting an indexed mutable reference", node.span);
                        result.valid = false;
                    }
                }
                Target::Static => {
                    if property.references {
                        result.origins.insert(Origin::Static);
                    }
                }
                Target::Opaque => {
                    self.unsupported("the projected reference's provenance", node.span);
                    result.valid = false;
                }
                Target::Invalid => result.valid = false,
            }
        }
        if matches!(mode, Mode::Value | Mode::Move(_)) {
            result.valid &= self.capabilities(
                &result.origins,
                true,
                matches!(mode, Mode::Move(_)),
                node.span,
                state,
            );
        }
        result
    }

    fn move_preserves_drop(&mut self, mut place: PlaceId, span: Span, causes: &Causes) -> bool {
        while let Some(parent) = self.places.parent(place) {
            if self.properties.user_drop(self.places.ty(parent)) {
                self.finding(
                    Predicate::MovePreservesDrop,
                    span,
                    false,
                    causes.clone(),
                    Some(Problem::DropPartialMove(span)),
                );
                return false;
            }
            place = parent;
        }
        true
    }

    fn capabilities(
        &mut self,
        origins: &Origins,
        exclusive: bool,
        transferring: bool,
        span: Span,
        state: &State,
    ) -> bool {
        let mut pending: Vec<_> = origins
            .iter()
            .cloned()
            .map(|o| (o, exclusive, transferring))
            .collect();
        let mut seen = HashSet::new();
        let mut valid = true;
        while let Some((origin, exclusive, transfer)) = pending.pop() {
            if let Origin::Borrow {
                place,
                precise,
                mutable,
                loan,
                parents,
                ..
            } = origin
            {
                let writable = exclusive && mutable;
                if !seen.insert((place, writable, loan, parents, transfer)) {
                    continue;
                }
                if seen.len() > 4096 || self.budget == 0 {
                    self.exhausted = true;
                    return false;
                }
                self.budget -= 1;
                self.visits += 1;
                // The consumed root slot is already dead. A same-ID loan in
                // another live holder must still conflict; ancestors may remain.
                let via = if writable && transfer {
                    parents
                } else {
                    self.lineage(parents, Some(loan), None)
                };
                valid &= self.access(
                    &Target::Place {
                        place,
                        precise,
                        via,
                        mutable,
                        projected: true,
                    },
                    if writable && transfer {
                        Access::Transfer
                    } else if writable {
                        Access::Write
                    } else {
                        Access::Read
                    },
                    span,
                    state,
                );
                let data = self.value(place, state);
                pending.extend(data.origins.into_iter().map(|o| (o, writable, false)));
            }
        }
        valid
    }

    fn available(&mut self, place: PlaceId, span: Span, state: &State) -> bool {
        let slot = self.summary(place, state);
        let local = self.places.owner(place);
        let valid = slot.flags == AVAILABLE;
        let diagnostic = (!valid && slot.flags != POISON).then_some(Problem::Availability {
            span,
            binding: self.function.locals.get_id(local).map(|l| l.span),
            flags: slot.flags,
            causes: &slot.causes,
        });
        self.finding(
            Predicate::Available(place),
            span,
            valid,
            slot.causes.clone(),
            diagnostic,
        );
        valid
    }

    fn access(&mut self, target: &Target, access: Access, span: Span, state: &State) -> bool {
        let write = !matches!(access, Access::Read | Access::BorrowShared);
        match target {
            Target::Place {
                place,
                via,
                mutable,
                ..
            } => {
                if write && !mutable {
                    return self.shared_write(span);
                }
                let conflicts: BTreeSet<_> = state
                    .active_borrows(*place, self.places, self.live())
                    .into_iter()
                    .filter_map(|(loan, event, mutable)| {
                        (!self.loans.contains(*via, loan) && (write || mutable)).then_some(event)
                    })
                    .collect();
                let diagnostic = conflicts
                    .first()
                    .map(|&loan| Problem::Conflict { span, loan });
                self.finding(
                    Predicate::NoLoanConflict(*place),
                    span,
                    conflicts.is_empty(),
                    conflicts.iter().copied().collect(),
                    diagnostic,
                );
                conflicts.is_empty()
            }
            Target::Static => {
                if write {
                    self.shared_write(span)
                } else {
                    true
                }
            }
            Target::Opaque => {
                self.unsupported("this access's reference capability", span);
                false
            }
            Target::Invalid => false,
        }
    }

    fn shared_write(&mut self, span: Span) -> bool {
        self.finding(
            Predicate::ReferenceAllowsWrite,
            span,
            false,
            Causes::new(),
            Some(Problem::SharedWrite(span)),
        );
        false
    }
    fn finding(
        &mut self,
        predicate: Predicate,
        span: Span,
        valid: bool,
        causes: Causes,
        problem: Option<Problem<'_>>,
    ) {
        let point = self.point;
        self.point.evaluation += 1;
        self.reporter.check(
            Check {
                point,
                span,
                predicate,
                assessment: if valid {
                    Assessment::Established
                } else {
                    Assessment::NotEstablished
                },
                causes: &causes,
            },
            problem,
        );
    }
    fn unsupported(&mut self, feature: &str, span: Span) {
        self.unsupported_problem(span, Problem::Unsupported { feature, span });
    }
    fn unsupported_problem(&mut self, span: Span, problem: Problem<'_>) {
        let point = self.point;
        self.point.evaluation += 1;
        self.reporter.check(
            Check {
                point,
                span,
                predicate: Predicate::SupportedLocalSemantics,
                assessment: Assessment::NotAnalyzed,
                causes: &Causes::new(),
            },
            Some(problem),
        );
    }
    fn expr_span(&self, id: ExprId) -> Span {
        self.function.expressions[id].span
    }
    fn definition(&self, mut id: ExprId) -> Option<hir::DefId> {
        for _ in 0..128 {
            match self.function.expressions[id].kind {
                H::Definition(id) => return Some(id),
                H::Group(inner) => id = inner,
                _ => return None,
            }
        }
        None
    }
    fn handle_place(&self, mut id: ExprId) -> Option<(PlaceId, EventId)> {
        for _ in 0..128 {
            match self.function.expressions[id].kind {
                H::Group(inner) => id = inner,
                _ => {
                    return self
                        .places
                        .direct(self.function, self.program, id)
                        .and_then(|(place, precise)| {
                            precise
                                .then_some(place)
                                .zip(self.graph.expression_events[id.0 as usize])
                        });
                }
            }
        }
        None
    }
    fn boolean(&self, id: ExprId) -> Option<bool> {
        super::cfg::constant_bool(self.function, id)
    }
}
