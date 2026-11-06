//! Borrow obligations checked on execution MIR, including its cleanup edges.
//! An established result covers this pass's local domain, never native codegen.

mod flow;
pub(crate) mod live;
pub(crate) use live::successors;
pub mod summary;

use super::*;
use crate::{local::properties::Properties, types::Ty};
use std::{
    collections::{BTreeSet, HashSet, VecDeque},
    fmt::Write,
};

type Loans = BTreeSet<LoanId>;
type CallSites = Vec<std::collections::BTreeMap<hir::DefId, [Vec<LoanId>; 3]>>;
const WORK_LIMIT: usize = 16_000_000;
const STATE_LIMIT: usize = 2_000_000;
const ORIGIN_LIMIT: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoanId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Established,
    Assumed,
    Unknown,
    Rejected,
}

#[derive(Debug)]
pub struct Report {
    pub functions: Vec<FunctionReport>,
    pub summaries: Vec<summary::FunctionSummary>,
}

#[derive(Debug)]
pub struct FunctionReport {
    pub definition: hir::DefId,
    pub verdict: Verdict,
    pub findings: Vec<Finding>,
    pub gaps: Vec<Gap>,
    pub loans: Vec<Loan>,
    pub assumptions: BTreeSet<crate::external::AssumptionId>,
}

#[derive(Debug)]
pub struct Loan {
    pub mutable: bool,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FindingKind {
    UntrackedOwner,
    UnknownRegion,
    TaskEscape,
    Conflict,
    SharedWrite,
    LocalEscape,
    DanglingReference,
    RegionMismatch,
}
impl FindingKind {
    pub fn message(self) -> &'static str {
        match self {
            Self::UntrackedOwner => {
                "cannot establish a tracked owner region for a reference derived from raw memory"
            }
            Self::UnknownRegion => {
                "cannot establish that the reference origin satisfies its required region"
            }
            Self::TaskEscape => "a scoped task capability may outlive its owning registry",
            Self::Conflict => "access may conflict with a live MIR loan",
            Self::SharedWrite => "write requires an exclusive reference capability",
            Self::LocalEscape => "a reference to local storage may escape the function",
            Self::DanglingReference => "a reference may access storage after its lifetime ended",
            Self::RegionMismatch => {
                "reference origin does not outlive its declared destination region"
            }
        }
    }
}

#[derive(Debug)]
pub struct Finding {
    pub kind: FindingKind,
    pub span: Span,
    pub block: BlockId,
    pub statement: Option<u32>,
    pub loan: Option<LoanId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GapKind {
    CallReferenceEffects,
    UnknownOrigin,
    ExternalReferenceStore,
    ReturnRegion,
    OpaqueDrop,
    RawPointer,
    BorrowGeneration,
    ResourceLimit,
}
impl GapKind {
    pub fn message(self) -> &'static str {
        match self {
            Self::CallReferenceEffects => "MIR call reference effects require a validated summary",
            Self::UnknownOrigin => "reference provenance is not established in this MIR domain",
            Self::ExternalReferenceStore => {
                "external reference storage requires interprocedural region checking"
            }
            Self::ReturnRegion => "returned input references require signature region refinement",
            Self::OpaqueDrop => "opaque Drop borrow/effect behavior is not established",
            Self::RawPointer => "raw pointer permissions are outside the local MIR borrow domain",
            Self::BorrowGeneration => "a loop may retain more than one generation of a borrow site",
            Self::ResourceLimit => "MIR borrow analysis exceeded its per-function resource budget",
        }
    }
}

#[derive(Debug)]
pub struct Gap {
    pub kind: GapKind,
    pub span: Span,
}

impl Report {
    pub fn dump(&self) -> String {
        let mut text = String::from(
            "MIR borrow analysis / local domain and call summaries; not a native certificate\n",
        );
        for function in &self.functions {
            let _ = writeln!(
                text,
                "  function #{}: {:?}, {} loan(s)",
                function.definition.0,
                function.verdict,
                function.loans.len()
            );
            for finding in &function.findings {
                let _ = writeln!(
                    text,
                    "    rejected bb{}: {} @file{}:{}..{}",
                    finding.block.0,
                    finding.kind.message(),
                    finding.span.file.0,
                    finding.span.start,
                    finding.span.end
                );
            }
            for gap in &function.gaps {
                let _ = writeln!(text, "    unknown: {}", gap.kind.message());
            }
            let _ = writeln!(text, "    assumed: {:?}", function.assumptions);
        }
        for summary in &self.summaries {
            let _ = writeln!(
                text,
                "  call summary #{}: complete={}, normal={}, panic={}, cancel={}, accesses={}",
                summary.definition.0,
                summary.complete,
                summary.normal.is_some(),
                summary.panic.is_some(),
                summary.cancel.is_some(),
                summary.accesses.len()
            );
        }
        text
    }
}

/// Validate the artifact before following IDs. HIR-local success is deliberately
/// not an input: these obligations are recomputed over the actual MIR edges.
pub fn analyze(mir: &Program, hir: &mut hir::Program) -> Result<Report, InvariantError> {
    analyze_with_summaries(mir, hir, &[])
}

pub fn analyze_with_summaries(
    mir: &Program,
    hir: &mut hir::Program,
    external: &[crate::external::SummaryReport],
) -> Result<Report, InvariantError> {
    mir.validate(hir)?;
    let properties = Properties::compute(hir);
    let summaries = summary::infer(mir, hir, &properties, external);
    let functions = mir
        .functions
        .iter()
        .map(|body| analyze_body(body, hir, &properties, &summaries))
        .collect();
    Ok(Report {
        functions,
        summaries: summaries.functions.into_iter().flatten().collect(),
    })
}

fn analyze_body(
    body: &Body,
    hir: &hir::Program,
    properties: &Properties,
    summaries: &summary::Summaries,
) -> FunctionReport {
    let mut report = FunctionReport {
        definition: body.definition,
        verdict: Verdict::Established,
        findings: Vec::new(),
        gaps: Vec::new(),
        loans: Vec::new(),
        assumptions: BTreeSet::new(),
    };
    let sites = Sites::build(body, hir, properties, summaries, &mut report.loans);
    let context = Context {
        body,
        hir,
        properties,
        summaries,
        sites,
        loans: &report.loans,
    };
    let mut recorder = Recorder::default();
    if summaries.functions[body.definition.0 as usize]
        .as_ref()
        .is_some_and(|summary| summary.limited)
    {
        recorder.gap(Point::entry(body), GapKind::ResourceLimit);
    }
    if !context.sites.complete {
        recorder.gap(Point::entry(body), GapKind::ResourceLimit);
        report.gaps = recorder.gaps;
        report.verdict = Verdict::Unknown;
        return report;
    }
    match live::Liveness::compute(body, properties) {
        Some(liveness) => match solve(&context, &liveness) {
            Some(inputs) => replay(&context, &liveness, &inputs, &mut recorder),
            None => recorder.gap(Point::entry(body), GapKind::ResourceLimit),
        },
        None => recorder.gap(Point::entry(body), GapKind::ResourceLimit),
    }
    report.findings = recorder.findings;
    report.gaps = recorder.gaps;
    report.assumptions = recorder.assumptions;
    report.verdict = verdict(&report);
    report
}

fn verdict(report: &FunctionReport) -> Verdict {
    if !report.findings.is_empty() {
        Verdict::Rejected
    } else if !report.gaps.is_empty() {
        Verdict::Unknown
    } else if !report.assumptions.is_empty() {
        Verdict::Assumed
    } else {
        Verdict::Established
    }
}

struct Sites {
    inputs: Vec<LoanId>,
    parameter_positions: Vec<Option<u32>>,
    borrows: Vec<Vec<Option<LoanId>>>,
    calls: Vec<std::collections::BTreeMap<hir::DefId, [Vec<LoanId>; 3]>>,
    static_loan: Option<LoanId>,
    iterations: Vec<std::collections::BTreeMap<Vec<summary::Step>, LoanId>>,
    complete: bool,
}
impl Sites {
    fn build(
        body: &Body,
        hir: &hir::Program,
        properties: &Properties,
        summaries: &summary::Summaries,
        loans: &mut Vec<Loan>,
    ) -> Self {
        let frame = summaries.frames[body.definition.0 as usize]
            .as_ref()
            .expect("function frame");
        let span = body.block(body.entry).span;
        let inputs = frame
            .inputs
            .iter()
            .map(|input| Self::push(loans, input.mutable, span))
            .collect();
        let mut parameter_positions = vec![None; body.locals.len()];
        let mut position = 0;
        for (index, local) in body.locals.iter().enumerate() {
            if local.kind == LocalKind::Parameter {
                parameter_positions[index] = Some(position);
                position += 1;
            }
        }
        let borrows = body
            .blocks
            .iter()
            .map(|block| {
                block
                    .statements
                    .iter()
                    .map(|statement| match statement.kind {
                        StatementKind::Assign {
                            value: Rvalue::Borrow { mutable, .. },
                            ..
                        } => Some(Self::push(loans, mutable, statement.span)),
                        _ => None,
                    })
                    .collect()
            })
            .collect();
        let (calls, mut complete) = Self::call_sites(body, hir, summaries, loans);
        let iterations = Self::iteration_sites(body, hir, properties, loans, &mut complete);
        let static_loan = summaries
            .static_origin
            .then(|| Self::push(loans, false, span));
        Self {
            inputs,
            parameter_positions,
            borrows,
            calls,
            static_loan,
            iterations,
            complete,
        }
    }
    fn call_sites(
        body: &Body,
        hir: &hir::Program,
        summaries: &summary::Summaries,
        loans: &mut Vec<Loan>,
    ) -> (CallSites, bool) {
        let mut candidates = summary::body_targets(body, hir);
        let initial: Vec<_> = candidates.iter().copied().collect();
        for definition in initial {
            if let Some(summary) = &summaries.functions[definition.0 as usize]
                && let Some(outcome) = &summary.normal
            {
                candidates.extend(&outcome.returned.functions);
            }
        }
        let mut complete = true;
        let mut calls = Vec::with_capacity(body.blocks.len());
        for block in &body.blocks {
            let mut sites = std::collections::BTreeMap::new();
            let targets = match &block.terminator {
                Terminator::Call {
                    callee: Operand::Function { definition, .. },
                    ..
                } => BTreeSet::from([*definition]),
                Terminator::Call { .. } | Terminator::DynCall { .. } => {
                    if candidates.len() > ORIGIN_LIMIT {
                        complete = false;
                        BTreeSet::new()
                    } else {
                        candidates.clone()
                    }
                }
                _ => BTreeSet::new(),
            };
            for target in targets {
                if let Some(summary) = &summaries.functions[target.0 as usize] {
                    let outcomes = [&summary.normal, &summary.panic, &summary.cancel];
                    let count: usize = outcomes
                        .iter()
                        .filter_map(|outcome| outcome.as_ref())
                        .map(|outcome| outcome.loans.len())
                        .sum();
                    if loans.len().saturating_add(count) > 200_000 {
                        complete = false;
                        break;
                    }
                    let ids = outcomes.map(|outcome| {
                        outcome.as_ref().map_or_else(Vec::new, |outcome| {
                            outcome
                                .loans
                                .iter()
                                .map(|loan| Self::push(loans, loan.mutable, block.span))
                                .collect()
                        })
                    });
                    sites.insert(target, ids);
                }
            }
            calls.push(sites);
        }
        (calls, complete)
    }
    fn iteration_sites(
        body: &Body,
        hir: &hir::Program,
        properties: &Properties,
        loans: &mut Vec<Loan>,
        complete: &mut bool,
    ) -> Vec<std::collections::BTreeMap<Vec<summary::Step>, LoanId>> {
        body.blocks
            .iter()
            .map(|block| {
                let mut sites = std::collections::BTreeMap::new();
                let Terminator::IteratorNext { iterator, .. } = &block.terminator else {
                    return sites;
                };
                let inner = match hir.types.get(body.local(*iterator).ty) {
                    Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => *inner,
                    _ => return sites,
                };
                let mut pending = vec![(inner, Vec::new())];
                while let Some((ty, path)) = pending.pop() {
                    if path.len() > 64 || sites.len() >= ORIGIN_LIMIT || loans.len() >= 200_000 {
                        *complete = false;
                        break;
                    }
                    if !properties.get(ty).references {
                        continue;
                    }
                    if let Ty::Reference { mutable, .. } = hir.types.get(ty) {
                        if *mutable {
                            sites.insert(path, Self::push(loans, true, block.span));
                        }
                    } else if let Some(children) = summary::children(ty, hir, properties) {
                        for (suffix, ty) in children {
                            let mut path = path.clone();
                            path.extend(suffix);
                            pending.push((ty, path));
                        }
                    }
                }
                sites
            })
            .collect()
    }
    fn push(loans: &mut Vec<Loan>, mutable: bool, span: Span) -> LoanId {
        let id = LoanId(loans.len() as u32);
        loans.push(Loan { mutable, span });
        id
    }
}

struct Context<'a> {
    body: &'a Body,
    hir: &'a hir::Program,
    properties: &'a Properties,
    summaries: &'a summary::Summaries,
    sites: Sites,
    loans: &'a [Loan],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Point {
    block: BlockId,
    statement: Option<u32>,
    span: Span,
}
impl Point {
    fn entry(body: &Body) -> Self {
        Self {
            block: body.entry,
            statement: None,
            span: body.block(body.entry).span,
        }
    }
    fn statement(block: BlockId, index: usize, statement: &Statement) -> Self {
        Self {
            block,
            statement: Some(index as u32),
            span: statement.span,
        }
    }
}

trait Reporter {
    fn finding(&mut self, point: Point, kind: FindingKind, loan: Option<LoanId>);
    fn gap(&mut self, point: Point, kind: GapKind);
    fn assumption(&mut self, _: crate::external::AssumptionId) {}
    fn access(&mut self, _: summary::Access) {}
    fn exit(&mut self, _: ExitKind, _: &Context<'_>, _: &flow::State) {}
}
struct Silent;
impl Reporter for Silent {
    fn finding(&mut self, _: Point, _: FindingKind, _: Option<LoanId>) {}
    fn gap(&mut self, _: Point, _: GapKind) {}
}
#[derive(Default)]
struct Recorder {
    findings: Vec<Finding>,
    gaps: Vec<Gap>,
    assumptions: BTreeSet<crate::external::AssumptionId>,
    seen_findings: HashSet<(Point, FindingKind, Option<LoanId>)>,
    seen_gaps: HashSet<(Span, GapKind)>,
}
impl Reporter for Recorder {
    fn assumption(&mut self, assumption: crate::external::AssumptionId) {
        self.assumptions.insert(assumption);
    }
    fn finding(&mut self, point: Point, kind: FindingKind, loan: Option<LoanId>) {
        if self.seen_findings.insert((point, kind, loan)) {
            self.findings.push(Finding {
                kind,
                span: point.span,
                block: point.block,
                statement: point.statement,
                loan,
            });
        }
    }
    fn gap(&mut self, point: Point, kind: GapKind) {
        if self.seen_gaps.insert((point.span, kind)) {
            self.gaps.push(Gap {
                kind,
                span: point.span,
            });
        }
    }
}

fn solve(context: &Context<'_>, liveness: &live::Liveness) -> Option<Vec<Option<flow::State>>> {
    let body = context.body;
    let width = body
        .locals
        .len()
        .checked_mul(2)?
        .checked_add(context.loans.len())?;
    if width.checked_mul(body.blocks.len())? > STATE_LIMIT {
        return None;
    }
    let mut inputs = vec![None; body.blocks.len()];
    inputs[body.entry.0 as usize] = Some(flow::State::initial(context));
    let mut queue = VecDeque::from([body.entry]);
    let mut queued = vec![false; body.blocks.len()];
    queued[body.entry.0 as usize] = true;
    let mut budget = WORK_LIMIT;
    while let Some(block) = queue.pop_front() {
        queued[block.0 as usize] = false;
        budget = budget.checked_sub(width + body.block(block).statements.len() + 1)?;
        let input = inputs[block.0 as usize].as_ref()?;
        let edges = transfer(context, liveness, block, input.clone(), &mut Silent);
        for (target, state) in edges {
            budget = budget.checked_sub(state.weight())?;
            if !state.bounded() {
                return None;
            }
            if merge_input(&mut inputs[target.0 as usize], state) && !queued[target.0 as usize] {
                queued[target.0 as usize] = true;
                queue.push_back(target);
            }
        }
    }
    Some(inputs)
}

fn merge_input(input: &mut Option<flow::State>, state: flow::State) -> bool {
    match input {
        Some(previous) => previous.merge(state),
        None => {
            *input = Some(state);
            true
        }
    }
}

fn replay(
    context: &Context<'_>,
    liveness: &live::Liveness,
    inputs: &[Option<flow::State>],
    recorder: &mut impl Reporter,
) {
    for (index, input) in inputs.iter().enumerate() {
        if let Some(input) = input {
            transfer(
                context,
                liveness,
                BlockId(index as u32),
                input.clone(),
                recorder,
            );
        }
    }
}

fn transfer<R: Reporter>(
    context: &Context<'_>,
    liveness: &live::Liveness,
    id: BlockId,
    mut state: flow::State,
    reporter: &mut R,
) -> Vec<(BlockId, flow::State)> {
    let block = context.body.block(id);
    for (index, statement) in block.statements.iter().enumerate() {
        let point = Point::statement(id, index, statement);
        let mut evaluator = flow::Evaluator::new(
            context,
            reporter,
            point,
            &liveness.before[id.0 as usize][index],
            &state,
        );
        evaluator.statement(&statement.kind, &mut state);
    }
    let point = Point {
        block: id,
        statement: None,
        span: block.span,
    };
    let mut evaluator = flow::Evaluator::new(
        context,
        reporter,
        point,
        liveness.before[id.0 as usize]
            .last()
            .expect("terminator liveness"),
        &state,
    );
    evaluator.terminator(&block.terminator, state)
}
