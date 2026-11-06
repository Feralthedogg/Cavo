//! Source-connected, bounded local-state analysis. This is not full memory-safety
//! verification and does not authorize LLVM alias or lifetime assumptions.

pub mod cfg;
mod flow;
mod memory;
mod nll;
mod place;
pub(crate) mod properties;
mod regions;

use crate::external::{AssumptionId, Bindings, Summaries, SummaryReport, SummaryStatus};
use crate::{diagnostic::Diagnostic, hir, source::Span};
pub use memory::{MemoryLoan, MemoryOrigin, MemoryPlace, MemorySummary, MemoryValue, MemoryWrite};
pub use nll::NllReport;
pub use place::{FieldProjection, Place, PlaceId};
pub use regions::{RegionContract, RegionInput, RegionStep, RegionTerm};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EventId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EvidenceId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub block: cfg::BlockId,
    pub operation: u32,
    pub evaluation: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Rejected,
    Undetermined,
}

#[derive(Debug)]
pub struct Report {
    pub verdict: Verdict,
    pub functions: Vec<FunctionReport>,
    pub not_analyzed: Vec<&'static str>,
    pub regions: Vec<RegionContract>,
    pub summaries: Vec<SummaryReport>,
}

#[derive(Debug)]
pub struct FunctionReport {
    pub definition: hir::DefId,
    pub cfg: cfg::Graph,
    pub places: Vec<Place>,
    pub nll: Option<NllReport>,
    pub evidence: Vec<Evidence>,
    pub findings: Vec<Finding>,
    pub local_complete: bool,
    pub reborrows: Vec<Reborrow>,
    pub assumptions: Vec<AssumptionId>,
    pub memory: Option<MemorySummary>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LoanId {
    Input(PlaceId),
    Borrow(EventId),
    Call {
        event: EventId,
        target: hir::DefId,
        index: u32,
    },
}

#[derive(Debug)]
pub struct Reborrow {
    pub point: Point,
    pub event: EventId,
    pub parents: Vec<LoanId>,
    pub loan: LoanId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventKind {
    Parameter,
    Declare,
    Initialize,
    Move,
    Read,
    BorrowShared,
    BorrowExclusive,
    StorageEnd,
    Call,
}

#[derive(Clone, Debug)]
pub struct Event {
    pub kind: EventKind,
    pub span: Span,
    pub local: Option<hir::LocalId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Predicate {
    Available(PlaceId),
    NoLoanConflict(PlaceId),
    StorageMayEnd(hir::LocalId),
    ReturnDoesNotBorrowLocalStorage,
    ExplicitMove,
    MovePreservesDrop,
    SupportedLocalSemantics,
    ReferenceAllowsWrite,
    ReturnRegion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Assessment {
    Established,
    Assumed,
    NotEstablished,
    NotAnalyzed,
}

#[derive(Debug)]
pub enum Evidence {
    Event(EventId),
    LocalCheck {
        point: Point,
        predicate: Predicate,
        assessment: Assessment,
        inputs: Vec<EvidenceId>,
        assumptions: Vec<AssumptionId>,
    },
}

#[derive(Debug)]
pub struct Finding {
    pub point: Point,
    pub span: Span,
    pub predicate: Predicate,
    pub assessment: Assessment,
    pub evidence: EvidenceId,
    pub assumptions: Vec<AssumptionId>,
}

impl Report {
    /// Structural arena validation, not recertification after a HIR transform.
    pub fn validate(&self, program: &hir::Program) -> Result<(), hir::InvariantError> {
        let fail = |message: &str| hir::InvariantError(message.to_owned());
        if self.not_analyzed.is_empty() {
            return Err(fail(
                "local analysis must retain incomplete full-safety coverage",
            ));
        }
        let mut seen = std::collections::HashSet::new();
        let valid_support = |ids: &[AssumptionId]| {
            ids.len() <= 128
                && ids.windows(2).all(|p| p[0] < p[1])
                && ids.iter().all(|id| {
                    self.summaries
                        .get(id.0 as usize)
                        .is_some_and(|s| s.assumption == *id && s.status == SummaryStatus::Assumed)
                })
        };
        for (index, summary) in self.summaries.iter().enumerate() {
            if summary.assumption.0 as usize != index
                || summary.function.0 as usize >= program.definitions.len()
            {
                return Err(fail("invalid summary identity"));
            }
        }
        let functions: std::collections::HashMap<_, _> = program
            .functions
            .iter()
            .map(|function| (function.definition, function))
            .collect();
        let mut region_definitions = std::collections::HashSet::new();
        let all_local_complete = self.functions.iter().all(|f| f.local_complete);
        for contract in &self.regions {
            let definition = program
                .definitions
                .get(contract.definition.0 as usize)
                .ok_or_else(|| fail("invalid region contract definition"))?;
            if definition.ty.0 as usize >= program.types.values().len() {
                return Err(fail("region contract has an invalid signature type"));
            }
            let crate::types::Ty::Function { parameters, result } =
                program.types.get(definition.ty)
            else {
                return Err(fail("region contract does not name a function"));
            };
            if !region_definitions.insert(contract.definition)
                || !valid_support(&contract.assumptions)
                || contract.inputs.len() > 128
                || contract.inputs.iter().any(|input| {
                    input.parameter as usize >= parameters.len()
                        || input.fields.len() > 128
                        || input.path.len() > 128
                        || !input
                            .path
                            .iter()
                            .filter_map(|step| {
                                if let RegionStep::Field(index) = step {
                                    Some(*index)
                                } else {
                                    None
                                }
                            })
                            .eq(input.fields.iter().copied())
                        || input
                            .pointee
                            .is_some_and(|id| id.0 as usize >= program.types.values().len())
                })
                || contract.inputs.iter().enumerate().any(|(index, input)| {
                    input.term
                        != match input.region {
                            Some(crate::types::Region::Infer(_)) | None => {
                                RegionTerm::Anonymous(index as u32)
                            }
                            Some(region) => RegionTerm::Declared(region),
                        }
                })
                || contract.outlives.len() > 128
                || contract.outlives.iter().any(|(a, b)| {
                    !contract.inputs.iter().any(|i| i.term == *a)
                        || !contract.inputs.iter().any(|i| i.term == *b)
                })
                || contract
                    .return_inputs
                    .iter()
                    .any(|&input| input >= contract.inputs.len())
                || contract
                    .return_inputs
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                || contract.reference_result
                    != matches!(
                        program.types.get(*result),
                        crate::types::Ty::Reference { .. }
                    )
                || contract.has_body != functions.contains_key(&contract.definition)
                || contract.body_checked
                    && (!contract.has_body
                        || !contract.valid
                        || self.verdict == Verdict::Rejected
                        || !all_local_complete)
            {
                return Err(fail("invalid region contract metadata"));
            }
        }
        for report in &self.functions {
            if !valid_support(&report.assumptions) {
                return Err(fail("invalid function assumption support"));
            }
            if self.verdict != Verdict::Rejected && report.local_complete && report.memory.is_none()
            {
                return Err(fail(
                    "completed local analysis is missing its memory transformer",
                ));
            }
            if !region_definitions.contains(&report.definition) {
                return Err(fail("function analysis is missing a region contract"));
            }
            if !seen.insert(report.definition) {
                return Err(fail("duplicate function analysis"));
            }
            let function = functions
                .get(&report.definition)
                .ok_or_else(|| fail("analysis has an invalid function ID"))?;
            let graph = &report.cfg;
            graph.validate(function)?;
            place::Places::validate(&report.places, graph.slots)?;
            if let Some(nll) = &report.nll {
                nll.validate(graph, &report.places)?;
            } else if report.local_complete {
                return Err(fail("completed local analysis is missing NLL liveness"));
            }
            if graph.blocks.is_empty()
                || graph.slots < function.locals.len()
                || graph.expression_events.len() != function.expressions.len()
            {
                return Err(fail("invalid local CFG arena dimensions"));
            }
            for event in &graph.events {
                if event
                    .local
                    .is_some_and(|local| local.0 as usize >= graph.slots)
                {
                    return Err(fail("invalid local event owner"));
                }
            }
            if graph
                .expression_events
                .iter()
                .flatten()
                .any(|event| event.0 as usize >= graph.events.len())
            {
                return Err(fail("invalid expression event ID"));
            }
            let valid_point = |point: Point| {
                graph
                    .blocks
                    .get(point.block.0 as usize)
                    .is_some_and(|block| point.operation as usize <= block.operations.len())
            };
            let valid_predicate = |predicate| match predicate {
                Predicate::StorageMayEnd(local) => (local.0 as usize) < graph.slots,
                Predicate::Available(place) | Predicate::NoLoanConflict(place) => {
                    (place.0 as usize) < report.places.len()
                }
                _ => true,
            };
            let input_sources: std::collections::HashSet<_> =
                report.places.iter().filter_map(|p| p.input).collect();
            let valid_loan = |loan: LoanId| match loan {
                LoanId::Input(place) => input_sources.contains(&place),
                LoanId::Borrow(event) => graph.events.get(event.0 as usize).is_some_and(|e| {
                    matches!(e.kind, EventKind::BorrowShared | EventKind::BorrowExclusive)
                }),
                LoanId::Call {
                    event,
                    target,
                    index,
                } => {
                    index < 128
                        && graph
                            .events
                            .get(event.0 as usize)
                            .is_some_and(|e| e.kind == EventKind::Call)
                        && program
                            .definitions
                            .get(target.0 as usize)
                            .is_some_and(|d| d.kind == hir::DefinitionKind::Function)
                }
            };
            for reborrow in &report.reborrows {
                let event = match reborrow.loan {
                    LoanId::Borrow(event) | LoanId::Call { event, .. } => Some(event),
                    LoanId::Input(_) => None,
                };
                if !valid_point(reborrow.point)
                    || event != Some(reborrow.event)
                    || !valid_loan(reborrow.loan)
                    || reborrow.parents.len() > 128
                    || reborrow.parents.windows(2).any(|p| p[0] >= p[1])
                    || reborrow
                        .parents
                        .iter()
                        .any(|&parent| parent == reborrow.loan || !valid_loan(parent))
                {
                    return Err(fail("invalid reborrow lineage"));
                }
            }
            if let Some(memory) = &report.memory {
                let inputs = self
                    .regions
                    .iter()
                    .find(|c| c.definition == report.definition)
                    .map_or(0, |c| c.inputs.len());
                if !memory.valid(inputs, program.definitions.len()) {
                    return Err(fail("invalid memory summary"));
                }
            }
            for (index, evidence) in report.evidence.iter().enumerate() {
                match evidence {
                    Evidence::Event(event)
                        if event.0 as usize >= graph.events.len() || event.0 as usize != index =>
                    {
                        return Err(fail("invalid root event evidence"));
                    }
                    Evidence::LocalCheck {
                        point,
                        predicate,
                        inputs,
                        assumptions,
                        assessment,
                        ..
                    } if !valid_point(*point)
                        || !valid_predicate(*predicate)
                        || !valid_support(assumptions)
                        || *assumptions != report.assumptions
                        || (*assessment == Assessment::Assumed) == assumptions.is_empty()
                            && matches!(
                                assessment,
                                Assessment::Established | Assessment::Assumed
                            )
                        || inputs.iter().any(|input| input.0 as usize >= index) =>
                    {
                        return Err(fail("invalid local check evidence or cyclic input"));
                    }
                    _ => {}
                }
            }
            for finding in &report.findings {
                if !matches!(report.evidence.get(finding.evidence.0 as usize), Some(Evidence::LocalCheck { point, predicate, assessment, assumptions, .. }) if *point == finding.point && *predicate == finding.predicate && *assessment == finding.assessment && *assumptions == finding.assumptions)
                {
                    return Err(fail("finding does not match its local check evidence"));
                }
            }
        }
        Ok(())
    }
}

/// The returned report also records incomplete global coverage on successful
/// local checks. No `Satisfied`/full-safety token is manufactured here.
pub fn analyze(program: &mut hir::Program, diagnostics: &mut Vec<Diagnostic>) -> Report {
    if let Err(error) = program.validate() {
        if let Some(function) = program.functions.first() {
            crate::diagnostic::report(
                diagnostics,
                Diagnostic::error(
                    "E-LOCAL-INTERNAL",
                    format!("invalid HIR supplied to local analysis: {error}"),
                    function.body.span,
                ),
            );
        }
        return Report {
            verdict: Verdict::Rejected,
            functions: Vec::new(),
            not_analyzed: vec!["invalid typed HIR; local analysis was not run"],
            regions: Vec::new(),
            summaries: Vec::new(),
        };
    }
    analyze_validated(program, diagnostics)
}

pub(crate) fn analyze_validated(
    program: &mut hir::Program,
    diagnostics: &mut Vec<Diagnostic>,
) -> Report {
    analyze_with_summaries(
        program,
        diagnostics,
        Bindings {
            functions: (0..program.definitions.len()).map(|_| None).collect(),
            reports: Vec::new(),
        },
        &Summaries::default(),
    )
}

pub(crate) fn analyze_with_summaries(
    program: &mut hir::Program,
    diagnostics: &mut Vec<Diagnostic>,
    mut external: Bindings,
    summaries: &Summaries,
) -> Report {
    if crate::sema::requires_execution_mir(program) {
        if let Some(function) = program.functions.first() {
            crate::diagnostic::report(
                diagnostics,
                Diagnostic::error(
                    "E-FRONTEND-STAGE",
                    "structured ownership requires the execution MIR analysis pipeline",
                    function.body.span,
                ),
            );
        }
        return Report {
            verdict: Verdict::Rejected,
            functions: Vec::new(),
            regions: Vec::new(),
            summaries: external.reports,
            not_analyzed: vec![
                "structured execution expressions are not representable in the legacy local CFG",
            ],
        };
    }
    let mut report = Report {
        verdict: Verdict::Undetermined,
        functions: Vec::new(),
        regions: Vec::new(),
        summaries: Vec::new(),
        not_analyzed: vec![
            "opaque/recursive memory paths and callable parameters with unknown reference-write effects",
            "Drop/defer and complete cleanup semantics",
            "layout/ABI and general value validity",
            "heap allocation permissions and definite heap free",
            "retention/free/callback effects, generic and callback ABI summaries",
            "contract proofs and temporal guard plans",
            "task transfer/cancellation/I/O lifetime contracts",
            "scheduling classes and Send/Sync/TaskTransfer",
        ],
    };
    let properties = properties::Properties::compute(program);
    let mut bodies = vec![false; program.definitions.len()];
    for function in &program.functions {
        bodies[function.definition.0 as usize] = true;
    }
    let mut contracts = regions::contracts(program, &properties, &bodies, diagnostics);
    external.apply(&mut contracts, program, diagnostics, summaries);
    let Some(supports) = external.dependencies(program) else {
        if let Some(f) = program.functions.first() {
            crate::diagnostic::report(
                diagnostics,
                Diagnostic::error(
                    "E-SUMMARY-LIMIT",
                    "summary dependency closure exceeds its resource limit",
                    f.body.span,
                ),
            );
        }
        report.verdict = Verdict::Rejected;
        report
            .not_analyzed
            .push("external assumption closure exceeded its resource limit");
        report.regions = contracts.into_iter().flatten().collect();
        report.summaries = external.reports;
        return report;
    };
    for (index, contract) in contracts.iter_mut().enumerate() {
        if let Some(contract) = contract {
            contract.assumptions = supports[index].clone();
        }
    }
    let graphs: Vec<_> = program.functions.iter().map(cfg::Graph::lower).collect();
    let Some(inferred) = memory::infer(
        program,
        &properties,
        &contracts,
        &external,
        &graphs,
        diagnostics,
    ) else {
        report.verdict = Verdict::Rejected;
        report
            .not_analyzed
            .push("interprocedural memory inference exceeded its resource limit");
        report.regions = contracts.into_iter().flatten().collect();
        report.summaries = external.reports;
        return report;
    };
    for (function, graph) in program.functions.iter().zip(graphs) {
        match graph {
            Some(graph) => {
                let mut checked = flow::analyze(
                    function,
                    graph,
                    program,
                    &properties,
                    memory::Calls {
                        regions: &contracts,
                        external: &external,
                        memory: &inferred,
                    },
                    diagnostics,
                )
                .report;
                if let Some(summary) = &checked.memory
                    && !matches!(&inferred[function.definition.0 as usize],memory::Inferred::Ready(expected) if expected==summary)
                {
                    crate::diagnostic::report(
                        diagnostics,
                        Diagnostic::error(
                            "E-MEMORY-INTERNAL",
                            "memory summary changed after the inference fixed point",
                            function.body.span,
                        )
                        .note("no memory transformer was approved from this inconsistent analysis"),
                    );
                    checked.memory = None;
                    checked.local_complete = false;
                }
                report.functions.push(checked);
            }
            None => crate::diagnostic::report(
                diagnostics,
                Diagnostic::error(
                    "E-LOCAL-LIMIT",
                    "local analysis exceeds its CFG resource limit",
                    function.body.span,
                )
                .help("split this function into smaller functions"),
            ),
        }
    }
    for function in &mut report.functions {
        if diagnostics.is_empty()
            && let Some(failed) = function.findings.iter().find(|f| {
                matches!(
                    f.assessment,
                    Assessment::NotEstablished | Assessment::NotAnalyzed
                )
            })
        {
            crate::diagnostic::report(
                diagnostics,
                Diagnostic::error(
                    "E-LOCAL-INTERNAL",
                    "a failed local safety check has no source diagnostic",
                    failed.span,
                )
                .note("no checked-body result was approved"),
            );
            function.local_complete = false;
        }
        let support = &supports[function.definition.0 as usize];
        function.assumptions = support.clone();
        for evidence in &mut function.evidence {
            if let Evidence::LocalCheck {
                assessment,
                assumptions,
                ..
            } = evidence
            {
                *assumptions = support.clone();
                if *assessment == Assessment::Established && !support.is_empty() {
                    *assessment = Assessment::Assumed;
                }
            }
        }
        for finding in &mut function.findings {
            finding.assumptions = support.clone();
            if finding.assessment == Assessment::Established && !support.is_empty() {
                finding.assessment = Assessment::Assumed;
            }
        }
        if !support.is_empty() {
            let body = program
                .functions
                .iter()
                .find(|f| f.definition == function.definition)
                .unwrap()
                .body
                .span;
            for diagnostic in diagnostics.iter_mut().filter(|d| {
                d.primary.file == body.file
                    && d.primary.start >= body.start
                    && d.primary.end <= body.end
            }) {
                for id in support {
                    let summary = &external.reports[id.0 as usize];
                    diagnostic.notes.push(format!(
                        "this analysis depends on assumed external contract `{}` {} ({})",
                        summary.id, summary.version, summary.digest
                    ));
                }
            }
        }
    }
    if !diagnostics.is_empty() {
        report.verdict = Verdict::Rejected;
    }
    let complete = diagnostics.is_empty()
        && report.functions.len() == program.functions.len()
        && report.functions.iter().all(|f| f.local_complete);
    for contract in contracts.iter_mut().flatten() {
        contract.body_checked = complete && contract.has_body && contract.valid;
    }
    report.regions = contracts.into_iter().flatten().collect();
    report.summaries = external.reports;
    report
}
