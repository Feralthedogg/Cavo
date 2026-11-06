//! Reporting receives immutable facts, never mutable analysis state. The three
//! sinks cannot change transfer decisions or move a state update behind a mode
//! check. Diagnostic strings and evidence arenas exist only in `Diagnostics`.
use super::*;

pub(super) enum Problem<'a> {
    Signature(super::super::regions::SignatureProblem),
    Unsupported {
        feature: &'a str,
        span: Span,
    },
    CallableInvariant(Span),
    ReferenceInvariant(Span),
    Region {
        code: &'static str,
        span: Span,
    },
    InputStore(Span),
    RegionReturn {
        span: Span,
        signature: Span,
    },
    LocalReturn {
        span: Span,
        storage: Span,
        borrow: Span,
    },
    StorageEnd {
        span: Span,
        loan: EventId,
    },
    Availability {
        span: Span,
        binding: Option<Span>,
        flags: u8,
        causes: &'a Causes,
    },
    Conflict {
        span: Span,
        loan: EventId,
    },
    ExplicitMove(Span),
    DropPartialMove(Span),
    SharedWrite(Span),
    Untrusted {
        span: Span,
        summary: &'a crate::external::SummaryReport,
    },
}
impl Problem<'_> {
    fn diagnostic(self, graph: &Graph) -> Diagnostic {
        match self {
            Self::DropPartialMove(span) => Diagnostic::error(
                "E-MOVE-DROP",
                "cannot partially move a value with a user destructor",
                span,
            ),
            Self::Signature(problem) => problem.diagnostic(),
            Self::Unsupported { feature, span } => {
                let message = format!("{feature} is not implemented in this local-state stage");
                Diagnostic::error("E-FRONTEND-STAGE", message, span).note(concat!(
                    "no complete ownership, region, or memory-safety result ",
                    "is being approved"
                ))
            }
            Self::CallableInvariant(span) => {
                let message = concat!(
                    "mutable callable storage would change ",
                    "its invocation lifetime contract"
                );
                Diagnostic::error("E-REGION-INVARIANT", message, span).note(concat!(
                    "a universally callable function cannot be replaced ",
                    "through a monomorphic mutable view"
                ))
            }
            Self::ReferenceInvariant(span) => {
                let diagnostic = Diagnostic::error(
                    "E-REGION-INVARIANT",
                    "mutable reference would change a contained lifetime",
                    span,
                );
                diagnostic.note("the pointee type of a mutable reference is invariant")
            }
            Self::Region { code, span } => {
                let message = "cannot establish the lifetime required by this reference type";
                let diagnostic = Diagnostic::error(code, message, span);
                diagnostic
                    .primary_label(concat!(
                        "the reference's actual origin does not ",
                        "outlive the declared region"
                    ))
                    .help(concat!(
                        "use a reference tied to the required input lifetime, ",
                        "or shorten the declared lifetime"
                    ))
            }
            Self::InputStore(span) => {
                let message = concat!(
                    "stored reference does not outlive ",
                    "the input memory's declared region"
                );
                Diagnostic::error("E-REGION-STORE", message, span)
                    .primary_label("the replacement must preserve the caller's storage lifetime")
                    .help(concat!(
                        "tie the destination's stored reference and the replacement ",
                        "to an appropriate named lifetime"
                    ))
            }
            Self::RegionReturn { span, signature } => {
                let message = "returned reference does not satisfy the declared input lifetime";
                Diagnostic::error("E-REGION-RETURN", message, span)
                    .label(signature, "return region is declared by this signature")
                    .help(concat!(
                        "return a reference from an allowed input, ",
                        "or correct the lifetime declaration"
                    ))
            }
            Self::LocalReturn {
                span,
                storage,
                borrow,
            } => {
                let diagnostic = Diagnostic::error(
                    "E-BORROW-RETURN",
                    "cannot return a reference to local storage",
                    span,
                );
                diagnostic
                    .label(storage, "local storage is declared here")
                    .label(borrow, "reference borrows this storage")
                    .help("return an owned value or a reference tied to an input")
            }
            Self::StorageEnd { span, loan } => {
                let diagnostic = Diagnostic::error(
                    "E-BORROW-LIFETIME",
                    "borrowed local storage does not live long enough",
                    span,
                );
                diagnostic
                    .primary_label("this storage ends while a reference can still use it")
                    .label(graph.event(loan).span, "borrow created here")
                    .help(concat!(
                        "keep the owner alive as long as the reference, ",
                        "or shorten the reference's scope"
                    ))
            }
            Self::Availability {
                span,
                binding,
                flags,
                causes,
            } => {
                let moved = flags & MOVED != 0;
                let (code, message, label, help) = if moved {
                    (
                        "E-MOVE-USE",
                        "value may have been moved before this use",
                        "this place is not available on every incoming path",
                        "use the new owner, or reinitialize this binding before using it",
                    )
                } else {
                    (
                        "E-INIT-READ",
                        "binding is not initialized on every path",
                        "used here before it is definitely initialized",
                        "initialize this binding on every path before using it",
                    )
                };
                let mut diagnostic = Diagnostic::error(code, message, span).primary_label(label);
                if let Some(binding) = binding {
                    diagnostic = diagnostic.label(binding, "binding declared here");
                }
                for &cause in causes {
                    if graph.event(cause).kind == super::super::EventKind::Move {
                        diagnostic =
                            diagnostic.label(graph.event(cause).span, "ownership moved here");
                    }
                }
                diagnostic.help(help)
            }
            Self::Conflict { span, loan } => {
                let diagnostic = Diagnostic::error(
                    "E-BORROW-CONFLICT",
                    "this access conflicts with an active borrow",
                    span,
                );
                diagnostic
                    .primary_label("this place overlaps a borrow that is still active")
                    .label(graph.event(loan).span, "conflicting borrow starts here")
                    .note(concat!(
                        "a reference or temporary still requires this loan, ",
                        "including possible cleanup use"
                    ))
                    .help("finish using the reference before accessing this place again")
            }
            Self::ExplicitMove(span) => {
                let diagnostic = Diagnostic::error(
                    "E-MOVE-EXPLICIT",
                    "this value requires an explicit move",
                    span,
                );
                diagnostic
                    .primary_label("Copy is not established for this use")
                    .help("use `move` to transfer the value, or borrow it instead")
            }
            Self::SharedWrite(span) => Diagnostic::error(
                "E-BORROW-SHARED",
                "cannot write through a shared reference",
                span,
            ),
            Self::Untrusted { span, summary } => {
                let message = "this call requires an explicitly trusted external contract";
                Diagnostic::error("E-SUMMARY-UNTRUSTED", message, span)
                    .label(summary.source, "summary was loaded without granting trust")
                    .note(format!("document identity: {}", summary.digest))
                    .help(concat!(
                        "review the exact document, then pin its identity ",
                        "with --trust-summary"
                    ))
            }
        }
    }
}

pub(super) struct Check<'a> {
    pub point: Point,
    pub span: Span,
    pub predicate: Predicate,
    pub assessment: Assessment,
    pub causes: &'a Causes,
}
pub(super) trait Reporter {
    fn check(&mut self, check: Check<'_>, problem: Option<Problem<'_>>);
    fn problem(&mut self, problem: Problem<'_>);
    fn reborrow(&mut self, point: Point, loan: LoanId, event: EventId, parents: &[LoanId]);
    fn dependency(&mut self, definition: hir::DefId);
}
pub(super) struct Discard;
impl Reporter for Discard {
    fn check(&mut self, _: Check<'_>, _: Option<Problem<'_>>) {}
    fn problem(&mut self, _: Problem<'_>) {}
    fn reborrow(&mut self, _: Point, _: LoanId, _: EventId, _: &[LoanId]) {}
    fn dependency(&mut self, _: hir::DefId) {}
}

#[derive(Default)]
pub(super) struct Summary {
    pub failed: bool,
    pub unsupported: bool,
    pub dependencies: BTreeSet<hir::DefId>,
}
impl Reporter for Summary {
    fn check(&mut self, check: Check<'_>, _: Option<Problem<'_>>) {
        self.failed |= matches!(
            check.assessment,
            Assessment::NotEstablished | Assessment::NotAnalyzed
        );
        self.unsupported |= check.assessment == Assessment::NotAnalyzed;
    }
    fn problem(&mut self, _: Problem<'_>) {
        self.failed = true;
    }
    fn reborrow(&mut self, _: Point, _: LoanId, _: EventId, _: &[LoanId]) {}
    fn dependency(&mut self, definition: hir::DefId) {
        self.dependencies.insert(definition);
    }
}

pub(super) struct Diagnostics<'a> {
    pub status: Summary,
    pub graph: &'a Graph,
    pub evidence: Vec<Evidence>,
    pub findings: Vec<Finding>,
    pub diagnostics: Vec<Diagnostic>,
    pub reborrows: Vec<Reborrow>,
}
impl<'a> Diagnostics<'a> {
    pub fn new(graph: &'a Graph) -> Self {
        Self {
            status: Summary::default(),
            graph,
            evidence: (0..graph.events.len())
                .map(|i| Evidence::Event(EventId(i as u32)))
                .collect(),
            findings: Vec::new(),
            diagnostics: Vec::new(),
            reborrows: Vec::new(),
        }
    }
}
impl Reporter for Diagnostics<'_> {
    fn check(&mut self, check: Check<'_>, problem: Option<Problem<'_>>) {
        self.status.failed |= matches!(
            check.assessment,
            Assessment::NotEstablished | Assessment::NotAnalyzed
        );
        self.status.unsupported |= check.assessment == Assessment::NotAnalyzed;
        let evidence = EvidenceId(self.evidence.len() as u32);
        self.evidence.push(Evidence::LocalCheck {
            point: check.point,
            predicate: check.predicate,
            assessment: check.assessment,
            inputs: check.causes.iter().map(|e| EvidenceId(e.0)).collect(),
            assumptions: Vec::new(),
        });
        self.findings.push(Finding {
            point: check.point,
            span: check.span,
            predicate: check.predicate,
            assessment: check.assessment,
            evidence,
            assumptions: Vec::new(),
        });
        if let Some(problem) = problem {
            self.problem(problem);
        }
    }
    fn problem(&mut self, problem: Problem<'_>) {
        self.status.failed = true;
        report(&mut self.diagnostics, problem.diagnostic(self.graph));
    }
    fn reborrow(&mut self, point: Point, loan: LoanId, event: EventId, parents: &[LoanId]) {
        self.reborrows.push(Reborrow {
            point,
            loan,
            event,
            parents: parents.to_vec(),
        });
    }
    fn dependency(&mut self, definition: hir::DefId) {
        self.status.dependencies.insert(definition);
    }
}
