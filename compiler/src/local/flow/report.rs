//! Reporting receives immutable facts, never mutable analysis state. The three
//! sinks cannot change transfer decisions or move a state update behind a mode
//! check. Diagnostic strings and evidence arenas exist only in `Diagnostics`.
use super::*;

// One borrow origin and up to four representative uses of expired storage.
const MAX_LIFETIME_LABELS: usize = 5;

pub(super) enum AvailabilityFailure {
    Moved(MoveCertainty),
    Uninitialized,
    StorageEnded,
}

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
        owner: hir::LocalId,
    },
    StorageEnd {
        span: Span,
        loan: EventId,
        end: EventId,
        owner: hir::LocalId,
    },
    Availability {
        span: Span,
        binding: Option<Span>,
        failure: AvailabilityFailure,
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
                ..
            } => {
                let diagnostic = Diagnostic::error(
                    "E-BORROW-RETURN",
                    "cannot return a reference to local storage",
                    span,
                );
                diagnostic
                    .primary_label("this reference would outlive its local owner")
                    .label(storage, "local storage is declared here")
                    .label(borrow, "reference borrows this storage")
                    .help("return an owned value or a reference tied to an input")
            }
            Self::StorageEnd { span, loan, .. } => {
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
                failure,
                causes,
            } => availability(span, binding, failure, causes, graph),
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

fn ended_storage(span: Span, causes: &Causes, graph: &Graph) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(
        "E-BORROW-LIFETIME",
        "cannot access storage after its lifetime has ended",
        span,
    )
    .primary_label("this reference refers to storage that is no longer alive");
    for &cause in causes {
        let event = graph.event(cause);
        if event.kind == super::super::EventKind::StorageEnd {
            diagnostic = diagnostic.label(event.span, "storage lifetime ends here");
        }
    }
    diagnostic
        .help("keep the owner alive as long as the reference, or shorten the reference's scope")
}

fn availability(
    span: Span,
    binding: Option<Span>,
    failure: AvailabilityFailure,
    causes: &Causes,
    graph: &Graph,
) -> Diagnostic {
    let mut diagnostic = match failure {
        AvailabilityFailure::StorageEnded => return ended_storage(span, causes, graph),
        AvailabilityFailure::Moved(certainty) => certainty.diagnostic(span),
        AvailabilityFailure::Uninitialized => Diagnostic::error(
            "E-INIT-READ",
            "binding is not initialized on every path",
            span,
        )
        .primary_label("used here before it is definitely initialized")
        .help("initialize this binding on every path before using it"),
    };
    if let Some(binding) = binding {
        diagnostic = diagnostic.label(binding, "binding declared here");
    }
    for &cause in causes {
        if graph.event(cause).kind == super::super::EventKind::Move {
            diagnostic = diagnostic.label(graph.event(cause).span, "ownership moved here");
        }
    }
    diagnostic
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
    diagnostics: Vec<Diagnostic>,
    pub reborrows: Vec<Reborrow>,
    storage_ends: HashMap<EventId, usize>,
    lifetime_owners: HashMap<usize, hir::LocalId>,
    returned_owners: HashSet<hir::LocalId>,
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
            storage_ends: HashMap::new(),
            lifetime_owners: HashMap::new(),
            returned_owners: HashSet::new(),
        }
    }

    pub fn take_diagnostics(&mut self) -> impl Iterator<Item = Diagnostic> + '_ {
        // A return error already explains why this owner's storage cannot end.
        // Defer coalescing until replay finishes: cleanup order and reborrows
        // can produce different loan events for the same storage owner.
        std::mem::take(&mut self.diagnostics)
            .into_iter()
            .enumerate()
            .filter_map(|(index, diagnostic)| {
                let duplicate = self
                    .lifetime_owners
                    .get(&index)
                    .is_some_and(|owner| self.returned_owners.contains(owner));
                (!duplicate).then_some(diagnostic)
            })
    }

    fn lifetime_cascade(&mut self, problem: &Problem<'_>) -> bool {
        let Problem::Availability {
            span,
            failure: AvailabilityFailure::StorageEnded,
            causes,
            ..
        } = problem
        else {
            return false;
        };
        for &cause in *causes {
            if let Some(&index) = self.storage_ends.get(&cause) {
                let diagnostic = &mut self.diagnostics[index];
                // Several locals can end at the same closing brace. Merge by
                // their event identity, and bound repeated use-site annotations.
                if diagnostic.labels.len() < MAX_LIFETIME_LABELS
                    && !diagnostic.labels.iter().any(|label| label.span == *span)
                {
                    diagnostic.labels.push(crate::diagnostic::Label {
                        span: *span,
                        message: "reference used after this storage ends".into(),
                    });
                }
                return true;
            }
        }
        false
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
        // Coalesce only a matching ended-storage cause. The failed finding and
        // evidence remain recorded, and unrelated initialization errors survive.
        if self.lifetime_cascade(&problem) {
            return;
        }
        let ended = match &problem {
            Problem::StorageEnd { end, owner, .. } => Some((*end, *owner)),
            _ => None,
        };
        let returned = match &problem {
            Problem::LocalReturn { owner, .. } => Some(*owner),
            _ => None,
        };
        let index = self.diagnostics.len();
        report(&mut self.diagnostics, problem.diagnostic(self.graph));
        if self.diagnostics.len() == index {
            return;
        }
        if let Some((end, owner)) = ended {
            self.storage_ends.insert(end, index);
            self.lifetime_owners.insert(index, owner);
        }
        if let Some(owner) = returned {
            self.returned_owners.insert(owner);
        }
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
