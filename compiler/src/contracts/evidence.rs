use crate::arena::Access as _;
use crate::{external::Digest, source::Span};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EvidenceId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EventId(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WitnessId(pub EvidenceId);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Trust {
    Module {
        digest: Digest,
        source: std::sync::Arc<str>,
        start: u32,
        reason: std::sync::Arc<str>,
    },
    Source {
        file: u32,
        start: u32,
        reason: std::sync::Arc<str>,
    },
    External(Digest),
    TrustedImpl {
        file: u32,
        start: u32,
        reason: std::sync::Arc<str>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceKind {
    ReferenceOrigin,
    Allocation,
    Initialization,
    Permission,
    Precondition,
    RuntimeGuard,
    Assumption,
    Invalidation,
    Derivation,
    Violation,
}

#[derive(Clone, Debug)]
pub struct Evidence {
    pub kind: EvidenceKind,
    pub span: Span,
    pub event: EventId,
    pub parents: Vec<EvidenceId>,
    pub trust: BTreeSet<Trust>,
    pub detail: String,
}

#[derive(Clone, Debug, Default)]
pub struct EvidenceGraph {
    pub nodes: Vec<Evidence>,
    origins: std::collections::BTreeMap<(EventId, u32, u32, BTreeSet<Trust>), EvidenceId>,
}

impl EvidenceGraph {
    pub(crate) fn origin(
        &mut self,
        event: EventId,
        span: Span,
        trust: BTreeSet<Trust>,
        detail: &str,
    ) -> Result<EvidenceId, String> {
        let key = (event, span.file.0, span.start, trust.clone());
        if let Some(&id) = self.origins.get(&key) {
            return Ok(id);
        }
        let id = self.insert(Evidence {
            kind: if trust.is_empty() {
                EvidenceKind::ReferenceOrigin
            } else {
                EvidenceKind::Assumption
            },
            span,
            event,
            parents: Vec::new(),
            trust,
            detail: detail.into(),
        })?;
        self.origins.insert(key, id);
        Ok(id)
    }
    pub fn insert(&mut self, mut node: Evidence) -> Result<EvidenceId, String> {
        if self.nodes.len() >= 200_000 || node.parents.len() > 128 {
            return Err("contract evidence budget exceeded".into());
        }
        for &parent in &node.parents {
            let evidence = self
                .nodes
                .get(parent.0 as usize)
                .ok_or("evidence parent is invalid or forward")?;
            node.trust.extend(evidence.trust.iter().cloned());
        }
        let id = EvidenceId(self.nodes.len() as u32);
        self.nodes.push(node);
        Ok(id)
    }

    pub fn validate(&self) -> Result<(), String> {
        for (index, node) in self.nodes.iter().enumerate() {
            for &parent in &node.parents {
                if parent.0 as usize >= index {
                    return Err("evidence graph is not a child-first DAG".into());
                }
                if !self.nodes[parent].trust.is_subset(&node.trust) {
                    return Err("derived evidence lost an assumption dependency".into());
                }
            }
        }
        Ok(())
    }

    pub fn trust(&self, evidence: EvidenceId) -> Option<&BTreeSet<Trust>> {
        self.nodes.get_id(evidence).map(|node| &node.trust)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Assessment {
    Proven(EvidenceId),
    Guarded(super::GuardPlanId),
    Assumed(EvidenceId),
    Unknown(String),
    Violated(WitnessId),
    NotAnalyzed(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coverage {
    Complete,
    Partial,
    Unavailable,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Satisfied,
    Rejected,
    Undetermined,
}

#[derive(Clone, Debug)]
pub struct Component {
    pub name: String,
    pub assessment: Assessment,
}

#[derive(Clone, Debug)]
pub struct Obligation {
    pub key: Digest,
    pub span: Span,
    pub operation: String,
    pub components: Vec<Component>,
}

impl Obligation {
    pub fn coverage(&self) -> Coverage {
        let missing = self
            .components
            .iter()
            .filter(|condition| matches!(condition.assessment, Assessment::NotAnalyzed(_)))
            .count();
        if missing == 0 {
            Coverage::Complete
        } else if missing == self.components.len() {
            Coverage::Unavailable
        } else {
            Coverage::Partial
        }
    }

    pub fn verdict(&self) -> Verdict {
        // A definite witness wins even when an unrelated pass is unavailable.
        if self
            .components
            .iter()
            .any(|c| matches!(c.assessment, Assessment::Violated(_)))
        {
            return Verdict::Rejected;
        }
        if self.coverage() != Coverage::Complete {
            return Verdict::Undetermined;
        }
        if self
            .components
            .iter()
            .any(|c| matches!(c.assessment, Assessment::Unknown(_)))
        {
            return Verdict::Rejected;
        }
        Verdict::Satisfied
    }

    pub fn code(&self) -> Option<&'static str> {
        if self
            .components
            .iter()
            .any(|c| matches!(c.assessment, Assessment::Violated(_)))
        {
            Some("E-CONTRACT-004")
        } else if self.coverage() != Coverage::Complete {
            Some("E-FRONTEND-STAGE")
        } else if self.verdict() == Verdict::Rejected {
            Some("E-CONTRACT-003")
        } else {
            None
        }
    }
}
