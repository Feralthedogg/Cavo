use super::*;
use crate::arena::Access as _;
use crate::{diagnostic::Diagnostic, external::digest::sha256};
use std::fmt::Write;

pub const REPORT_SCHEMA: u32 = 1;
pub const SEMANTICS: &str = "cavo.contracts.1";

#[derive(Debug, Default)]
pub struct Report {
    pub(crate) dependencies:
        std::collections::BTreeMap<hir::DefId, std::collections::BTreeSet<Trust>>,
    pub evidence: EvidenceGraph,
    pub obligations: Vec<Obligation>,
    pub guards: Vec<GuardPlan>,
    pub certificates: Vec<GuardUseCertificate>,
    pub(crate) artifact: Option<crate::external::Digest>,
}

impl Report {
    pub fn validate_for(
        &self,
        mir: &crate::mir::Program,
        hir: &hir::Program,
    ) -> Result<(), String> {
        self.validate()?;
        if self.artifact != Some(artifact_key(mir, hir)) {
            return Err(
                "contract certificates are stale for this MIR and declaration snapshot".into(),
            );
        }
        super::checks::verify(mir, &self.guards, &self.certificates)
    }
    pub fn validate(&self) -> Result<(), String> {
        self.evidence.validate()?;
        for obligation in &self.obligations {
            if obligation.components.is_empty() {
                return Err("a contract obligation has no analyzed components".into());
            }
            for component in &obligation.components {
                match component.assessment {
                    Assessment::Proven(id)
                    | Assessment::Assumed(id)
                    | Assessment::Violated(WitnessId(id)) => {
                        let evidence = self
                            .evidence
                            .nodes
                            .get(id.0 as usize)
                            .ok_or("a contract result references missing evidence")?;
                        match component.assessment {
                            Assessment::Proven(_) if !evidence.trust.is_empty() => {
                                return Err("assumed evidence was promoted to Proven".into());
                            }
                            Assessment::Assumed(_) if evidence.trust.is_empty() => {
                                return Err("Assumed result has no trust dependency".into());
                            }
                            Assessment::Violated(_) if evidence.kind != EvidenceKind::Violation => {
                                return Err("violation has no checked witness".into());
                            }
                            _ => {}
                        }
                    }
                    Assessment::Guarded(id) if id.0 as usize >= self.guards.len() => {
                        return Err("a contract result references a missing guard plan".into());
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    pub fn diagnostics(&self, output: &mut Vec<Diagnostic>) {
        for obligation in &self.obligations {
            let Some(code) = obligation.code() else {
                continue;
            };
            let violated = code == "E-CONTRACT-004";
            let message = if violated {
                "contract violation"
            } else {
                "cannot establish the required contract"
            };
            let mut diagnostic = Diagnostic::error(
                code,
                format!("{message} for `{}`", obligation.operation),
                obligation.span,
            );
            diagnostic.notes.push(format!(
                "analysis coverage: {}",
                coverage_text(obligation.coverage())
            ));
            for component in &obligation.components {
                diagnostic.notes.push(format!(
                    "{}: {}",
                    component.name,
                    assessment_text(&component.assessment)
                ));
                self.evidence_notes(&component.assessment, &mut diagnostic);
            }
            diagnostic.helps.push("derive the pointer from a valid reference or provide the external owner's contract and evidence".into());
            diagnostic
                .notes
                .push("a `contract` block alone does not establish these obligations".into());
            crate::diagnostic::report(output, diagnostic);
        }
    }

    fn evidence_notes(&self, assessment: &Assessment, diagnostic: &mut Diagnostic) {
        let id = match assessment {
            // Established components are already listed in notes. Their routine
            // origin is not a cause of this failure and should not mark parameters.
            Assessment::Assumed(id) => *id,
            Assessment::Violated(WitnessId(id)) => *id,
            _ => return,
        };
        let Some(evidence) = self.evidence.nodes.get_id(id) else {
            return;
        };
        diagnostic.labels.push(crate::diagnostic::Label {
            span: evidence.span,
            message: evidence.detail.clone(),
        });
        for trust in &evidence.trust {
            diagnostic
                .notes
                .push(format!("under declared assumptions: {trust:?}"));
        }
    }

    pub fn dump(&self) -> String {
        let mut output =
            format!("Contract analysis / schema={REPORT_SCHEMA}, semantics={SEMANTICS}\n");
        for obligation in &self.obligations {
            let _ = writeln!(
                output,
                "  {}: {:?}, coverage={:?}, key={}",
                obligation.operation,
                obligation.verdict(),
                obligation.coverage(),
                obligation.key
            );
            for component in &obligation.components {
                let _ = writeln!(
                    output,
                    "    {}: {}",
                    component.name,
                    assessment_text(&component.assessment)
                );
            }
        }
        output
    }
}

fn coverage_text(coverage: Coverage) -> &'static str {
    match coverage {
        Coverage::Complete => "complete",
        Coverage::Partial => "partial",
        Coverage::Unavailable => "unavailable",
    }
}

fn assessment_text(assessment: &Assessment) -> String {
    match assessment {
        Assessment::Proven(_) => "established".into(),
        Assessment::Guarded(_) => "runtime checks retained".into(),
        Assessment::Assumed(_) => "assumed".into(),
        Assessment::Violated(_) => "violated".into(),
        Assessment::Unknown(reason) => format!("not established: {reason}"),
        Assessment::NotAnalyzed(reason) => format!("not analyzed: {reason}"),
    }
}

pub(crate) fn obligation_key(
    definition: &str,
    ordinal: usize,
    operation: &str,
) -> crate::external::Digest {
    sha256(format!("{SEMANTICS}\0{definition}\0{ordinal}\0{operation}").as_bytes())
}

pub(crate) fn artifact_key(
    mir: &crate::mir::Program,
    hir: &hir::Program,
) -> crate::external::Digest {
    sha256(format!("{SEMANTICS}\0{mir:?}\0{hir:?}").as_bytes())
}
