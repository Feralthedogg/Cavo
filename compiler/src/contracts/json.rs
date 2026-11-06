use super::source::{REPORT_SCHEMA, SEMANTICS};
use super::*;
use crate::{
    external::{digest::sha256, json::quote},
    source::SourceMap,
};
use std::fmt::Write;

impl Report {
    /// External keys are content identities; arena indices never cross this boundary.
    pub fn json(&self, sources: &SourceMap) -> String {
        let keys = evidence_keys(&self.evidence, sources);
        let guards = guard_keys(self);
        let mut output = format!(
            "{{\"schema\":{REPORT_SCHEMA},\"semantics\":{},\"obligations\":[",
            quote(SEMANTICS)
        );
        render_obligations(&mut output, &self.obligations, &keys, &guards, sources);
        output.push_str("],\"evidence\":[");
        for (index, evidence) in self.evidence.nodes.iter().enumerate() {
            if index > 0 {
                output.push(',');
            }
            render_evidence(&mut output, &keys[index], evidence, &keys, sources);
        }
        output.push_str("],\"guards\":[");
        for (index, guard) in self.guards.iter().enumerate() {
            if index > 0 {
                output.push(',');
            }
            let _ = write!(
                output,
                "{{\"key\":{},\"checks\":{},\"dependency_count\":{},\"pure\":{},\"nosuspend\":{},\"noalloc\":{}}}",
                quote(&guards[index]),
                guard.checks.len(),
                guard
                    .checks
                    .iter()
                    .map(|c| c.dependencies.len())
                    .sum::<usize>(),
                guard.pure,
                guard.nosuspend,
                guard.noalloc
            );
        }
        output.push_str("]}\n");
        output
    }
}

fn guard_keys(report: &Report) -> Vec<String> {
    (0..report.guards.len())
        .map(|index| {
            let obligation = report.obligations.iter().find(|o| {
                o.components.iter().any(
                    |c| matches!(c.assessment, Assessment::Guarded(id) if id.0 as usize == index),
                )
            });
            sha256(format!("{SEMANTICS}/guard/{:?}", obligation.map(|o| o.key)).as_bytes())
                .to_string()
        })
        .collect()
}

fn render_obligations(
    output: &mut String,
    obligations: &[Obligation],
    keys: &[String],
    guards: &[String],
    sources: &SourceMap,
) {
    for (index, obligation) in obligations.iter().enumerate() {
        if index > 0 {
            output.push(',');
        }
        let _ = write!(
            output,
            "{{\"key\":{},\"operation\":{},\"source\":{},\"verdict\":{},\"coverage\":{},\"components\":[",
            quote(&obligation.key.to_string()),
            quote(&obligation.operation),
            location(obligation.span, sources),
            quote(&format!("{:?}", obligation.verdict())),
            quote(&format!("{:?}", obligation.coverage()))
        );
        for (index, component) in obligation.components.iter().enumerate() {
            if index > 0 {
                output.push(',');
            }
            let _ = write!(
                output,
                "{{\"name\":{},\"assessment\":{}}}",
                quote(&component.name),
                assessment(&component.assessment, keys, guards)
            );
        }
        output.push_str("]}");
    }
}

fn evidence_keys(graph: &EvidenceGraph, sources: &SourceMap) -> Vec<String> {
    let mut keys = Vec::with_capacity(graph.nodes.len());
    for evidence in &graph.nodes {
        let parents: Vec<_> = evidence
            .parents
            .iter()
            .filter_map(|id| keys.get(id.0 as usize))
            .collect();
        let identity = format!(
            "{SEMANTICS}/{}/{:?}/{}/{:?}/{}",
            location(evidence.span, sources),
            evidence.kind,
            evidence.detail,
            parents,
            trust_list(&evidence.trust, sources),
        );
        keys.push(sha256(identity.as_bytes()).to_string());
    }
    keys
}

fn render_evidence(
    output: &mut String,
    key: &str,
    evidence: &Evidence,
    keys: &[String],
    sources: &SourceMap,
) {
    let parents = evidence
        .parents
        .iter()
        .map(|id| quote(&keys[id.0 as usize]))
        .collect::<Vec<_>>()
        .join(",");
    let trust = trust_list(&evidence.trust, sources);
    let _ = write!(
        output,
        "{{\"key\":{},\"kind\":{},\"source\":{},\"detail\":{},\"parents\":[{}],\"trust\":[{}]}}",
        quote(key),
        quote(&format!("{:?}", evidence.kind)),
        location(evidence.span, sources),
        quote(&evidence.detail),
        parents,
        trust
    );
}

fn trust_list(trust: &std::collections::BTreeSet<Trust>, sources: &SourceMap) -> String {
    // Canonical ordering uses source identities, never compilation-local FileIds.
    let mut values: Vec<_> = trust
        .iter()
        .map(|trust| trust_json(trust, sources))
        .collect();
    values.sort();
    values.join(",")
}

fn trust_json(trust: &Trust, sources: &SourceMap) -> String {
    match trust {
        Trust::Module {
            digest,
            source,
            start,
            reason,
        } => format!(
            "{{\"kind\":\"module_premise\",\"digest\":{},\"source\":{},\"start\":{},\"reason\":{}}}",
            quote(&digest.to_string()),
            quote(source),
            start,
            quote(reason)
        ),
        Trust::Source {
            file,
            start,
            reason,
        }
        | Trust::TrustedImpl {
            file,
            start,
            reason,
        } => {
            let kind = if matches!(trust, Trust::Source { .. }) {
                "source"
            } else {
                "trusted_impl"
            };
            format!(
                "{{\"kind\":{},\"source\":{},\"reason\":{}}}",
                quote(kind),
                location(
                    Span::new(crate::source::FileId(*file), *start, *start),
                    sources
                ),
                quote(reason)
            )
        }
        Trust::External(digest) => format!(
            "{{\"kind\":\"external\",\"digest\":{}}}",
            quote(&digest.to_string())
        ),
    }
}

fn assessment(value: &Assessment, evidence: &[String], guards: &[String]) -> String {
    let (status, key, detail) = match value {
        Assessment::Proven(id) => ("established", Some(&evidence[id.0 as usize]), None),
        Assessment::Assumed(id) => ("assumed", Some(&evidence[id.0 as usize]), None),
        Assessment::Violated(WitnessId(id)) => ("violated", Some(&evidence[id.0 as usize]), None),
        Assessment::Guarded(id) => (
            "runtime_checks_retained",
            Some(&guards[id.0 as usize]),
            None,
        ),
        Assessment::Unknown(detail) => ("not_established", None, Some(detail)),
        Assessment::NotAnalyzed(detail) => ("not_analyzed", None, Some(detail)),
    };
    format!(
        "{{\"status\":{},\"key\":{},\"detail\":{}}}",
        quote(status),
        key.map_or("null".into(), |key| quote(key)),
        detail.map_or("null".into(), |detail| quote(detail))
    )
}

fn location(span: Span, sources: &SourceMap) -> String {
    let Some(file) = sources.files().get(span.file.0 as usize) else {
        return "null".into();
    };
    format!(
        "{{\"file\":{},\"start\":{},\"end\":{}}}",
        quote(&file.path.to_string_lossy()),
        span.start,
        span.end
    )
}
