use super::*;
use crate::{
    diagnostic::Diagnostic,
    local::properties::Properties,
    mir::{
        self,
        borrow::summary::{self, Frame, FunctionSummary, Origin, Outcome, Step, Value},
        effects::Boundedness,
    },
};

pub(crate) fn analyze(
    mir: &mir::Program,
    hir: &mut hir::Program,
    borrows: &mir::borrow::Report,
    effects: &mir::effects::Report,
) -> Report {
    let properties = Properties::compute(hir);
    let mut report = Report::default();
    validate_union_storage(mir, hir, &properties, &mut report);
    for (&definition, contract) in &hir.modular.functions {
        let Some(actual) = effects.get(definition) else {
            continue;
        };
        let frame = Frame::declaration(definition, hir, &properties);
        let summary = borrows
            .summaries
            .iter()
            .find(|s| s.definition == definition);
        let effect_failure = !actual.effects.is_subset(&contract.upper)
            || contract.bounded && actual.bounded != Boundedness::Established
            || !actual.unknown.is_empty() && contract.upper != mir::effects::all_effects();
        if effect_failure {
            reject(
                &mut report,
                contract,
                "implementation exceeds its declared effect or termination bound",
            );
        }
        if let Some(summary) = summary {
            validate_memory(summary, contract, &frame, &mut report);
        }
        if contract.no_callback && may_callback(definition, mir, hir, &mut BTreeSet::new()) {
            reject(
                &mut report,
                contract,
                "implementation may invoke a callback or an unbounded opaque call",
            );
        }
        if contract.no_retain
            && summary.is_none_or(|s| !s.complete || s.accesses.iter().any(|a| a.write))
        {
            reject(
                &mut report,
                contract,
                "no_retain requires established absence of outward stores",
            );
        }
    }
    report
}

fn validate_union_storage(
    mir: &mir::Program,
    hir: &hir::Program,
    properties: &Properties,
    report: &mut Report,
) {
    let mut seen = BTreeSet::new();
    for local in mir.functions.iter().flat_map(|f| &f.locals) {
        if !properties.union(local.ty) || !seen.insert(local.ty.0) {
            continue;
        }
        if properties.get(local.ty).may_drop
            || properties.get(local.ty).references
            || !properties.get(local.ty).copy
        {
            report.diagnostics.push(Diagnostic::error("E-UNION-FIELD",
                "union storage requires Copy fields without embedded references; use raw pointers and explicit initialization contracts for opaque storage", local.span));
        }
    }
    let _ = hir;
}

fn reject(report: &mut Report, contract: &Contract, message: &str) {
    report
        .diagnostics
        .push(Diagnostic::error("E-EFFECT-REFINE", message, contract.span));
}

fn validate_memory(
    actual: &FunctionSummary,
    contract: &Contract,
    frame: &Frame,
    report: &mut Report,
) {
    if contract.reads.is_none()
        && contract.writes.is_none()
        && contract.returns.is_none()
        && contract.normal.is_empty()
        && contract.panic.is_empty()
        && contract.cancel.is_empty()
    {
        return;
    }
    if !actual.complete || actual.limited || !frame.complete {
        reject(report, contract, "memory refinement coverage is incomplete");
        return;
    }
    for access in &actual.accesses {
        let paths = if access.write {
            &contract.writes
        } else {
            &contract.reads
        };
        if paths.as_ref().is_some_and(|paths| {
            !paths
                .iter()
                .filter_map(|p| summary::footprint(p, frame))
                .any(|allowed| covers(&allowed, &access.target))
        }) {
            reject(
                report,
                contract,
                "implementation accesses memory outside its declared frame",
            );
        }
    }
    for (outcome, stores) in [
        (&actual.normal, &contract.normal),
        (&actual.panic, &contract.panic),
        (&actual.cancel, &contract.cancel),
    ] {
        if let Some(outcome) = outcome {
            validate_outcome(outcome, stores, contract, frame, report);
        }
    }
    if let (Some(paths), Some(outcome)) = (&contract.returns, &actual.normal)
        && !value_refines(&outcome.returned, paths, outcome, frame)
    {
        reject(
            report,
            contract,
            "returned origins exceed the declared returns relation",
        );
    }
}

fn covers(allowed: &summary::Footprint, actual: &summary::Footprint) -> bool {
    allowed.input == actual.input && actual.path.starts_with(&allowed.path)
}

fn validate_outcome(
    outcome: &Outcome,
    stores: &[crate::external::ReferenceStore],
    contract: &Contract,
    frame: &Frame,
    report: &mut Report,
) {
    for promise in stores {
        let target = summary::footprint(&promise.target, frame);
        let established = target
            .as_ref()
            .and_then(|target| outcome.writes.iter().find(|w| &w.target == target));
        if established.is_none_or(|write| {
            promise.definite && !write.definite
                || !value_refines(&write.value, &promise.sources, outcome, frame)
        }) {
            reject(
                report,
                contract,
                "an exit does not establish its declared entry-relative post-state store",
            );
        }
    }
    for write in &outcome.writes {
        if contract.writes.as_ref().is_some_and(|paths| {
            !paths
                .iter()
                .filter_map(|p| summary::footprint(p, frame))
                .any(|allowed| covers(&allowed, &write.target))
        }) {
            reject(
                report,
                contract,
                "an exit writes outside the declared memory frame",
            );
        }
    }
}

fn value_refines(value: &Value, allowed: &[String], outcome: &Outcome, frame: &Frame) -> bool {
    if value.unknown {
        return false;
    }
    let mut sources = BTreeSet::new();
    for origin in value.fields.values().flatten() {
        if !origin_sources(*origin, outcome, frame, &mut sources, &mut BTreeSet::new()) {
            return false;
        }
    }
    for origin in value.parameters.values().flatten() {
        sources.insert(format_path(origin.parameter, &origin.path));
    }
    sources.iter().all(|source| {
        allowed.iter().any(|allowed| {
            source == allowed
                || source
                    .strip_prefix(allowed)
                    .is_some_and(|rest| rest.starts_with('.'))
        })
    })
}

fn origin_sources(
    origin: Origin,
    outcome: &Outcome,
    frame: &Frame,
    output: &mut BTreeSet<String>,
    seen: &mut BTreeSet<u32>,
) -> bool {
    match origin {
        Origin::Static => {
            output.insert("static".into());
        }
        Origin::Input(input) => {
            let Some(input) = frame.inputs.get(input as usize) else {
                return false;
            };
            output.insert(format_path(input.parameter, &input.path));
        }
        Origin::Fresh(id) => {
            if !seen.insert(id) {
                return false;
            }
            let Some(loan) = outcome.loans.get(id as usize) else {
                return false;
            };
            if loan.unknown || loan.parents.is_empty() {
                return false;
            }
            for parent in &loan.parents {
                if !origin_sources(*parent, outcome, frame, output, seen) {
                    return false;
                }
            }
            seen.remove(&id);
        }
    }
    true
}

fn format_path(parameter: u32, path: &[Step]) -> String {
    let mut value = parameter.to_string();
    for step in path {
        value.push('.');
        value.push_str(&match step {
            Step::Deref => "*".into(),
            Step::Element => "[]".into(),
            Step::Field(field) => field.to_string(),
            Step::Variant(id) => format!("variant{}", id.0),
        });
    }
    value
}

fn may_callback(
    definition: hir::DefId,
    mir: &mir::Program,
    hir: &hir::Program,
    seen: &mut BTreeSet<hir::DefId>,
) -> bool {
    if !seen.insert(definition) {
        return false;
    }
    if seen.len() > 4096 {
        return true;
    }
    let Some(body) = mir
        .functions
        .iter()
        .find(|body| body.definition == definition)
    else {
        return true;
    };
    body.blocks.iter().any(|block| match &block.terminator {
        mir::Terminator::Call {
            callee: mir::Operand::Function { definition, .. },
            ..
        } => {
            !hir.contracts.intrinsics.contains_key(definition)
                && !hir
                    .modular
                    .functions
                    .get(definition)
                    .is_some_and(|c| c.no_callback)
                && may_callback(*definition, mir, hir, seen)
        }
        mir::Terminator::Call { .. }
        | mir::Terminator::DynCall { .. }
        | mir::Terminator::Spawn { .. } => true,
        _ => false,
    })
}
