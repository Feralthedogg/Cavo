//! Conservative trust closure over declared calls and known function values.
//! Native summaries remain assumptions; checking a capsule does not erase the
//! explicit premises inside its implementation witness.
use super::*;
use crate::{
    external::{SummaryReport, SummaryStatus},
    mir,
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn collect(
    mir: &mir::Program,
    hir: &hir::Program,
    external: &[SummaryReport],
    properties: &crate::local::properties::Properties,
) -> Result<BTreeMap<hir::DefId, BTreeSet<Trust>>, String> {
    let mut trust = hir.modular.assumptions.clone();
    if hir
        .tasks
        .scopes
        .len()
        .saturating_mul(hir.tasks.trusted.len())
        > 200_000
    {
        return Err("contract trust seeds exceed their resource budget".into());
    }
    seed_source(hir, &mut trust);
    for summary in external
        .iter()
        .filter(|s| s.status == SummaryStatus::Assumed)
    {
        trust
            .entry(summary.function)
            .or_default()
            .insert(Trust::External(summary.digest));
    }
    let indices: BTreeMap<_, _> = mir
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.definition, i))
        .collect();
    let targets: Vec<_> = mir
        .functions
        .iter()
        .map(|body| body_dependencies(body, hir, properties))
        .collect();
    let edges: Vec<Vec<_>> = targets
        .iter()
        .map(|targets| {
            targets
                .iter()
                .filter_map(|id| indices.get(id).copied())
                .collect()
        })
        .collect();
    propagate(mir, &targets, &edges, &mut trust)?;
    Ok(trust)
}

fn body_dependencies(
    body: &mir::Body,
    hir: &hir::Program,
    properties: &crate::local::properties::Properties,
) -> BTreeSet<hir::DefId> {
    let mut targets = mir::borrow::summary::body_targets(body, hir);
    targets.extend(mir::borrow::summary::drops::dependencies(
        body, hir, properties,
    ));
    for block in &body.blocks {
        match &block.terminator {
            mir::Terminator::Spawn {
                callee: mir::Operand::Function { definition, .. },
                ..
            } => {
                targets.insert(*definition);
            }
            mir::Terminator::DynCall { trait_method, .. } => {
                targets.insert(*trait_method);
            }
            _ => {}
        }
    }
    targets
}

fn propagate(
    mir: &mir::Program,
    targets: &[BTreeSet<hir::DefId>],
    edges: &[Vec<usize>],
    trust: &mut BTreeMap<hir::DefId, BTreeSet<Trust>>,
) -> Result<(), String> {
    let mut retained = 0usize;
    for component in crate::graph::components(edges) {
        let mut combined = BTreeSet::new();
        for &node in &component {
            for dependency in std::iter::once(&mir.functions[node].definition).chain(&targets[node])
            {
                if let Some(dependencies) = trust.get(dependency) {
                    combined.extend(dependencies.iter().cloned());
                }
            }
        }
        retained = retained.saturating_add(combined.len().saturating_mul(component.len()));
        if retained > 200_000 {
            return Err("contract trust closure exceeds its resource budget".into());
        }
        for node in component {
            trust.insert(mir.functions[node].definition, combined.clone());
        }
    }
    Ok(())
}

fn seed_source(hir: &hir::Program, trust: &mut BTreeMap<hir::DefId, BTreeSet<Trust>>) {
    for function in &hir.functions {
        for statement in &function.statements {
            if let hir::StmtKind::Assume(assumption) = &statement.kind {
                trust
                    .entry(function.definition)
                    .or_default()
                    .insert(Trust::Source {
                        file: statement.span.file.0,
                        start: statement.span.start,
                        reason: assumption.reason.clone(),
                    });
            }
        }
    }
    for scope in &hir.tasks.scopes {
        for (&definition, reason) in &hir.tasks.trusted {
            trust
                .entry(scope.owner)
                .or_default()
                .insert(Trust::TrustedImpl {
                    file: hir.definitions[definition].span.file.0,
                    start: hir.definitions[definition].span.start,
                    reason: reason.clone(),
                });
        }
    }
}
