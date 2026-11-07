//! Effects of the current MIR, before runtime/checkpoint insertion. Source body
//! inference and trusted external assumptions retain distinct provenance.

mod dispatch;
mod source;

pub(crate) use source::validate_defers;
pub use source::{CleanupCandidates, CleanupError, cleanup_candidates, validate_cleanup_body};

use super::{BlockId, Body, ExitKind, InvariantError, Operand, Program, Terminator};
use crate::{
    external::{AssumptionId, SummaryReport, SummaryStatus},
    graph, hir,
    source::Span,
    symbol::Interner,
    syntax::token::TokenKind,
};
use std::collections::{BTreeSet, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Effect {
    MemoryWrite,
    MemoryFree,
    Poll,
    AsyncPreempt,
    Park,
    Cancel,
    Panic,
    Allocate,
    Ffi,
    Block,
    Thread,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Unknown {
    ExternalCall,
    IndirectCall,
    DropGlue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Boundedness {
    Established,
    Unknown,
    MayDiverge,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionEffects {
    pub definition: hir::DefId,
    pub effects: BTreeSet<Effect>,
    pub unknown: BTreeSet<Unknown>,
    pub assumptions: BTreeSet<AssumptionId>,
    pub bounded: Boundedness,
    /// Fatal traps do not become catchable panic effects.
    pub may_abort: bool,
}

impl FunctionEffects {
    fn empty(definition: hir::DefId) -> Self {
        Self {
            definition,
            effects: BTreeSet::new(),
            unknown: BTreeSet::new(),
            assumptions: BTreeSet::new(),
            bounded: Boundedness::Established,
            may_abort: false,
        }
    }

    fn include(&mut self, other: &Self) {
        self.effects.extend(&other.effects);
        self.unknown.extend(&other.unknown);
        self.assumptions.extend(&other.assumptions);
        self.bounded = self.bounded.max(other.bounded);
        self.may_abort |= other.may_abort;
    }

    pub fn cleanup_safe(&self) -> bool {
        self.bounded == Boundedness::Established
            && self.unknown.is_empty()
            && self.effects.is_disjoint(&cleanup_forbidden())
    }
}

#[derive(Debug)]
pub struct EffectViolation {
    pub definition: hir::DefId,
    pub span: Span,
    pub message: String,
}

#[derive(Debug)]
pub struct Report {
    pub functions: Vec<FunctionEffects>,
    pub violations: Vec<EffectViolation>,
    indices: Vec<Option<usize>>,
    /// These later transformations must invalidate/recompute this report.
    pub not_analyzed: Vec<&'static str>,
}

impl Report {
    pub fn get(&self, definition: hir::DefId) -> Option<&FunctionEffects> {
        let index = self.indices.get(definition.0 as usize).copied().flatten()?;
        self.functions.get(index)
    }
}

/// The caller must validate MIR first. Invalid graph references still return an
/// error here rather than indexing arbitrary input. The report is not a proof of
/// heap validity, alias permissions, machine-PC preemption, or external honesty.
pub fn analyze(
    mir: &Program,
    hir: &hir::Program,
    symbols: &Interner,
    external: &[SummaryReport],
) -> Result<Report, InvariantError> {
    analyze_inner(mir, hir, symbols, external, None)
}

/// The caller owns the canonical elaborated plan for this exact MIR snapshot.
/// An absent plan remains opaque; no user annotation can manufacture one.
pub(crate) fn analyze_with_cleanup(
    mir: &Program,
    hir: &hir::Program,
    symbols: &Interner,
    external: &[SummaryReport],
    cleanup: &super::drop::Program,
) -> Result<Report, InvariantError> {
    analyze_inner(mir, hir, symbols, external, Some(cleanup))
}

fn analyze_inner(
    mir: &Program,
    hir: &hir::Program,
    symbols: &Interner,
    external: &[SummaryReport],
    cleanup: Option<&super::drop::Program>,
) -> Result<Report, InvariantError> {
    let targets = Targets {
        hir,
        declared: hir
            .modular
            .functions
            .iter()
            .filter(|(definition, _)| crate::modular::usable(hir, **definition))
            .map(|(&definition, contract)| (definition, contract))
            .collect(),
        intrinsics: &hir.contracts.intrinsics,
        bodies: body_indices(mir, hir)?,
        external: external_index(external, hir.definitions.len())?,
        foreign: hir
            .definitions
            .iter()
            .map(|definition| definition.foreign_abi.is_some())
            .collect(),
    };
    let mut summaries = Vec::with_capacity(mir.functions.len());
    let mut calls = Vec::with_capacity(mir.functions.len());
    for body in &mir.functions {
        let (mut summary, mut dependencies) = scan_body(body, hir, &targets, cleanup.is_some())?;
        if let Some(cleanup) = cleanup {
            scan_cleanup(
                body.definition,
                cleanup,
                &targets,
                &mut summary,
                &mut dependencies,
            )?;
        }
        summaries.push(summary);
        calls.push(dependencies.into_iter().collect());
    }
    mark_recursive_bodies(mir, &targets, &calls, &mut summaries);
    propagate(&calls, &mut summaries)?;
    let mut violations = check_bounds(hir, symbols, &summaries);
    violations.extend(check_cleanup_calls(mir, hir, &targets, &summaries));
    if let Some(cleanup) = cleanup {
        violations.extend(check_drop_bodies(cleanup, &targets, &summaries));
    }
    Ok(Report {
        functions: summaries,
        violations,
        indices: targets.bodies,
        not_analyzed: vec![
            "runtime/checkpoint insertion and machine-PC asynchronous preemption",
            "external boundedness and cancellation contracts absent from summary schema",
            "heap/alias validity and unresolved generic or opaque Drop effects",
        ],
    })
}

fn body_indices(mir: &Program, hir: &hir::Program) -> Result<Vec<Option<usize>>, InvariantError> {
    let mut indices = vec![None; hir.definitions.len()];
    for (index, body) in mir.functions.iter().enumerate() {
        let entry = indices
            .get_mut(body.definition.0 as usize)
            .ok_or_else(|| error("effect analysis found an invalid function ID"))?;
        if entry.replace(index).is_some() {
            return Err(error("effect analysis found duplicate function bodies"));
        }
    }
    Ok(indices)
}

fn mark_recursive_bodies(
    mir: &Program,
    targets: &Targets<'_>,
    calls: &[Vec<usize>],
    summaries: &mut [FunctionEffects],
) {
    // A bounded declaration is a call-site promise, never evidence that its own
    // recursive implementation terminates. Keep recursion independent of it.
    let edges: Vec<Vec<usize>> = mir
        .functions
        .iter()
        .enumerate()
        .map(|(index, body)| {
            // Destructor and finite dynamic-call dependencies participate too;
            // a local drop can recurse without a direct Core Call terminator.
            let mut edges = calls[index].clone();
            edges.extend(
                body.blocks
                    .iter()
                    .filter_map(|block| match &block.terminator {
                        Terminator::Call {
                            callee: Operand::Function { definition, .. },
                            ..
                        } => targets.bodies.get(definition.0 as usize).copied().flatten(),
                        _ => None,
                    }),
            );
            edges.sort_unstable();
            edges.dedup();
            edges
        })
        .collect();
    for component in graph::components(&edges) {
        if component.len() > 1 || edges[component[0]].contains(&component[0]) {
            for node in component {
                summaries[node].bounded = Boundedness::MayDiverge;
            }
        }
    }
}

fn external_index(
    reports: &[SummaryReport],
    count: usize,
) -> Result<Vec<Option<&SummaryReport>>, InvariantError> {
    let mut index = vec![None; count];
    for report in reports {
        if report.status != SummaryStatus::Assumed {
            continue;
        }
        let slot = index
            .get_mut(report.function.0 as usize)
            .ok_or_else(|| error("effect assumption has an invalid function ID"))?;
        if slot.replace(report).is_some() {
            return Err(error("duplicate external effect assumptions"));
        }
    }
    Ok(index)
}

struct Targets<'a> {
    hir: &'a hir::Program,
    declared: std::collections::BTreeMap<hir::DefId, &'a crate::modular::Contract>,
    intrinsics: &'a std::collections::BTreeMap<hir::DefId, crate::contracts::Intrinsic>,
    bodies: Vec<Option<usize>>,
    external: Vec<Option<&'a SummaryReport>>,
    foreign: Vec<bool>,
}

fn scan_body(
    body: &Body,
    hir: &hir::Program,
    targets: &Targets<'_>,
    has_cleanup: bool,
) -> Result<(FunctionEffects, BTreeSet<usize>), InvariantError> {
    let edges = cfg_edges(body)?;
    let reachable = reachable_blocks(body.entry, &edges)?;
    let mut summary = FunctionEffects::empty(body.definition);
    let mut dependencies = BTreeSet::new();
    let witnesses = body
        .blocks
        .iter()
        .any(|block| matches!(block.terminator, Terminator::DynCall { .. }))
        .then(|| dispatch::Witnesses::compute(body));
    for (index, block) in body.blocks.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        if block.statements.iter().any(|statement| matches!(&statement.kind,
            super::StatementKind::Assign { destination, .. } if destination.projection.contains(&super::Projection::Deref))) {
            summary.effects.insert(Effect::MemoryWrite);
        }
        match &block.terminator {
            Terminator::Spawn { .. } => {
                summary
                    .effects
                    .extend([Effect::Allocate, Effect::AsyncPreempt, Effect::Cancel]);
            }
            Terminator::TaskDrain { .. } => {
                summary.effects.insert(Effect::Park);
            }
            Terminator::Call { callee, .. } => {
                scan_call(callee, targets, &mut summary, &mut dependencies)?;
            }
            Terminator::DynCall {
                receiver,
                trait_method,
                ..
            } => {
                scan_dynamic(
                    receiver,
                    *trait_method,
                    witnesses.as_ref(),
                    hir,
                    targets,
                    &mut summary,
                    &mut dependencies,
                )?;
            }
            Terminator::Drop { .. } if !has_cleanup => {
                summary.unknown.insert(Unknown::DropGlue);
                summary.bounded = summary.bounded.max(Boundedness::Unknown);
            }
            Terminator::Checked { .. } | Terminator::Bounds { .. } | Terminator::Abort => {
                summary.may_abort = true;
            }
            _ => {}
        }
    }
    if has_cycle(&edges, &reachable) {
        summary.bounded = Boundedness::MayDiverge;
    }
    record_direct_resumes(body, &edges, &mut summary)?;
    Ok((summary, dependencies))
}

fn scan_cleanup(
    definition: hir::DefId,
    cleanup: &super::drop::Program,
    targets: &Targets<'_>,
    summary: &mut FunctionEffects,
    dependencies: &mut BTreeSet<usize>,
) -> Result<(), InvariantError> {
    use super::drop::Terminator as T;
    let body = cleanup
        .functions
        .iter()
        .find(|body| body.definition == definition)
        .ok_or_else(|| error("effect analysis has no matching cleanup body"))?;
    let mut pending: Vec<_> = body
        .blocks
        .iter()
        .filter_map(|block| match block.terminator {
            T::InvokeGlue { glue, .. } => Some(glue),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > 200_000 {
            return Err(error("cleanup effect graph exceeds its work budget"));
        }
        let glue = cleanup
            .glue
            .get(id.0 as usize)
            .ok_or_else(|| error("invalid effect glue ID"))?;
        scan_cleanup_glue(&glue.kind, &mut pending, targets, summary, dependencies)?;
    }
    Ok(())
}

fn scan_cleanup_glue(
    kind: &super::drop::GlueKind,
    pending: &mut Vec<super::drop::GlueId>,
    targets: &Targets<'_>,
    summary: &mut FunctionEffects,
    dependencies: &mut BTreeSet<usize>,
) -> Result<(), InvariantError> {
    use super::drop::GlueKind as G;
    match kind {
        G::Trivial => {}
        G::Record(fields) => pending.extend(fields.iter().map(|field| field.glue)),
        G::Enum(variants) => pending.extend(
            variants
                .iter()
                .flat_map(|variant| variant.fields.iter().copied()),
        ),
        G::Array { element, .. }
        | G::SymbolicArray { element, .. }
        | G::ArrayTail { element, .. } => pending.push(*element),
        G::User {
            destructor, fields, ..
        } => {
            scan_destructor(destructor.definition, targets, summary, dependencies)?;
            pending.push(*fields);
        }
        G::Destructor { destructor, .. } => {
            scan_destructor(destructor.definition, targets, summary, dependencies)?
        }
        G::TaskHandle | G::Parameter { .. } | G::Manual => {
            summary.unknown.insert(Unknown::DropGlue);
            summary.bounded = summary.bounded.max(Boundedness::Unknown);
        }
    }
    Ok(())
}

fn scan_destructor(
    definition: hir::DefId,
    targets: &Targets<'_>,
    summary: &mut FunctionEffects,
    dependencies: &mut BTreeSet<usize>,
) -> Result<(), InvariantError> {
    scan_call(
        &Operand::Function {
            definition,
            ty: targets.hir.definitions[definition].ty,
        },
        targets,
        summary,
        dependencies,
    )
}

fn check_drop_bodies(
    cleanup: &super::drop::Program,
    targets: &Targets<'_>,
    summaries: &[FunctionEffects],
) -> Vec<EffectViolation> {
    use super::drop::GlueKind;
    let mut seen = HashSet::new();
    let mut failures = Vec::new();
    for glue in &cleanup.glue {
        let definition = match &glue.kind {
            GlueKind::User { destructor, .. } | GlueKind::Destructor { destructor, .. } => {
                destructor.definition
            }
            _ => continue,
        };
        if !seen.insert(definition) {
            continue;
        }
        let summary = targets
            .bodies
            .get(definition.0 as usize)
            .copied()
            .flatten()
            .and_then(|index| summaries.get(index));
        if summary.is_none_or(|summary| !summary.cleanup_safe()) {
            failures.push(EffectViolation {
                definition,
                span: targets.hir.definitions[definition].span,
                message: "transformed destructor must retain bounded nosuspend, nocancel, nopanic and noalloc effects".into(),
            });
        }
    }
    failures
}

fn scan_call(
    callee: &Operand,
    targets: &Targets<'_>,
    summary: &mut FunctionEffects,
    dependencies: &mut BTreeSet<usize>,
) -> Result<(), InvariantError> {
    let Operand::Function { definition, .. } = callee else {
        summary.unknown.insert(Unknown::IndirectCall);
        summary.bounded = summary.bounded.max(Boundedness::Unknown);
        return Ok(());
    };
    let index = definition.0 as usize;
    if let Some(&role) = targets.intrinsics.get(definition) {
        intrinsic_effects(role, summary);
        return Ok(());
    }
    if let Some(contract) = targets.declared.get(definition) {
        summary.effects.extend(&contract.upper);
        if !contract.bounded {
            summary.bounded = summary.bounded.max(Boundedness::Unknown);
        }
        return Ok(());
    }
    let target = targets
        .bodies
        .get(index)
        .ok_or_else(|| error("effect call has an invalid definition ID"))?;
    if let Some(target) = target {
        dependencies.insert(*target);
    } else {
        if targets.foreign[index] {
            summary.effects.insert(Effect::Ffi);
        }
        summary.unknown.insert(Unknown::ExternalCall);
        summary.bounded = summary.bounded.max(Boundedness::Unknown);
        if let Some(report) = targets.external[index] {
            summary.assumptions.insert(report.assumption);
            external_effects(report, summary);
        }
    }
    Ok(())
}

fn intrinsic_effects(role: crate::contracts::Intrinsic, summary: &mut FunctionEffects) {
    use crate::contracts::Intrinsic as I;
    match role {
        I::Allocate => {
            summary.effects.insert(Effect::Allocate);
            summary.may_abort = true;
        }
        I::TaskJoin => {
            summary.effects.extend([Effect::Park, Effect::Cancel]);
        }
        I::Deallocate => {
            summary.effects.insert(Effect::MemoryFree);
            summary.may_abort = true;
        }
        I::Take | I::Initialize | I::Replace | I::WriteUnaligned => {
            summary.effects.insert(Effect::MemoryWrite);
            summary.may_abort = true;
        }
        I::Read | I::ReadUnaligned => {
            summary.may_abort = true;
        }
        _ => {}
    }
}

fn scan_dynamic(
    receiver: &Operand,
    method: hir::DefId,
    witnesses: Option<&dispatch::Witnesses>,
    hir: &hir::Program,
    targets: &Targets<'_>,
    summary: &mut FunctionEffects,
    dependencies: &mut BTreeSet<usize>,
) -> Result<(), InvariantError> {
    if targets.declared.contains_key(&method) {
        let callee = Operand::Function {
            definition: method,
            ty: hir.definitions[method].ty,
        };
        return scan_call(&callee, targets, summary, dependencies);
    }
    let Some(implementations) =
        witnesses.and_then(|witnesses| witnesses.targets(receiver, method, hir))
    else {
        summary.unknown.insert(Unknown::IndirectCall);
        summary.bounded = summary.bounded.max(Boundedness::Unknown);
        return Ok(());
    };
    for definition in implementations {
        let operand = Operand::Function {
            definition,
            ty: hir.definitions[definition].ty,
        };
        scan_call(&operand, targets, summary, dependencies)?;
    }
    Ok(())
}

fn external_effects(report: &SummaryReport, summary: &mut FunctionEffects) {
    // False explicitly permits an effect. True is only an assumed absence;
    // missing cancellation/boundedness facts keep this call cleanup-ineligible.
    for (absence, effect) in [
        (report.effects.no_unwind, Effect::Panic),
        (report.effects.no_suspend, Effect::Park),
        (report.effects.no_block, Effect::Block),
        (report.effects.no_allocate, Effect::Allocate),
    ] {
        if absence == Some(false) {
            summary.effects.insert(effect);
        }
    }
}

pub(super) fn propagate(
    edges: &[Vec<usize>],
    summaries: &mut [FunctionEffects],
) -> Result<(), InvariantError> {
    let mut retained_assumptions = 0usize;
    for component in graph::components(edges) {
        let mut combined = FunctionEffects::empty(summaries[component[0]].definition);
        let members: HashSet<_> = component.iter().copied().collect();
        let recursive = component.len() > 1 || edges[component[0]].contains(&component[0]);
        for &node in &component {
            combined.include(&summaries[node]);
            for &dependency in &edges[node] {
                if !members.contains(&dependency) {
                    combined.include(&summaries[dependency]);
                }
            }
        }
        if recursive {
            combined.bounded = Boundedness::MayDiverge;
        }
        retained_assumptions = retained_assumptions
            .checked_add(combined.assumptions.len().saturating_mul(component.len()))
            .ok_or_else(|| error("effect assumption closure exceeds its resource limit"))?;
        if retained_assumptions > 200_000 {
            return Err(error(
                "effect assumption closure exceeds its resource limit",
            ));
        }
        // Union effects are identical throughout an SCC. This computes its
        // least fixed point once after dependency components, without rescans.
        for node in component {
            combined.definition = summaries[node].definition;
            summaries[node] = combined.clone();
        }
    }
    Ok(())
}

fn cfg_edges(body: &Body) -> Result<Vec<Vec<usize>>, InvariantError> {
    if body.blocks.len() > 200_000 {
        return Err(error("effect CFG exceeds its resource limit"));
    }
    let mut edges = Vec::with_capacity(body.blocks.len());
    for block in &body.blocks {
        let targets = successors(&block.terminator);
        if targets
            .iter()
            .any(|target| target.0 as usize >= body.blocks.len())
        {
            return Err(error("effect CFG has an invalid successor"));
        }
        edges.push(
            targets
                .into_iter()
                .map(|target| target.0 as usize)
                .collect(),
        );
    }
    Ok(edges)
}

fn successors(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Spawn {
            normal,
            panic,
            cancel,
            ..
        } => vec![*normal, *panic, *cancel],
        Terminator::TaskDrain { next, abort, .. } => vec![*next, *abort],
        Terminator::Goto(target) => vec![*target],
        Terminator::IteratorNext { some, none, .. } => vec![*some, *none],
        Terminator::Switch { condition, yes, no } => match condition {
            Operand::Constant {
                value: hir::Constant::Bool(value),
                ..
            } => {
                vec![if *value { *yes } else { *no }]
            }
            _ => vec![*yes, *no],
        },
        Terminator::Call {
            normal,
            panic,
            cancel,
            ..
        }
        | Terminator::DynCall {
            normal,
            panic,
            cancel,
            ..
        } => vec![*normal, *panic, *cancel],
        Terminator::Checked { normal, trap, .. } | Terminator::Bounds { normal, trap, .. } => {
            vec![*normal, *trap]
        }
        Terminator::Drop { next, unwind, .. } => vec![*next, *unwind],
        Terminator::Return
        | Terminator::Resume(_)
        | Terminator::Abort
        | Terminator::Unreachable => Vec::new(),
    }
}

fn reachable_blocks(entry: BlockId, edges: &[Vec<usize>]) -> Result<Vec<bool>, InvariantError> {
    if entry.0 as usize >= edges.len() {
        return Err(error("effect CFG has an invalid entry"));
    }
    let mut seen = vec![false; edges.len()];
    let mut pending = vec![entry.0 as usize];
    while let Some(block) = pending.pop() {
        if std::mem::replace(&mut seen[block], true) {
            continue;
        }
        pending.extend(&edges[block]);
    }
    Ok(seen)
}

fn has_cycle(edges: &[Vec<usize>], reachable: &[bool]) -> bool {
    graph::components(edges).into_iter().any(|component| {
        reachable[component[0]]
            && (component.len() > 1 || edges[component[0]].contains(&component[0]))
    })
}

fn record_direct_resumes(
    body: &Body,
    edges: &[Vec<usize>],
    summary: &mut FunctionEffects,
) -> Result<(), InvariantError> {
    let reachable = reachable_without_call_failure(body, edges)?;
    for (index, block) in body.blocks.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        match block.terminator {
            Terminator::Resume(ExitKind::Panic) => {
                summary.effects.insert(Effect::Panic);
            }
            Terminator::Resume(ExitKind::Cancel) => {
                summary.effects.insert(Effect::Cancel);
            }
            _ => {}
        }
    }
    Ok(())
}

fn reachable_without_call_failure(
    body: &Body,
    edges: &[Vec<usize>],
) -> Result<Vec<bool>, InvariantError> {
    if body.entry.0 as usize >= edges.len() {
        return Err(error("effect CFG has an invalid entry"));
    }
    let mut seen = vec![false; edges.len()];
    let mut pending = vec![body.entry.0 as usize];
    while let Some(block) = pending.pop() {
        if std::mem::replace(&mut seen[block], true) {
            continue;
        }
        if let Terminator::Call { normal, .. } | Terminator::DynCall { normal, .. } =
            body.blocks[block].terminator
        {
            pending.push(normal.0 as usize);
        } else {
            pending.extend(&edges[block]);
        }
    }
    Ok(seen)
}

fn check_bounds(
    hir: &hir::Program,
    symbols: &Interner,
    summaries: &[FunctionEffects],
) -> Vec<EffectViolation> {
    let mut violations = Vec::new();
    for summary in summaries {
        let definition = &hir.definitions[summary.definition];
        if let Some(contract) = hir.modular.functions.get(&summary.definition) {
            if !summary.effects.is_subset(&contract.upper)
                || contract.bounded && summary.bounded != Boundedness::Established
                || !summary.unknown.is_empty() && contract.upper != all_effects()
            {
                violations.push(violation(
                    summary.definition,
                    definition.span,
                    "implementation effects do not refine the declaration contract".into(),
                ));
            }
            continue;
        }
        for attribute in &definition.attributes {
            let name = symbols.get(attribute.name);
            let forbidden = match attribute_bound(name, attribute, symbols) {
                Ok(Some(forbidden)) => forbidden,
                Ok(None) => continue,
                Err(message) => {
                    violations.push(violation(summary.definition, definition.span, message));
                    continue;
                }
            };
            let exceeds = !summary.effects.is_disjoint(&forbidden);
            if exceeds || (!summary.unknown.is_empty() && !forbidden.is_empty()) {
                violations.push(violation(
                    summary.definition,
                    definition.span,
                    format!(
                        "cannot establish @{name}: body effects exceed its bound or remain unknown"
                    ),
                ));
            }
        }
    }
    violations
}

fn check_cleanup_calls(
    mir: &Program,
    hir: &hir::Program,
    targets: &Targets<'_>,
    summaries: &[FunctionEffects],
) -> Vec<EffectViolation> {
    let mut violations = Vec::new();
    for body in &mir.functions {
        let witnesses = body
            .blocks
            .iter()
            .any(|block| matches!(block.terminator, Terminator::DynCall { .. }))
            .then(|| dispatch::Witnesses::compute(body));
        for block in &body.blocks {
            if block.cleanup.is_none() {
                continue;
            }
            let methods = match &block.terminator {
                Terminator::Call {
                    callee: Operand::Function { definition, .. },
                    ..
                } => Some(BTreeSet::from([*definition])),
                Terminator::Call { .. } => None,
                Terminator::DynCall {
                    receiver,
                    trait_method,
                    ..
                } => witnesses
                    .as_ref()
                    .and_then(|witnesses| witnesses.targets(receiver, *trait_method, hir)),
                _ => continue,
            };
            let established = methods.is_some_and(|methods| {
                methods.into_iter().all(|definition| {
                    if let Some(contract) = targets.declared.get(&definition) {
                        return contract.cleanup_safe();
                    }
                    targets
                        .bodies
                        .get(definition.0 as usize)
                        .copied()
                        .flatten()
                        .is_some_and(|index| summaries[index].cleanup_safe())
                })
            });
            // Redirecting failures to Abort enforces fatal cleanup failure, but
            // does not prove boundedness or the absence of forbidden effects.
            if !established {
                violations.push(violation(
                    body.definition,
                    block.span,
                    "cleanup call lacks established bounded nosuspend, nocancel, nopanic and noalloc effects".into(),
                ));
            }
        }
    }
    violations
}

fn attribute_bound(
    name: &str,
    attribute: &hir::Attribute,
    symbols: &Interner,
) -> Result<Option<BTreeSet<Effect>>, String> {
    let one = match name {
        "nosuspend" => Some(Effect::Park),
        "nocancel" => Some(Effect::Cancel),
        "nopanic" => Some(Effect::Panic),
        "noalloc" => Some(Effect::Allocate),
        _ => None,
    };
    if let Some(effect) = one {
        return Ok(Some(BTreeSet::from([effect])));
    }
    if name != "effects" {
        return Ok(None);
    }
    let mut permitted = BTreeSet::new();
    for token in &attribute.arguments {
        match token.kind {
            TokenKind::Ident(symbol) => {
                let name = symbols.get(symbol);
                permitted
                    .insert(effect_named(name).ok_or_else(|| format!("unknown effect `{name}`"))?);
            }
            TokenKind::Comma | TokenKind::Pipe => {}
            _ => return Err("effect bounds contain only effect names and separators".into()),
        }
    }
    Ok(Some(
        all_effects().difference(&permitted).copied().collect(),
    ))
}

fn effect_named(name: &str) -> Option<Effect> {
    Some(match name {
        "poll" => Effect::Poll,
        "async_preempt" => Effect::AsyncPreempt,
        "park" => Effect::Park,
        "cancel" => Effect::Cancel,
        "panic" => Effect::Panic,
        "alloc" => Effect::Allocate,
        "ffi" => Effect::Ffi,
        "block" => Effect::Block,
        "thread" => Effect::Thread,
        _ => return None,
    })
}

pub(crate) fn all_effects() -> BTreeSet<Effect> {
    BTreeSet::from([
        Effect::MemoryWrite,
        Effect::MemoryFree,
        Effect::Poll,
        Effect::AsyncPreempt,
        Effect::Park,
        Effect::Cancel,
        Effect::Panic,
        Effect::Allocate,
        Effect::Ffi,
        Effect::Block,
        Effect::Thread,
    ])
}

fn cleanup_forbidden() -> BTreeSet<Effect> {
    BTreeSet::from([
        Effect::Poll,
        Effect::AsyncPreempt,
        Effect::Park,
        Effect::Cancel,
        Effect::Panic,
        Effect::Allocate,
        Effect::Block,
        Effect::Thread,
    ])
}

fn violation(definition: hir::DefId, span: Span, message: String) -> EffectViolation {
    EffectViolation {
        definition,
        span,
        message,
    }
}
fn error(message: &str) -> InvariantError {
    InvariantError::new(message.into())
}
