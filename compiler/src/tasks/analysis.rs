use super::*;
use crate::{
    diagnostic::Diagnostic,
    local::properties::Properties,
    mir::{
        self, Terminator,
        effects::{Effect, FunctionEffects},
    },
    symbol::Interner,
};
use std::{
    collections::{BTreeSet, HashSet},
    fmt::Write,
};

#[derive(Debug, Default)]
pub struct Report {
    pub assumptions: BTreeSet<hir::DefId>,
    pub protocols: Vec<(hir::DefId, mir::tasks::ScopeProtocol)>,
    pub diagnostics: Vec<Diagnostic>,
    pub deferred: Vec<(hir::DefId, TyId)>,
}

pub(crate) fn analyze(
    mir: &mir::Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    effects: &[FunctionEffects],
) -> Result<Report, String> {
    let mut report = Report::default();
    if hir.tasks.scopes.is_empty() {
        return Ok(report);
    }
    let properties = Properties::compute(hir);
    for body in &mir.functions {
        protocols(body, &mut report)?;
        frame(body, hir, &properties, symbols, effects, &mut report)?;
    }
    Ok(report)
}

/// A hidden body must also establish its own frame obligations without relying
/// on the exporting package having happened to contain a `spawn` expression.
pub(crate) struct FrameEvidence {
    pub established: BTreeSet<hir::DefId>,
    pub assumptions: BTreeSet<hir::DefId>,
}

pub(crate) fn independent_frames(
    mir: &mir::Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    effects: &[FunctionEffects],
) -> Result<FrameEvidence, String> {
    let properties = Properties::compute(hir);
    let mut established = BTreeSet::new();
    let mut assumptions = BTreeSet::new();
    for body in &mir.functions {
        let mut report = Report::default();
        frame(body, hir, &properties, symbols, effects, &mut report)?;
        if report.diagnostics.is_empty() && report.deferred.is_empty() {
            established.insert(body.definition);
            assumptions.extend(report.assumptions);
        }
    }
    Ok(FrameEvidence {
        established,
        assumptions,
    })
}

fn protocols(body: &mir::Body, report: &mut Report) -> Result<(), String> {
    let mut seen = HashSet::new();
    for block in &body.blocks {
        if let Terminator::TaskDrain { scope, exit, .. } = block.terminator
            && seen.insert((scope, exit))
        {
            let protocol = mir::tasks::lower_scope(body, scope, exit).map_err(|e| e.to_string())?;
            report.protocols.push((body.definition, protocol));
        }
    }
    Ok(())
}

fn frame(
    body: &mir::Body,
    hir: &hir::Program,
    properties: &Properties,
    symbols: &Interner,
    effects: &[FunctionEffects],
    report: &mut Report,
) -> Result<(), String> {
    let no_preempt = hir.definitions[body.definition]
        .attributes
        .iter()
        .any(|a| symbols.get(a.name) == "nopreempt");
    let summary = effects
        .iter()
        .find(|summary| summary.definition == body.definition);
    let thread_bound = hir
        .modular
        .functions
        .get(&body.definition)
        .is_some_and(|contract| contract.affinity);
    let protected = thread_bound
        || no_preempt
            && summary.is_some_and(|summary| {
                summary.unknown.is_empty()
                    && !summary.effects.iter().any(|effect| {
                        matches!(effect, Effect::Poll | Effect::AsyncPreempt | Effect::Park)
                    })
            });
    let required = frame_requirements(body, hir, properties, effects, protected)?;
    for (local, property) in required {
        let binding = body.local(mir::LocalId(local as u32));
        match transfer::establish(hir, properties, binding.ty, property) {
            Ok(trust) => report.assumptions.extend(trust),
            Err(reason) if reason.kind == transfer::FailureKind::MissingBound => {
                report.deferred.push((body.definition, binding.ty))
            }
            Err(reason) => report.diagnostics.push(Diagnostic::error(
                "E-TASK-LIVE",
                format!("live value does not satisfy {property:?}: {reason}"),
                binding.span,
            )),
        }
    }
    Ok(())
}

fn frame_requirements(
    body: &mir::Body,
    hir: &hir::Program,
    properties: &Properties,
    effects: &[FunctionEffects],
    protected: bool,
) -> Result<BTreeSet<(usize, transfer::Property)>, String> {
    let live = mir::borrow::live::Liveness::compute(body, properties)
        .ok_or("task liveness budget exceeded")?;
    let available = super::availability::compute(body)?;
    let mut required = BTreeSet::new();
    for (index, block) in body.blocks.iter().enumerate() {
        for (point, values) in live.before[index].iter().enumerate() {
            let park = point == block.statements.len() && is_park(&block.terminator, hir, effects);
            for &local in values {
                if !available[index][point][local]
                    || matches!(
                        body.locals[local].kind,
                        mir::LocalKind::Address | mir::LocalKind::TaskRegistry
                    )
                {
                    continue;
                }
                if !protected {
                    required.insert((local, transfer::Property::Send));
                }
                if park {
                    required.insert((local, transfer::Property::SuspendSafe));
                }
            }
        }
    }
    Ok(required)
}

fn is_park(exit: &Terminator, hir: &hir::Program, effects: &[FunctionEffects]) -> bool {
    match exit {
        Terminator::TaskDrain { .. } => true,
        Terminator::Call {
            callee: mir::Operand::Function { definition, .. },
            ..
        } => {
            hir.contracts.intrinsics.get(definition) == Some(&crate::contracts::Intrinsic::TaskJoin)
                || effects
                    .iter()
                    .find(|e| e.definition == *definition)
                    .is_none_or(|e| !e.unknown.is_empty() || e.effects.contains(&Effect::Park))
        }
        Terminator::Call { .. } | Terminator::DynCall { .. } => true,
        _ => false,
    }
}

impl Report {
    pub fn dump(&self) -> String {
        let mut output = String::from("Task typing / scoped transfer and cancellation barriers\n");
        for (definition, protocol) in &self.protocols {
            let _ = writeln!(
                output,
                "  function #{} scope s{} {:?}: checked admission and masked drain; backend={:?}",
                definition.0,
                protocol.scope.0,
                protocol.exit,
                protocol.pinned_runtime_requirement()
            );
        }
        for (definition, ty) in &self.deferred {
            let _ = writeln!(
                output,
                "  pending concrete transfer: function #{} ty{}",
                definition.0, ty.0
            );
        }
        for definition in &self.assumptions {
            let _ = writeln!(
                output,
                "  assumed trusted impl #{} (source justification retained)",
                definition.0
            );
        }
        output
    }
}
