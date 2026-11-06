//! Retained scalar guards use their actual success and fatal failure edges.
//! Certificates are invalidated whenever their MIR/declaration snapshot changes.

use super::*;
use crate::arena::Access as _;
use crate::{
    hir,
    mir::{self, BlockId, Operand, Terminator},
    symbol::Interner,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn collect(
    mir: &mir::Program,
    hir: &hir::Program,
    symbols: &Interner,
    report: &mut Report,
) -> Result<(), String> {
    for body in &mir.functions {
        let incoming = incoming(body)?;
        for (index, block) in body.blocks.iter().enumerate() {
            let Some((success, failure, operands, operation)) = retained(&block.terminator) else {
                continue;
            };
            let check_block = BlockId(index as u32);
            immediate_edge(body, check_block, success, failure, &incoming)?;
            let dependencies = dependencies(check_block, operands);
            let plan = GuardPlan {
                definition: body.definition,
                checks: vec![GuardCheck {
                    block: check_block,
                    success,
                    failure,
                    dependencies: dependencies.clone(),
                }],
                pure: true,
                nosuspend: true,
                noalloc: true,
            };
            let id = GuardPlanId(report.guards.len() as u32);
            let certificate = plan.certify(
                id,
                success,
                &BTreeSet::from([check_block, success]),
                &dependencies,
            )?;
            report.guards.push(plan);
            report.certificates.push(certificate);
            let name = crate::external::interface::qualified(hir, symbols, body.definition);
            report.obligations.push(Obligation {
                key: source::obligation_key(&name, index, operation),
                span: block.span,
                operation: operation.into(),
                components: vec![Component {
                    name: "safe guard and fatal failure edge".into(),
                    assessment: Assessment::Guarded(id),
                }],
            });
        }
    }
    Ok(())
}

type Retained<'a> = (BlockId, BlockId, Vec<&'a Operand>, &'static str);

fn retained(terminator: &Terminator) -> Option<Retained<'_>> {
    match terminator {
        Terminator::Checked {
            value,
            normal,
            trap,
            ..
        } => {
            let operands = match value {
                mir::Rvalue::Unary { operand, .. } => vec![operand],
                mir::Rvalue::Binary { left, right, .. } => vec![left, right],
                _ => return None,
            };
            Some((*normal, *trap, operands, "checked arithmetic"))
        }
        // Bounds and scalar preconditions retain their own verifier rules. A
        // plain user branch is not promoted to a memory guard certificate.
        _ => None,
    }
}

pub(super) fn verify(
    mir: &mir::Program,
    plans: &[GuardPlan],
    certificates: &[GuardUseCertificate],
) -> Result<(), String> {
    if plans.len() != certificates.len() {
        return Err("guard plan/certificate count mismatch".into());
    }
    let incoming: BTreeMap<_, _> = mir
        .functions
        .iter()
        .map(|body| Ok((body.definition, (body, incoming(body)?))))
        .collect::<Result<_, String>>()?;
    for (index, certificate) in certificates.iter().enumerate() {
        if certificate.plan.0 as usize != index {
            return Err("guard certificates are duplicated or out of order".into());
        }
        let plan = plans
            .get_id(certificate.plan)
            .ok_or("invalid guard plan ID")?;
        let (body, predecessors) = incoming
            .get(&plan.definition)
            .ok_or("guard definition no longer has a MIR body")?;
        verify_use(body, predecessors, plan, certificate)?;
    }
    Ok(())
}

fn dependencies(block: BlockId, operands: Vec<&Operand>) -> BTreeMap<Dependency, u64> {
    operands
        .into_iter()
        .filter_map(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                Some((Dependency::Value(place.local), u64::from(block.0)))
            }
            _ => None,
        })
        .collect()
}

fn incoming(body: &mir::Body) -> Result<Vec<BTreeSet<BlockId>>, String> {
    let mut incoming = vec![BTreeSet::new(); body.blocks.len()];
    for (index, block) in body.blocks.iter().enumerate() {
        for target in mir::borrow::successors(&block.terminator) {
            incoming
                .get_mut(target.0 as usize)
                .ok_or("guard CFG target is invalid")?
                .insert(BlockId(index as u32));
        }
    }
    Ok(incoming)
}

fn immediate_edge(
    body: &mir::Body,
    check: BlockId,
    success: BlockId,
    failure: BlockId,
    incoming: &[BTreeSet<BlockId>],
) -> Result<(), String> {
    // These certificates describe entry to the immediate success block only.
    // A unique incoming edge excludes bypasses and any intervening mutation.
    if success == body.entry
        || success == failure
        || incoming.get(success.0 as usize) != Some(&BTreeSet::from([check]))
    {
        return Err("guard success edge does not dominate its immediate use".into());
    }
    let failure = body
        .blocks
        .get_id(failure)
        .ok_or("guard failure block is invalid")?;
    if !failure.statements.is_empty() || !matches!(failure.terminator, Terminator::Abort) {
        return Err("a retained contract guard does not abort immediately on failure".into());
    }
    Ok(())
}

fn verify_use(
    body: &mir::Body,
    incoming: &[BTreeSet<BlockId>],
    plan: &GuardPlan,
    certificate: &GuardUseCertificate,
) -> Result<(), String> {
    let [check] = plan.checks.as_slice() else {
        return Err("retained arithmetic must have exactly one immediate guard".into());
    };
    let (success, failure, operands, _) = body
        .blocks
        .get_id(check.block)
        .and_then(|block| retained(&block.terminator))
        .ok_or("guard certificate no longer describes a retained MIR check")?;
    if success != check.success
        || failure != check.failure
        || certificate.use_block != success
        || dependencies(check.block, operands) != check.dependencies
        || certificate.dependencies != check.dependencies
    {
        return Err("guard edges, operands or dependency versions no longer match".into());
    }
    immediate_edge(body, check.block, success, failure, incoming)?;
    plan.certify(
        certificate.plan,
        success,
        &BTreeSet::from([check.block, success]),
        &certificate.dependencies,
    )?;
    Ok(())
}
