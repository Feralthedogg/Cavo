use cavo_compiler::{
    Compilation, mir,
    mir::tasks::{self, AdmissionOutcome, Operation, ProtocolBlockId, ScopeExit, Terminator},
};

fn body() -> mir::Body {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("tasks.cavo", "void frame() {}".into())
        .unwrap();
    compilation.parse(file);
    let (_, mut program) = compilation.check_mir().expect("ordinary frame MIR");
    assert!(compilation.diagnostics.is_empty());
    program.functions.remove(0)
}

#[test]
fn every_exit_preserves_the_task_lifetime_barrier_and_original_exit_reason() {
    let body = body();
    for exit in [
        ScopeExit::Fallthrough,
        ScopeExit::Return,
        ScopeExit::Break,
        ScopeExit::Continue,
        ScopeExit::Error,
        ScopeExit::Cancel,
        ScopeExit::Panic,
    ] {
        let protocol = tasks::lower_scope(&body, mir::ScopeId(0), exit).unwrap();
        protocol.validate(&body).unwrap();
        let initial = &protocol.drain.blocks[protocol.drain.entry.0 as usize];
        assert_eq!(
            initial
                .operations
                .contains(&Operation::RequestChildCancellation),
            exit.requests_cancellation(),
        );
        assert!(matches!(
            initial.terminator,
            Terminator::WaitForAllTerminated { .. }
        ));
        assert_eq!(
            protocol.pinned_runtime_requirement(),
            tasks::BackendRequirement::CancellationImmuneManagedGroupDrain,
        );
    }
}

#[test]
fn spawn_admission_keeps_allocation_capacity_and_cancellation_distinct() {
    let body = body();
    let protocol = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Fallthrough).unwrap();
    let outcomes: Vec<_> = protocol
        .admission
        .blocks
        .iter()
        .filter_map(|block| match block.terminator {
            Terminator::FinishAdmission(outcome) => Some(outcome),
            _ => None,
        })
        .collect();
    for outcome in [
        AdmissionOutcome::Admitted,
        AdmissionOutcome::Failed(tasks::SpawnError::Allocation),
        AdmissionOutcome::Failed(tasks::SpawnError::Capacity),
        AdmissionOutcome::Failed(tasks::SpawnError::RuntimeUnavailable),
        AdmissionOutcome::ParentCancelled,
    ] {
        assert!(outcomes.contains(&outcome));
    }
    let accepted = protocol
        .admission
        .blocks
        .iter()
        .find(|block| block.terminator == Terminator::FinishAdmission(AdmissionOutcome::Admitted))
        .unwrap();
    assert!(
        accepted.operations.is_empty(),
        "published captures belong to the child"
    );
}

#[test]
fn failed_admission_cannot_leak_captures_or_free_their_record_first() {
    let body = body();
    let base = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Return).unwrap();
    for mutation in [0, 1] {
        let mut protocol = base.clone();
        let block = protocol
            .admission
            .blocks
            .iter_mut()
            .find(|block| {
                block
                    .operations
                    .contains(&Operation::ReleaseUnpublishedRecord)
            })
            .unwrap();
        if mutation == 0 {
            block.operations.remove(0);
        } else {
            block.operations.reverse();
        }
        assert!(protocol.validate(&body).is_err());
    }
}

#[test]
fn published_capture_cannot_be_dropped_by_the_parent() {
    let body = body();
    let mut protocol = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Fallthrough).unwrap();
    let block = protocol
        .admission
        .blocks
        .iter_mut()
        .find(|block| block.terminator == Terminator::FinishAdmission(AdmissionOutcome::Admitted))
        .unwrap();
    block.operations.push(Operation::DropPreparedCaptures);
    assert!(protocol.validate(&body).is_err());
}

#[test]
fn cancellation_requests_are_required_only_when_leaving_the_scope_early() {
    let body = body();
    let mut abrupt = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Return).unwrap();
    abrupt.drain.blocks[0]
        .operations
        .retain(|op| *op != Operation::RequestChildCancellation);
    assert!(abrupt.validate(&body).is_err());
    let mut normal = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Fallthrough).unwrap();
    normal.drain.blocks[0]
        .operations
        .push(Operation::RequestChildCancellation);
    assert!(normal.validate(&body).is_err());
}

#[test]
fn loans_and_records_cannot_be_released_before_actual_termination() {
    let body = body();
    let base = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Cancel).unwrap();
    for operation in [Operation::ReleaseScopeLoans, Operation::ReclaimChildRecords] {
        let mut protocol = base.clone();
        protocol.drain.blocks[0].operations.push(operation);
        assert!(protocol.validate(&body).is_err());
    }
    let mut bypass = base;
    bypass.drain.blocks[0].terminator = Terminator::Goto(ProtocolBlockId(1));
    assert!(bypass.validate(&body).is_err());
}

#[test]
fn fatal_drain_failure_cannot_resume_cleanup_or_erase_parent_cancellation() {
    let body = body();
    let base = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Cancel).unwrap();
    let mut failure = base.clone();
    failure.drain.blocks[2].terminator = Terminator::Goto(ProtocolBlockId(1));
    assert!(failure.validate(&body).is_err());
    let mut swallowed = base;
    swallowed.drain.blocks[1].terminator = Terminator::ContinueCleanup(ScopeExit::Fallthrough);
    assert!(swallowed.validate(&body).is_err());
}

#[test]
fn malformed_scope_targets_and_join_retry_cycles_are_rejected() {
    let body = body();
    assert!(tasks::lower_scope(&body, mir::ScopeId(u32::MAX), ScopeExit::Return).is_err());
    let base = tasks::lower_scope(&body, mir::ScopeId(0), ScopeExit::Return).unwrap();
    let mut bad_target = base.clone();
    bad_target.admission.blocks[0].terminator = Terminator::Goto(ProtocolBlockId(u32::MAX));
    assert!(bad_target.validate(&body).is_err());
    let mut retry = base;
    retry.drain.blocks[2].terminator = Terminator::Goto(ProtocolBlockId(0));
    assert!(retry.validate(&body).is_err());
}
