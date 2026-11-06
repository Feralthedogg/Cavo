//! Typed task admission and scope-drain protocol IR, before runtime ABI lowering.
//!
//! This models ownership at publication and the non-cancellable lifetime barrier.
//! It neither launches tasks nor authorizes scoped code on LLAM 3.0.0: that release
//! does not provide the required cancellation-immune managed group drain.

use super::{Body, ScopeId};
use std::{collections::VecDeque, fmt};

const BLOCK_LIMIT: usize = 128;
const TRANSITION_LIMIT: usize = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ScopeExit {
    Fallthrough,
    Return,
    Break,
    Continue,
    Error,
    Cancel,
    Panic,
}

impl ScopeExit {
    pub fn requests_cancellation(self) -> bool {
        self != Self::Fallthrough
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpawnError {
    Allocation,
    Capacity,
    RuntimeUnavailable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdmissionOutcome {
    Admitted,
    Failed(SpawnError),
    ParentCancelled,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProtocolBlockId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Admission,
    Drain,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    DropPreparedCaptures,
    ReleaseUnpublishedRecord,
    SealAdmission,
    RequestChildCancellation,
    /// Includes dropping results whose observation handle was explicitly ignored.
    ReclaimChildRecords,
    DestroyEmptyGroup,
    ReleaseScopeLoans,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    Goto(ProtocolBlockId),
    PrepareRecord {
        ready: ProtocolBlockId,
        allocation_failed: ProtocolBlockId,
    },
    /// Admission, group registration and capture transfer are one publication
    /// boundary, serialized against parent cancellation and closing admission.
    PublishChild {
        admitted: ProtocolBlockId,
        allocation_failed: ProtocolBlockId,
        capacity_failed: ProtocolBlockId,
        unavailable: ProtocolBlockId,
        parent_cancelled: ProtocolBlockId,
    },
    FinishAdmission(AdmissionOutcome),
    /// Completion-cell readiness is insufficient. Success establishes actual
    /// task termination and consumption of every group-owned runtime handle.
    WaitForAllTerminated {
        quiescent: ProtocolBlockId,
        fatal: ProtocolBlockId,
    },
    ContinueCleanup(ScopeExit),
    Abort,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub operations: Vec<Operation>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph {
    pub phase: Phase,
    pub entry: ProtocolBlockId,
    pub blocks: Vec<Block>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopeProtocol {
    pub scope: ScopeId,
    pub exit: ScopeExit,
    pub admission: Graph,
    pub drain: Graph,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackendRequirement {
    CancellationImmuneManagedGroupDrain,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ProtocolError(pub String);

impl fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ProtocolError {}

/// Compiles the lifecycle contract for an existing lexical scope. Source task
/// typing must still establish Task/Result, Send/TaskTransfer and scoped loans.
pub fn lower_scope(
    body: &Body,
    scope: ScopeId,
    exit: ScopeExit,
) -> Result<ScopeProtocol, ProtocolError> {
    let protocol = ScopeProtocol {
        scope,
        exit,
        admission: admission_graph(),
        drain: drain_graph(exit),
    };
    protocol.validate(body)?;
    Ok(protocol)
}

impl ScopeProtocol {
    pub fn validate(&self, body: &Body) -> Result<(), ProtocolError> {
        require(
            (self.scope.0 as usize) < body.scopes.len(),
            "task protocol references an absent lexical scope",
        )?;
        require(
            self.admission.phase == Phase::Admission && self.drain.phase == Phase::Drain,
            "task protocol phase mismatch",
        )?;
        self.admission.validate(self.exit)?;
        self.drain.validate(self.exit)
    }

    /// A structural protocol is not evidence that the pinned backend can run it.
    /// Do not substitute cancellable join, host drain, or a retry busy loop.
    pub fn pinned_runtime_requirement(&self) -> BackendRequirement {
        BackendRequirement::CancellationImmuneManagedGroupDrain
    }
}

fn admission_graph() -> Graph {
    let outcomes = [
        AdmissionOutcome::Failed(SpawnError::Allocation),
        AdmissionOutcome::Admitted,
        AdmissionOutcome::Failed(SpawnError::Allocation),
        AdmissionOutcome::Failed(SpawnError::Capacity),
        AdmissionOutcome::Failed(SpawnError::RuntimeUnavailable),
        AdmissionOutcome::ParentCancelled,
    ];
    let mut blocks = vec![
        Block {
            operations: Vec::new(),
            terminator: Terminator::PrepareRecord {
                ready: ProtocolBlockId(1),
                allocation_failed: ProtocolBlockId(2),
            },
        },
        Block {
            operations: Vec::new(),
            terminator: Terminator::PublishChild {
                admitted: ProtocolBlockId(3),
                allocation_failed: ProtocolBlockId(4),
                capacity_failed: ProtocolBlockId(5),
                unavailable: ProtocolBlockId(6),
                parent_cancelled: ProtocolBlockId(7),
            },
        },
    ];
    for (index, outcome) in outcomes.into_iter().enumerate() {
        let operations = match (index, outcome) {
            (_, AdmissionOutcome::Admitted) => Vec::new(),
            (0, _) => vec![Operation::DropPreparedCaptures],
            _ => vec![
                Operation::DropPreparedCaptures,
                Operation::ReleaseUnpublishedRecord,
            ],
        };
        blocks.push(Block {
            operations,
            terminator: Terminator::FinishAdmission(outcome),
        });
    }
    Graph {
        phase: Phase::Admission,
        entry: ProtocolBlockId(0),
        blocks,
    }
}

fn drain_graph(exit: ScopeExit) -> Graph {
    let mut operations = vec![Operation::SealAdmission];
    if exit.requests_cancellation() {
        operations.push(Operation::RequestChildCancellation);
    }
    Graph {
        phase: Phase::Drain,
        entry: ProtocolBlockId(0),
        blocks: vec![
            Block {
                operations,
                terminator: Terminator::WaitForAllTerminated {
                    quiescent: ProtocolBlockId(1),
                    fatal: ProtocolBlockId(2),
                },
            },
            Block {
                operations: vec![
                    Operation::ReclaimChildRecords,
                    Operation::DestroyEmptyGroup,
                    Operation::ReleaseScopeLoans,
                ],
                terminator: Terminator::ContinueCleanup(exit),
            },
            Block {
                operations: Vec::new(),
                terminator: Terminator::Abort,
            },
        ],
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CaptureOwner {
    Parent,
    Child,
    Released,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RecordOwner {
    Absent,
    Parent,
    Scope,
    Released,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AdmissionState {
    captures: CaptureOwner,
    record: RecordOwner,
    outcome: Option<AdmissionOutcome>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DrainState {
    Open,
    Sealed,
    CancellationRequested,
    Quiescent,
    RecordsReclaimed,
    GroupDestroyed,
    LoansReleased,
    Fatal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Admission(AdmissionState),
    Drain(DrainState),
}

impl Graph {
    fn validate(&self, exit: ScopeExit) -> Result<(), ProtocolError> {
        self.structure()?;
        let start = match self.phase {
            Phase::Admission => State::Admission(AdmissionState {
                captures: CaptureOwner::Parent,
                record: RecordOwner::Absent,
                outcome: None,
            }),
            Phase::Drain => State::Drain(DrainState::Open),
        };
        let mut inputs = vec![None; self.blocks.len()];
        inputs[self.entry.0 as usize] = Some(start);
        let mut pending = VecDeque::from([self.entry]);
        let mut steps = 0;
        while let Some(id) = pending.pop_front() {
            steps += 1;
            require(
                steps <= TRANSITION_LIMIT,
                "task protocol work limit exceeded",
            )?;
            let block = &self.blocks[id];
            let mut state = inputs[id.0 as usize].expect("queued protocol state");
            for &operation in &block.operations {
                state = operation.apply(state, exit)?;
            }
            for (target, state) in block.terminator.edges(state, exit)? {
                let input = &mut inputs[target.0 as usize];
                if let Some(previous) = input {
                    require(*previous == state, "incompatible task ownership at join")?;
                } else {
                    *input = Some(state);
                    pending.push_back(target);
                }
            }
        }
        require(
            inputs.iter().all(Option::is_some),
            "unreachable task protocol block",
        )
    }

    fn structure(&self) -> Result<(), ProtocolError> {
        require(
            !self.blocks.is_empty() && self.blocks.len() <= BLOCK_LIMIT,
            "invalid task protocol block count",
        )?;
        require(
            (self.entry.0 as usize) < self.blocks.len(),
            "invalid task protocol entry",
        )?;
        let mut incoming = vec![0usize; self.blocks.len()];
        for block in &self.blocks {
            require(
                block.operations.len() <= 16,
                "task protocol operation limit exceeded",
            )?;
            for target in block.terminator.targets() {
                let index = target.0 as usize;
                require(index < self.blocks.len(), "invalid task protocol successor")?;
                incoming[index] += 1;
            }
        }
        self.acyclic(incoming)
    }

    fn acyclic(&self, mut incoming: Vec<usize>) -> Result<(), ProtocolError> {
        let mut ready: VecDeque<_> = incoming
            .iter()
            .enumerate()
            .filter_map(|(index, &count)| (count == 0).then_some(index))
            .collect();
        let mut visited = 0;
        while let Some(index) = ready.pop_front() {
            visited += 1;
            for target in self.blocks[index].terminator.targets() {
                let count = &mut incoming[target.0 as usize];
                *count -= 1;
                if *count == 0 {
                    ready.push_back(target.0 as usize);
                }
            }
        }
        require(
            visited == self.blocks.len(),
            "task protocol contains a retry cycle",
        )
    }
}

impl Operation {
    fn apply(self, state: State, exit: ScopeExit) -> Result<State, ProtocolError> {
        match state {
            State::Admission(mut state) => {
                self.admission(&mut state)?;
                Ok(State::Admission(state))
            }
            State::Drain(state) => self.drain(state, exit).map(State::Drain),
        }
    }

    fn admission(self, state: &mut AdmissionState) -> Result<(), ProtocolError> {
        require(
            matches!(
                state.outcome,
                Some(AdmissionOutcome::Failed(_) | AdmissionOutcome::ParentCancelled)
            ),
            "admission cleanup requires a failed or cancelled publication",
        )?;
        match self {
            Self::DropPreparedCaptures => {
                require(
                    state.captures == CaptureOwner::Parent,
                    "capture dropped twice or after publication",
                )?;
                state.captures = CaptureOwner::Released;
            }
            Self::ReleaseUnpublishedRecord => {
                require(
                    state.record == RecordOwner::Parent && state.captures == CaptureOwner::Released,
                    "record released before capture cleanup or after publication",
                )?;
                state.record = RecordOwner::Released;
            }
            _ => return fail("drain operation in task admission"),
        }
        Ok(())
    }

    fn drain(self, state: DrainState, exit: ScopeExit) -> Result<DrainState, ProtocolError> {
        match (self, state) {
            (Self::SealAdmission, DrainState::Open) => Ok(DrainState::Sealed),
            (Self::RequestChildCancellation, DrainState::Sealed)
                if exit.requests_cancellation() =>
            {
                Ok(DrainState::CancellationRequested)
            }
            (Self::ReclaimChildRecords, DrainState::Quiescent) => Ok(DrainState::RecordsReclaimed),
            (Self::DestroyEmptyGroup, DrainState::RecordsReclaimed) => {
                Ok(DrainState::GroupDestroyed)
            }
            (Self::ReleaseScopeLoans, DrainState::GroupDestroyed) => Ok(DrainState::LoansReleased),
            _ => fail("invalid task drain order or premature lifetime release"),
        }
    }
}

impl Terminator {
    fn targets(&self) -> Vec<ProtocolBlockId> {
        match self {
            Self::Goto(target) => vec![*target],
            Self::PrepareRecord {
                ready,
                allocation_failed,
            } => vec![*ready, *allocation_failed],
            Self::PublishChild {
                admitted,
                allocation_failed,
                capacity_failed,
                unavailable,
                parent_cancelled,
            } => {
                vec![
                    *admitted,
                    *allocation_failed,
                    *capacity_failed,
                    *unavailable,
                    *parent_cancelled,
                ]
            }
            Self::WaitForAllTerminated { quiescent, fatal } => vec![*quiescent, *fatal],
            Self::FinishAdmission(_) | Self::ContinueCleanup(_) | Self::Abort => Vec::new(),
        }
    }

    fn edges(
        &self,
        state: State,
        exit: ScopeExit,
    ) -> Result<Vec<(ProtocolBlockId, State)>, ProtocolError> {
        if let Self::Goto(target) = self {
            return Ok(vec![(*target, state)]);
        }
        if matches!(self, Self::Abort) {
            return Ok(Vec::new());
        }
        match state {
            State::Admission(state) => self.admission_edges(state),
            State::Drain(state) => self.drain_edges(state, exit),
        }
    }

    fn admission_edges(
        &self,
        state: AdmissionState,
    ) -> Result<Vec<(ProtocolBlockId, State)>, ProtocolError> {
        match self {
            Self::PrepareRecord {
                ready,
                allocation_failed,
            } => prepare(state, *ready, *allocation_failed),
            Self::PublishChild {
                admitted,
                allocation_failed,
                capacity_failed,
                unavailable,
                parent_cancelled,
            } => publish(
                state,
                [
                    *admitted,
                    *allocation_failed,
                    *capacity_failed,
                    *unavailable,
                    *parent_cancelled,
                ],
            ),
            Self::FinishAdmission(outcome) => {
                finish_admission(state, *outcome)?;
                Ok(Vec::new())
            }
            _ => fail("drain terminator in task admission"),
        }
    }

    fn drain_edges(
        &self,
        state: DrainState,
        exit: ScopeExit,
    ) -> Result<Vec<(ProtocolBlockId, State)>, ProtocolError> {
        match self {
            Self::WaitForAllTerminated { quiescent, fatal } => {
                let expected = if exit.requests_cancellation() {
                    DrainState::CancellationRequested
                } else {
                    DrainState::Sealed
                };
                require(
                    state == expected,
                    "drain started before admission close or required cancellation",
                )?;
                Ok(vec![
                    (*quiescent, State::Drain(DrainState::Quiescent)),
                    (*fatal, State::Drain(DrainState::Fatal)),
                ])
            }
            Self::ContinueCleanup(saved) => {
                require(
                    state == DrainState::LoansReleased,
                    "parent cleanup resumed before task lifetime barrier",
                )?;
                require(*saved == exit, "task cleanup lost its saved exit reason")?;
                Ok(Vec::new())
            }
            _ => fail("admission terminator in task drain"),
        }
    }
}

fn prepare(
    state: AdmissionState,
    ready: ProtocolBlockId,
    failed: ProtocolBlockId,
) -> Result<Vec<(ProtocolBlockId, State)>, ProtocolError> {
    require(
        state.captures == CaptureOwner::Parent
            && state.record == RecordOwner::Absent
            && state.outcome.is_none(),
        "record preparation repeated or occurs after capture publication",
    )?;
    Ok(vec![
        (
            ready,
            State::Admission(AdmissionState {
                record: RecordOwner::Parent,
                ..state
            }),
        ),
        (
            failed,
            State::Admission(AdmissionState {
                outcome: Some(AdmissionOutcome::Failed(SpawnError::Allocation)),
                ..state
            }),
        ),
    ])
}

fn publish(
    state: AdmissionState,
    targets: [ProtocolBlockId; 5],
) -> Result<Vec<(ProtocolBlockId, State)>, ProtocolError> {
    require(
        state.captures == CaptureOwner::Parent
            && state.record == RecordOwner::Parent
            && state.outcome.is_none(),
        "publication requires an unpublished capture record",
    )?;
    let outcomes = [
        AdmissionOutcome::Admitted,
        AdmissionOutcome::Failed(SpawnError::Allocation),
        AdmissionOutcome::Failed(SpawnError::Capacity),
        AdmissionOutcome::Failed(SpawnError::RuntimeUnavailable),
        AdmissionOutcome::ParentCancelled,
    ];
    Ok(targets
        .into_iter()
        .zip(outcomes)
        .map(|(target, outcome)| {
            let mut branch = AdmissionState {
                outcome: Some(outcome),
                ..state
            };
            if outcome == AdmissionOutcome::Admitted {
                branch.captures = CaptureOwner::Child;
                branch.record = RecordOwner::Scope;
            }
            (target, State::Admission(branch))
        })
        .collect())
}

fn finish_admission(state: AdmissionState, outcome: AdmissionOutcome) -> Result<(), ProtocolError> {
    require(
        state.outcome == Some(outcome),
        "admission outcome was discarded or changed",
    )?;
    let ownership = if outcome == AdmissionOutcome::Admitted {
        state.captures == CaptureOwner::Child && state.record == RecordOwner::Scope
    } else {
        state.captures == CaptureOwner::Released
            && matches!(state.record, RecordOwner::Absent | RecordOwner::Released)
    };
    require(
        ownership,
        "admission leaves captures or records with the wrong owner",
    )
}

fn require(condition: bool, message: &str) -> Result<(), ProtocolError> {
    if condition { Ok(()) } else { fail(message) }
}

fn fail<T>(message: &str) -> Result<T, ProtocolError> {
    Err(ProtocolError(message.into()))
}
