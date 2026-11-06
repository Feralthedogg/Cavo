//! Entry-relative memory transformers inferred from the execution CFG. Each
//! outcome has its own post-state: a cancelled call never initializes its out.

mod declarations;
pub(crate) mod drops;
mod external;
pub(crate) use declarations::footprint;
mod signature;

use super::*;
use crate::external::{AssumptionId, SummaryReport};
pub(super) use signature::children;
pub(crate) use signature::{Frame, Requirement, Storage};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Step {
    Field(u32),
    Variant(hir::DefId),
    Element,
    Deref,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Footprint {
    pub input: u32,
    pub path: Vec<Step>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Origin {
    Input(u32),
    Fresh(u32),
    Static,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Value {
    pub parameters: BTreeMap<Vec<Step>, BTreeSet<ParameterOrigin>>,
    pub fields: BTreeMap<Vec<Step>, BTreeSet<Origin>>,
    pub functions: BTreeSet<hir::DefId>,
    pub vtables: BTreeSet<u32>,
    pub unknown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ParameterOrigin {
    pub parameter: u32,
    pub path: Vec<Step>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FreshLoan {
    pub targets: Vec<Footprint>,
    pub parents: BTreeSet<Origin>,
    pub mutable: bool,
    pub unknown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Write {
    pub target: Footprint,
    pub value: Value,
    pub definite: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    pub returned: Value,
    pub writes: Vec<Write>,
    pub loans: Vec<FreshLoan>,
    pub unmodeled: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Access {
    pub target: Footprint,
    pub write: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummary {
    pub definition: hir::DefId,
    pub normal: Option<Outcome>,
    pub panic: Option<Outcome>,
    pub cancel: Option<Outcome>,
    pub accesses: BTreeSet<Access>,
    pub assumptions: BTreeSet<AssumptionId>,
    pub complete: bool,
    pub limited: bool,
}
impl FunctionSummary {
    fn bottom(definition: hir::DefId) -> Self {
        Self {
            definition,
            normal: None,
            panic: None,
            cancel: None,
            accesses: BTreeSet::new(),
            assumptions: BTreeSet::new(),
            complete: true,
            limited: false,
        }
    }
}

pub(super) struct Summaries {
    pub declared: Vec<Option<FunctionSummary>>,
    pub functions: Vec<Option<FunctionSummary>>,
    pub frames: Vec<Option<Frame>>,
    pub static_origin: bool,
}

pub(super) fn infer(
    mir: &Program,
    hir: &hir::Program,
    properties: &Properties,
    external: &[SummaryReport],
) -> Summaries {
    let mut summaries = initial(mir, hir, properties, external);
    let indices: BTreeMap<_, _> = mir
        .functions
        .iter()
        .enumerate()
        .map(|(i, body)| (body.definition, i))
        .collect();
    let calls = dependencies(mir, hir, properties, &indices);
    for component in crate::graph::components(&calls) {
        let recursive = component.len() > 1 || calls[component[0]].contains(&component[0]);
        infer_component(mir, hir, properties, &mut summaries, &component, recursive);
    }
    summaries
}

fn initial(
    mir: &Program,
    hir: &hir::Program,
    properties: &Properties,
    external: &[SummaryReport],
) -> Summaries {
    let mut frames = vec![None; hir.definitions.len()];
    for (index, definition) in hir.definitions.iter().enumerate() {
        if matches!(definition.kind, hir::DefinitionKind::Function) {
            frames[index] = Some(Frame::declaration(
                hir::DefId(index as u32),
                hir,
                properties,
            ));
        }
    }
    let mut functions = vec![None; hir.definitions.len()];
    let mut declared = vec![None; hir.definitions.len()];
    for (&definition, contract) in &hir.modular.functions {
        if crate::modular::usable(hir, definition)
            && let Some(frame) = &frames[definition.0 as usize]
        {
            declared[definition.0 as usize] =
                declarations::declared(definition, contract, frame, hir);
        }
    }
    for body in &mir.functions {
        functions[body.definition.0 as usize] = Some(FunctionSummary::bottom(body.definition));
    }
    for record in external {
        let index = record.function.0 as usize;
        if index < functions.len()
            && functions[index].is_none()
            && let Some(frame) = &frames[index]
        {
            functions[index] = external::adapt(record, frame, hir);
        }
    }
    let static_origin = mir
        .functions
        .iter()
        .any(|body| body.blocks.iter().any(static_block))
        || declared.iter().flatten().any(|s| {
            s.normal.as_ref().is_some_and(|out| {
                out.returned
                    .fields
                    .values()
                    .flatten()
                    .any(|origin| *origin == Origin::Static)
            })
        })
        || external
            .iter()
            .any(|record| record.returns.iter().any(|origin| origin == "static"));
    Summaries {
        declared,
        functions,
        frames,
        static_origin,
    }
}

fn static_operand(operand: &Operand) -> bool {
    matches!(
        operand,
        Operand::Constant {
            value: hir::Constant::String(_),
            ..
        }
    )
}
fn static_value(value: &Rvalue) -> bool {
    match value {
        Rvalue::Use(value)
        | Rvalue::Unary { operand: value, .. }
        | Rvalue::Repeat { value, .. }
        | Rvalue::ArrayToSlice(value) => static_operand(value),
        Rvalue::Binary { left, right, .. } => static_operand(left) || static_operand(right),
        Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
            values.iter().any(static_operand)
        }
        Rvalue::Record { fields, .. } => fields.iter().any(|(_, value)| static_operand(value)),
        _ => false,
    }
}
fn static_block(block: &Block) -> bool {
    block.statements.iter().any(|statement| matches!(&statement.kind, StatementKind::Assign { value, .. } if static_value(value)))
        || matches!(&block.terminator, Terminator::Call { arguments, .. } if arguments.iter().any(static_operand))
}

pub(crate) fn body_targets(body: &Body, hir: &hir::Program) -> BTreeSet<hir::DefId> {
    let mut targets = BTreeSet::new();
    for block in &body.blocks {
        for statement in &block.statements {
            if let StatementKind::Assign { value, .. } = &statement.kind {
                value_targets(value, &mut targets);
            }
        }
        match &block.terminator {
            Terminator::Call {
                callee, arguments, ..
            } => {
                operand_target(callee, &mut targets);
                for argument in arguments {
                    operand_target(argument, &mut targets);
                }
            }
            Terminator::DynCall {
                trait_method,
                arguments,
                ..
            } => {
                for table in &hir.vtables {
                    targets.extend(
                        table
                            .slots
                            .iter()
                            .filter(|slot| slot.declaration == *trait_method)
                            .map(|slot| slot.implementation),
                    );
                }
                for argument in arguments {
                    operand_target(argument, &mut targets);
                }
            }
            _ => {}
        }
    }
    targets
}

fn operand_target(operand: &Operand, targets: &mut BTreeSet<hir::DefId>) {
    if let Operand::Function { definition, .. } = operand {
        targets.insert(*definition);
    }
}
fn value_targets(value: &Rvalue, targets: &mut BTreeSet<hir::DefId>) {
    match value {
        Rvalue::Use(value)
        | Rvalue::Unary { operand: value, .. }
        | Rvalue::Repeat { value, .. }
        | Rvalue::RepeatConst { value, .. }
        | Rvalue::ArrayToSlice(value)
        | Rvalue::DynCoerce { value, .. } => operand_target(value, targets),
        Rvalue::Binary { left, right, .. } => {
            operand_target(left, targets);
            operand_target(right, targets);
        }
        Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
            for value in values {
                operand_target(value, targets);
            }
        }
        Rvalue::Record { fields, .. } => {
            for (_, value) in fields {
                operand_target(value, targets);
            }
        }
        _ => {}
    }
}

fn dependencies(
    mir: &Program,
    hir: &hir::Program,
    properties: &Properties,
    indices: &BTreeMap<hir::DefId, usize>,
) -> Vec<Vec<usize>> {
    mir.functions
        .iter()
        .map(|body| {
            let mut targets = body_targets(body, hir);
            targets.extend(drops::dependencies(body, hir, properties));
            targets
                .into_iter()
                .filter_map(|target| indices.get(&target).copied())
                .collect()
        })
        .collect()
}

fn infer_component(
    mir: &Program,
    hir: &hir::Program,
    properties: &Properties,
    summaries: &mut Summaries,
    component: &[usize],
    recursive: bool,
) {
    let mut remaining = 4096usize.saturating_mul(component.len().max(1));
    loop {
        let mut changed = false;
        for &index in component {
            if remaining == 0 {
                for &member in component {
                    summaries.functions[mir.functions[member].definition.0 as usize]
                        .as_mut()
                        .unwrap()
                        .complete = false;
                    summaries.functions[mir.functions[member].definition.0 as usize]
                        .as_mut()
                        .unwrap()
                        .limited = true;
                }
                return;
            }
            remaining -= 1;
            let body = &mir.functions[index];
            let next = infer_body(body, hir, properties, summaries);
            let slot = &mut summaries.functions[body.definition.0 as usize];
            changed |= slot.as_ref() != Some(&next);
            *slot = Some(next);
        }
        if !changed || !recursive {
            return;
        }
    }
}

fn infer_body(
    body: &Body,
    hir: &hir::Program,
    properties: &Properties,
    summaries: &Summaries,
) -> FunctionSummary {
    let mut loans = Vec::new();
    let sites = Sites::build(body, hir, properties, summaries, &mut loans);
    let context = Context {
        body,
        hir,
        properties,
        summaries,
        sites,
        loans: &loans,
    };
    let mut collector = Collector::new(body.definition);
    if !context.sites.complete {
        collector.summary.complete = false;
        collector.summary.limited = true;
        return collector.summary;
    }
    match live::Liveness::compute(body, properties)
        .and_then(|live| solve(&context, &live).map(|inputs| (live, inputs)))
    {
        Some((live, inputs)) => replay(&context, &live, &inputs, &mut collector),
        None => {
            collector.summary.complete = false;
            collector.summary.limited = true;
        }
    }
    collector.summary
}

struct Collector {
    summary: FunctionSummary,
    exits: [Option<flow::State>; 3],
}
impl Collector {
    fn new(definition: hir::DefId) -> Self {
        Self {
            summary: FunctionSummary::bottom(definition),
            exits: [None, None, None],
        }
    }
}
impl Reporter for Collector {
    fn finding(&mut self, _: Point, _: FindingKind, _: Option<LoanId>) {
        self.summary.complete = false;
    }
    fn gap(&mut self, _: Point, _: GapKind) {
        self.summary.complete = false;
    }
    fn assumption(&mut self, assumption: AssumptionId) {
        self.summary.assumptions.insert(assumption);
    }
    fn access(&mut self, access: Access) {
        if self.summary.accesses.len() >= 4096 || access.target.path.len() >= 128 {
            self.summary.complete = false;
            self.summary.limited = true;
        } else {
            self.summary.accesses.insert(access);
        }
    }
    fn exit(&mut self, reason: ExitKind, context: &Context<'_>, state: &flow::State) {
        let index = match reason {
            ExitKind::Normal => 0,
            ExitKind::Panic => 1,
            ExitKind::Cancel => 2,
        };
        match &mut self.exits[index] {
            Some(previous) => {
                previous.merge(state.clone());
            }
            slot => *slot = Some(state.clone()),
        }
        let captured = self.exits[index].as_ref().unwrap().capture(context);
        match captured {
            Some(value) => match reason {
                ExitKind::Normal => self.summary.normal = Some(value),
                ExitKind::Panic => self.summary.panic = Some(value),
                ExitKind::Cancel => self.summary.cancel = Some(value),
            },
            None => {
                self.summary.complete = false;
                self.summary.limited = true;
            }
        }
    }
}
