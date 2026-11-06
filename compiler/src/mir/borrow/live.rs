use super::*;

pub(super) type Live = BTreeSet<usize>;
pub(super) struct Liveness {
    pub before: Vec<Vec<Live>>,
}

impl Liveness {
    pub fn compute(body: &Body, properties: &Properties) -> Option<Self> {
        let points = body.blocks.iter().try_fold(0usize, |count, block| {
            count.checked_add(block.statements.len() + 1)
        })?;
        if body.locals.len().checked_mul(points)? > STATE_LIMIT {
            return None;
        }
        let predecessors = predecessors(body);
        let mut inputs = vec![Live::new(); body.blocks.len()];
        let mut queue: VecDeque<_> = (0..body.blocks.len()).collect();
        let mut queued = vec![true; body.blocks.len()];
        let mut budget = WORK_LIMIT;
        while let Some(index) = queue.pop_front() {
            queued[index] = false;
            budget =
                budget.checked_sub(body.locals.len() + body.blocks[index].statements.len() + 1)?;
            let mut live = terminator(body, index, &inputs, properties);
            for statement in body.blocks[index].statements.iter().rev() {
                statement_before(&statement.kind, &mut live);
            }
            if live != inputs[index] {
                inputs[index] = live;
                enqueue(&predecessors[index], &mut queue, &mut queued);
            }
        }
        let before = body
            .blocks
            .iter()
            .enumerate()
            .map(|(index, block)| {
                let mut live = terminator(body, index, &inputs, properties);
                let mut points = vec![Live::new(); block.statements.len() + 1];
                points[block.statements.len()] = live.clone();
                for (index, statement) in block.statements.iter().enumerate().rev() {
                    statement_before(&statement.kind, &mut live);
                    points[index] = live.clone();
                }
                points
            })
            .collect();
        Some(Self { before })
    }
}

fn enqueue(predecessors: &[usize], queue: &mut VecDeque<usize>, queued: &mut [bool]) {
    for &predecessor in predecessors {
        if !queued[predecessor] {
            queued[predecessor] = true;
            queue.push_back(predecessor);
        }
    }
}

fn predecessors(body: &Body) -> Vec<Vec<usize>> {
    let mut incoming = vec![Vec::new(); body.blocks.len()];
    for (index, block) in body.blocks.iter().enumerate() {
        for successor in successors(&block.terminator) {
            incoming[successor.0 as usize].push(index);
        }
    }
    incoming
}

pub(super) fn successors(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(next) => vec![*next],
        Terminator::IteratorNext { some, none, .. } => vec![*some, *none],
        Terminator::Switch {
            condition:
                Operand::Constant {
                    value: hir::Constant::Bool(value),
                    ..
                },
            yes,
            no,
        } => vec![if *value { *yes } else { *no }],
        Terminator::Switch { yes, no, .. } => vec![*yes, *no],
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

fn terminator(body: &Body, index: usize, inputs: &[Live], properties: &Properties) -> Live {
    let exit = &body.blocks[index].terminator;
    let mut live = Live::new();
    for successor in successors(exit) {
        let mut edge = inputs[successor.0 as usize].clone();
        kill_result(exit, successor, &mut edge);
        live.extend(edge);
    }
    match exit {
        Terminator::Switch { condition, .. } => operand_uses(condition, &mut live),
        Terminator::IteratorNext {
            iterator,
            destination,
            ..
        } => {
            live.insert(iterator.0 as usize);
            address_uses(destination, &mut live);
        }
        Terminator::Call {
            callee,
            arguments,
            destination,
            ..
        }
        | Terminator::DynCall {
            receiver: callee,
            arguments,
            destination,
            ..
        } => {
            operand_uses(callee, &mut live);
            for argument in arguments {
                operand_uses(argument, &mut live);
            }
            address_uses(destination, &mut live);
        }
        Terminator::Checked {
            value, destination, ..
        } => {
            rvalue_uses(value, &mut live);
            address_uses(destination, &mut live);
        }
        Terminator::Bounds { base, index, .. } => {
            address_uses(base, &mut live);
            live.insert(index.0 as usize);
        }
        Terminator::Drop { place, .. } => {
            address_uses(place, &mut live);
            if properties.get(body.local(place.local).ty).may_drop {
                live.insert(place.local.0 as usize);
            }
        }
        Terminator::Return => {
            live.insert(body.return_local.0 as usize);
        }
        _ => {}
    }
    live
}

fn kill_result(exit: &Terminator, successor: BlockId, live: &mut Live) {
    match exit {
        Terminator::IteratorNext {
            destination,
            some: normal,
            ..
        }
        | Terminator::Call {
            destination,
            normal,
            ..
        }
        | Terminator::DynCall {
            destination,
            normal,
            ..
        }
        | Terminator::Checked {
            destination,
            normal,
            ..
        } if *normal == successor => kill(destination, live),
        _ => {}
    }
}

fn kill(place: &Place, live: &mut Live) {
    if place.projection.is_empty() {
        live.remove(&(place.local.0 as usize));
    }
}

fn statement_before(statement: &StatementKind, live: &mut Live) {
    match statement {
        StatementKind::StorageLive(local)
        | StatementKind::StorageDead(local)
        | StatementKind::Argument(local) => {
            live.remove(&(local.0 as usize));
        }
        StatementKind::IteratorStart { iterator, value } => {
            live.remove(&(iterator.0 as usize));
            operand_uses(value, live);
        }
        StatementKind::Assign { destination, value } => {
            kill(destination, live);
            address_uses(destination, live);
            rvalue_uses(value, live);
        }
        StatementKind::EnterScope(_) | StatementKind::ExitScope(_) => {}
    }
}

fn operand_uses(operand: &Operand, live: &mut Live) {
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        live.insert(place.local.0 as usize);
        address_uses(place, live);
    }
}

fn address_uses(place: &Place, live: &mut Live) {
    for projection in &place.projection {
        match projection {
            Projection::Deref => {
                live.insert(place.local.0 as usize);
            }
            Projection::Index(index) => {
                live.insert(index.0 as usize);
            }
            Projection::Field(_) | Projection::Downcast(_) => {}
        }
    }
}

fn rvalue_uses(value: &Rvalue, live: &mut Live) {
    match value {
        Rvalue::Use(value)
        | Rvalue::Unary { operand: value, .. }
        | Rvalue::Repeat { value, .. }
        | Rvalue::RepeatConst { value, .. }
        | Rvalue::DynCoerce { value, .. }
        | Rvalue::ArrayToSlice(value) => operand_uses(value, live),
        Rvalue::Binary { left, right, .. } => {
            operand_uses(left, live);
            operand_uses(right, live);
        }
        Rvalue::Borrow { place, .. } => {
            live.insert(place.local.0 as usize);
            address_uses(place, live);
        }
        Rvalue::AddressOf(place) | Rvalue::Length(place) | Rvalue::IsVariant { place, .. } => {
            address_uses(place, live)
        }
        Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
            for value in values {
                operand_uses(value, live);
            }
        }
        Rvalue::Record { fields, .. } => {
            for (_, value) in fields {
                operand_uses(value, live);
            }
        }
    }
}
