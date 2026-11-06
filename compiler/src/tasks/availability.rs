//! May-initialization for transfer checks. Moved whole values do not remain
//! live merely because an unconditional cleanup operation names their type.
use crate::mir::*;
use std::collections::VecDeque;

pub(super) fn compute(body: &Body) -> Result<Vec<Vec<Vec<bool>>>, String> {
    let points: usize = body.blocks.iter().map(|b| b.statements.len() + 1).sum();
    if points.saturating_mul(body.locals.len()) > 2_000_000 {
        return Err("task initialization budget exceeded".into());
    }
    let mut inputs = vec![None; body.blocks.len()];
    inputs[body.entry.0 as usize] = Some(vec![false; body.locals.len()]);
    let mut queue = VecDeque::from([body.entry.0 as usize]);
    let mut queued = vec![false; body.blocks.len()];
    queued[body.entry.0 as usize] = true;
    let mut budget = 2_000_000usize;
    while let Some(index) = queue.pop_front() {
        queued[index] = false;
        let block = &body.blocks[index];
        budget = budget
            .checked_sub(block.statements.len() + 1)
            .ok_or("task initialization work budget exceeded")?;
        let mut state = inputs[index].clone().expect("queued task block");
        for statement in &block.statements {
            transfer(&statement.kind, &mut state);
        }
        for (target, state) in edges(&block.terminator, state) {
            let index = target.0 as usize;
            let changed = if let Some(old) = &mut inputs[index] {
                let mut changed = false;
                for (left, right) in old.iter_mut().zip(state) {
                    changed |= !*left && right;
                    *left |= right;
                }
                changed
            } else {
                inputs[index] = Some(state);
                true
            };
            if changed && !queued[index] {
                queued[index] = true;
                queue.push_back(index);
            }
        }
    }
    Ok(body
        .blocks
        .iter()
        .zip(inputs)
        .map(|(block, input)| {
            let Some(mut state) = input else {
                return vec![vec![false; body.locals.len()]; block.statements.len() + 1];
            };
            let mut points = vec![state.clone()];
            for statement in &block.statements {
                transfer(&statement.kind, &mut state);
                points.push(state.clone());
            }
            points
        })
        .collect())
}

fn operand(value: &Operand, state: &mut [bool]) {
    if let Operand::Move(place) = value
        && place.projection.is_empty()
    {
        state[place.local.0 as usize] = false;
    }
}

fn value(value: &Rvalue, state: &mut [bool]) {
    match value {
        Rvalue::Use(value)
        | Rvalue::Unary { operand: value, .. }
        | Rvalue::Repeat { value, .. }
        | Rvalue::RepeatConst { value, .. }
        | Rvalue::ArrayToSlice(value)
        | Rvalue::DynCoerce { value, .. } => operand(value, state),
        Rvalue::Binary { left, right, .. } => {
            operand(left, state);
            operand(right, state);
        }
        Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
            for value in values {
                operand(value, state);
            }
        }
        Rvalue::Record { fields, .. } => {
            for (_, value) in fields {
                operand(value, state);
            }
        }
        _ => {}
    }
}

fn transfer(statement: &StatementKind, state: &mut [bool]) {
    match statement {
        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state[local.0 as usize] = false
        }
        StatementKind::Argument(local) | StatementKind::RegistryStart(local) => {
            state[local.0 as usize] = true
        }
        StatementKind::Assign {
            destination,
            value: source,
        } => {
            value(source, state);
            initialized(destination, state);
        }
        StatementKind::IteratorStart { iterator, value } => {
            operand(value, state);
            state[iterator.0 as usize] = true;
        }
        _ => {}
    }
}

fn initialized(destination: &Place, state: &mut [bool]) {
    if destination.projection.contains(&Projection::Deref) {
        // This compact may-analysis has no alias oracle. An indirect write may
        // initialize captured local storage; excluding it would skip Send checks.
        state.fill(true);
    } else {
        state[destination.local.0 as usize] = true;
    }
}

fn outcome<'a>(exit: &'a Terminator, state: &mut [bool]) -> Option<(&'a Place, BlockId)> {
    match exit {
        Terminator::Call {
            callee,
            arguments,
            destination,
            normal,
            ..
        }
        | Terminator::Spawn {
            callee,
            arguments,
            destination,
            normal,
            ..
        }
        | Terminator::DynCall {
            receiver: callee,
            arguments,
            destination,
            normal,
            ..
        } => {
            operand(callee, state);
            for arg in arguments {
                operand(arg, state);
            }
            Some((destination, *normal))
        }
        Terminator::Checked {
            value: source,
            destination,
            normal,
            ..
        } => {
            value(source, state);
            Some((destination, *normal))
        }
        Terminator::IteratorNext {
            destination, some, ..
        } => Some((destination, *some)),
        Terminator::Drop { place, .. } => {
            if place.projection.is_empty() {
                state[place.local.0 as usize] = false;
            }
            None
        }
        _ => None,
    }
}

fn edges(exit: &Terminator, mut state: Vec<bool>) -> Vec<(BlockId, Vec<bool>)> {
    let result = outcome(exit, &mut state);
    crate::mir::borrow::successors(exit)
        .into_iter()
        .map(|target| {
            let mut state = state.clone();
            if let Some((destination, normal)) = result
                && normal == target
            {
                initialized(destination, &mut state);
            }
            (target, state)
        })
        .collect()
}
