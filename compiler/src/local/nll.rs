use super::{
    Place, PlaceId,
    cfg::{BlockId, Exit, Graph, Operation},
    place::Places,
    properties::Properties,
};
use crate::{
    hir::{self, ExprId, ExprKind as H},
    syntax::ast::{BinaryOp, UnaryOp},
    types::Ty,
};
use std::collections::{HashSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Live(Vec<u64>);

impl Live {
    pub fn new(count: usize) -> Self {
        Self(vec![0; count.div_ceil(64)])
    }
    pub fn set(&mut self, index: usize) {
        self.0[index / 64] |= 1 << (index % 64);
    }
    fn clear(&mut self, index: usize) {
        self.0[index / 64] &= !(1 << (index % 64));
    }
    fn union(&mut self, other: &Self) {
        for (left, right) in self.0.iter_mut().zip(&other.0) {
            *left |= right;
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(word, &bits)| {
            let mut remaining = bits;
            std::iter::from_fn(move || {
                if remaining == 0 {
                    return None;
                }
                let bit = remaining.trailing_zeros() as usize;
                remaining &= remaining - 1;
                Some(word * 64 + bit)
            })
        })
    }
}

/// Converged intraprocedural liveness. These IDs are function-local analysis data.
#[derive(Debug)]
pub struct NllReport {
    pub leaves: Vec<PlaceId>,
    pub reachable: Vec<bool>,
    pub block_entry: Vec<Vec<PlaceId>>,
    pub block_exit: Vec<Vec<PlaceId>>,
}

impl NllReport {
    pub(super) fn validate(
        &self,
        graph: &Graph,
        places: &[Place],
    ) -> Result<(), hir::InvariantError> {
        let fail = || hir::InvariantError("invalid NLL liveness arena".into());
        if self.reachable.len() != graph.blocks.len()
            || self.block_entry.len() != graph.blocks.len()
            || self.block_exit.len() != graph.blocks.len()
        {
            return Err(fail());
        }
        let parents: HashSet<_> = places
            .iter()
            .filter_map(|p| p.projection.map(|p| p.base))
            .collect();
        let expected: HashSet<_> = (0..places.len())
            .map(|i| PlaceId(i as u32))
            .filter(|id| !parents.contains(id))
            .collect();
        let leaves: HashSet<_> = self.leaves.iter().copied().collect();
        if leaves != expected || leaves.len() != self.leaves.len() {
            return Err(fail());
        }
        for (index, (entry, exit)) in self.block_entry.iter().zip(&self.block_exit).enumerate() {
            if !self.reachable[index] && (!entry.is_empty() || !exit.is_empty()) {
                return Err(fail());
            }
            for live in [entry, exit] {
                let mut seen = HashSet::new();
                if live
                    .iter()
                    .any(|id| !leaves.contains(id) || !seen.insert(*id))
                {
                    return Err(fail());
                }
            }
        }
        Ok(())
    }
}

pub(super) struct Liveness {
    pub report: NllReport,
    expressions: Vec<Live>,
    before: Vec<Vec<Live>>,
    after: Vec<Vec<Live>>,
}

impl Liveness {
    pub fn expression(&self, id: ExprId) -> &Live {
        &self.expressions[id.0 as usize]
    }
    pub fn operation(&self, block: BlockId, operation: u32, after: bool) -> &Live {
        if after {
            &self.after[block.0 as usize][operation as usize]
        } else {
            &self.before[block.0 as usize][operation as usize]
        }
    }

    pub fn compute(
        function: &hir::Function,
        graph: &Graph,
        program: &hir::Program,
        places: &Places,
        properties: &Properties,
    ) -> Option<Self> {
        let count = places.leaf_count();
        let points = graph
            .blocks
            .iter()
            .map(|b| b.operations.len() + 1)
            .sum::<usize>();
        if (function.expressions.len() + points * 2).saturating_mul(count.max(1)) > 2_000_000 {
            return None;
        }
        let empty = Live::new(count);
        let mut reachable = vec![false; graph.blocks.len()];
        let mut predecessors = vec![Vec::new(); graph.blocks.len()];
        let mut work = vec![BlockId(0)];
        reachable[0] = true;
        while let Some(block) = work.pop() {
            for next in graph.successors(block, function) {
                predecessors[next.0 as usize].push(block);
                if !reachable[next.0 as usize] {
                    reachable[next.0 as usize] = true;
                    work.push(next);
                }
            }
        }
        let mut result = Self {
            report: NllReport {
                leaves: (0..count).map(|i| places.leaf(i)).collect(),
                reachable: reachable.clone(),
                block_entry: Vec::new(),
                block_exit: Vec::new(),
            },
            expressions: vec![empty.clone(); function.expressions.len()],
            before: graph
                .blocks
                .iter()
                .map(|b| vec![empty.clone(); b.operations.len() + 1])
                .collect(),
            after: graph
                .blocks
                .iter()
                .map(|b| vec![empty.clone(); b.operations.len() + 1])
                .collect(),
        };
        let mut incoming = vec![empty.clone(); graph.blocks.len()];
        let mut outgoing = incoming.clone();
        let mut queue: VecDeque<_> = (0..graph.blocks.len())
            .rev()
            .filter(|&i| reachable[i])
            .map(|i| BlockId(i as u32))
            .collect();
        let mut queued = reachable;
        let mut remaining = 2_000_000usize;
        while let Some(block) = queue.pop_front() {
            let index = block.0 as usize;
            queued[index] = false;
            let mut live = empty.clone();
            for next in graph.successors(block, function) {
                live.union(&incoming[next.0 as usize]);
            }
            outgoing[index] = live.clone();
            let mut walker = Walker {
                function,
                program,
                places,
                properties,
                result: &mut result,
                remaining: &mut remaining,
                depth: 0,
                expression_frames: 0,
            };
            let end = graph.blocks[index].operations.len();
            walker.result.after[index][end] = live.clone();
            if let Exit::Branch {
                condition: Some(condition),
                ..
            } = graph.blocks[index].exit
            {
                walker.expr(condition, &mut live)?;
            }
            walker.result.before[index][end] = live.clone();
            for (operation_index, operation) in
                graph.blocks[index].operations.iter().enumerate().rev()
            {
                walker.result.after[index][operation_index] = live.clone();
                walker.operation(operation, &mut live)?;
                walker.result.before[index][operation_index] = live.clone();
            }
            if live != incoming[index] {
                incoming[index] = live;
                for &previous in &predecessors[index] {
                    if !queued[previous.0 as usize] {
                        queued[previous.0 as usize] = true;
                        queue.push_back(previous);
                    }
                }
            }
        }
        let export = |sets: Vec<Live>| {
            sets.into_iter()
                .map(|s| s.iter().map(|i| places.leaf(i)).collect())
                .collect()
        };
        result.report.block_entry = export(incoming);
        result.report.block_exit = export(outgoing);
        Some(result)
    }
}

struct Walker<'a> {
    function: &'a hir::Function,
    program: &'a hir::Program,
    places: &'a Places,
    properties: &'a Properties,
    result: &'a mut Liveness,
    remaining: &'a mut usize,
    depth: usize,
    expression_frames: usize,
}

impl Walker<'_> {
    fn tick(&mut self) -> Option<()> {
        *self.remaining = self
            .remaining
            .checked_sub(self.places.leaf_count().div_ceil(64).max(1))?;
        Some(())
    }
    fn mark(&self, place: PlaceId, live: &mut Live) {
        for i in self.places.leaves(place) {
            live.set(i);
        }
    }
    fn kill(&self, place: PlaceId, live: &mut Live) {
        // Only an exact overwrite/storage end kills these leaves. An uncertain
        // index must not clear a sibling's future use or destructor obligation.
        for i in self.places.leaves(place) {
            live.clear(i);
        }
    }
    fn drop_use(&self, place: PlaceId, live: &mut Live) {
        for i in self.places.leaves(place) {
            let property = self.properties.get(self.places.ty(self.places.leaf(i)));
            if property.references && property.may_drop {
                live.set(i);
            }
        }
    }
    fn operation(&mut self, operation: &Operation, live: &mut Live) -> Option<()> {
        self.tick()?;
        match *operation {
            Operation::Parameter { local, .. } => self.kill(Places::root(local), live),
            Operation::Declare {
                local, initializer, ..
            } => {
                self.kill(Places::root(local), live);
                if let Some(value) = initializer {
                    self.expr(value, live)?;
                }
            }
            Operation::IterationStart { slot, value, .. } => {
                self.kill(Places::root(slot), live);
                self.expr(value, live)?;
            }
            Operation::IterationValue { slot, local, .. } => {
                self.kill(Places::root(local), live);
                self.mark(Places::root(slot), live);
            }
            Operation::EndStorage { local, .. } => {
                self.kill(Places::root(local), live);
                self.drop_use(Places::root(local), live);
            }
            Operation::Evaluate(value) => self.expr(value, live)?,
            Operation::Return { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, live)?;
                }
            }
            Operation::Assign {
                target,
                value,
                compound,
                ..
            } => {
                if let Some((place, true)) = self.places.direct(self.function, self.program, target)
                    && !compound
                {
                    self.kill(place, live);
                    self.drop_use(place, live);
                }
                self.expr(value, live)?;
                self.access(target, compound, live)?;
            }
        }
        Some(())
    }
    fn expr(&mut self, id: ExprId, live: &mut Live) -> Option<()> {
        self.tick()?;
        if self.depth >= 128 || self.expression_frames >= 256 {
            return None;
        }
        let nested = usize::from(!matches!(
            self.function.expressions[id.0 as usize].kind,
            H::Binary { .. }
        ));
        self.depth += nested;
        self.expression_frames += 1;
        let function = self.function;
        match &function.expressions[id.0 as usize].kind {
            H::Local(_)
            | H::Field { .. }
            | H::Index { .. }
            | H::Unary {
                op: UnaryOp::Dereference,
                ..
            } => self.access(id, true, live)?,
            H::Group(inner) | H::CoerceArrayToSlice(inner) | H::Old(inner) => {
                self.expr(*inner, live)?
            }
            H::Unary {
                op: UnaryOp::Borrow | UnaryOp::BorrowMut,
                operand,
            } => self.access(*operand, true, live)?,
            H::Unary { operand, .. } => self.expr(*operand, live)?,
            H::Binary { op, left, right } => {
                let condition = super::cfg::constant_bool(function, *left);
                let skip = matches!(
                    (op, condition),
                    (BinaryOp::And, Some(false)) | (BinaryOp::Or, Some(true))
                );
                if !skip {
                    let after = live.clone();
                    self.expr(*right, live)?;
                    if condition.is_none() && matches!(op, BinaryOp::And | BinaryOp::Or) {
                        live.union(&after);
                    }
                }
                self.expr(*left, live)?;
            }
            H::Call {
                callee, arguments, ..
            } => {
                for &arg in arguments.iter().rev() {
                    self.expr(arg, live)?;
                }
                self.expr(*callee, live)?;
            }
            H::Array(values) => {
                for &value in values.iter().rev() {
                    self.expr(value, live)?;
                }
            }
            H::Repeat { value, .. } => self.expr(*value, live)?,
            H::Record { fields, .. } => {
                for &(_, value) in fields.iter().rev() {
                    self.expr(value, live)?;
                }
            }
            H::Constant(_) | H::Definition(_) | H::Error => {}
            H::ConstTerm(_)
            | H::RepeatConst { .. }
            | H::Match { .. }
            | H::BlockValue { .. }
            | H::IsVariant { .. }
            | H::VariantField { .. }
            | H::DynCoerce { .. }
            | H::DynCall { .. } => return None,
        }
        self.result.expressions[id.0 as usize].union(live);
        self.depth -= nested;
        self.expression_frames -= 1;
        Some(())
    }
    fn access(&mut self, id: ExprId, read: bool, live: &mut Live) -> Option<()> {
        self.tick()?;
        if self.depth >= 128 {
            return None;
        }
        self.depth += 1;
        if read && let Some((place, _)) = self.places.direct(self.function, self.program, id) {
            self.mark(place, live);
        }
        let function = self.function;
        match function.expressions[id.0 as usize].kind {
            H::Group(inner) => self.access(inner, false, live)?,
            H::Field { base, .. } | H::Index { base, .. } => {
                if let H::Index { index, .. } = function.expressions[id.0 as usize].kind {
                    self.expr(index, live)?;
                }
                if matches!(
                    self.program
                        .types
                        .get(function.expressions[base.0 as usize].ty),
                    Ty::Reference { .. }
                ) || self.places.direct(function, self.program, base).is_none()
                {
                    self.expr(base, live)?;
                } else {
                    self.access(base, false, live)?;
                }
            }
            H::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => self.expr(operand, live)?,
            H::Local(_) => {}
            _ => self.expr(id, live)?,
        }
        self.depth -= 1;
        Some(())
    }
}
