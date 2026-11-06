//! A local-analysis CFG, not the runtime/cleanup MIR or an optimization IR.

use super::{Event, EventId, EventKind};
use crate::{
    hir::{self, ExprId, LocalId, StmtKind},
    source::Span,
    syntax::ast::UnaryOp,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BlockId(pub u32);

#[derive(Clone, Debug)]
pub struct Graph {
    pub blocks: Vec<Block>,
    pub events: Vec<Event>,
    pub expression_events: Vec<Option<EventId>>,
    pub slots: usize,
}

#[derive(Clone, Debug, Default)]
pub struct Block {
    pub operations: Vec<Operation>,
    pub exit: Exit,
}

#[derive(Clone, Debug)]
pub enum Operation {
    Parameter {
        local: LocalId,
        event: EventId,
    },
    Declare {
        local: LocalId,
        initializer: Option<ExprId>,
        event: EventId,
    },
    Evaluate(ExprId),
    Assign {
        target: ExprId,
        value: ExprId,
        compound: bool,
        event: EventId,
    },
    EndStorage {
        local: LocalId,
        event: EventId,
    },
    Return {
        value: Option<ExprId>,
        span: Span,
    },
    IterationStart {
        slot: LocalId,
        value: ExprId,
        event: EventId,
    },
    IterationValue {
        slot: LocalId,
        local: LocalId,
        event: EventId,
    },
}

#[derive(Clone, Debug, Default)]
pub enum Exit {
    Goto(BlockId),
    Branch {
        condition: Option<ExprId>,
        yes: BlockId,
        no: BlockId,
    },
    Iterate {
        yes: BlockId,
        no: BlockId,
    },
    #[default]
    Stop,
}

struct Loop {
    stop: BlockId,
    next: BlockId,
    scope_depth: usize,
}

#[derive(Clone, Copy)]
enum Cleanup {
    Local(LocalId),
    Defer(hir::StmtId),
}

struct Builder<'a> {
    function: &'a hir::Function,
    graph: Graph,
    current: Option<BlockId>,
    scopes: Vec<Vec<Cleanup>>,
    loops: Vec<Loop>,
    limited: bool,
    operations: usize,
    depth: usize,
}

impl Graph {
    pub fn event(&self, id: EventId) -> &Event {
        &self.events[id.0 as usize]
    }
    pub(super) fn successors(&self, block: BlockId, function: &hir::Function) -> Vec<BlockId> {
        match self.blocks[block.0 as usize].exit {
            Exit::Goto(target) => vec![target],
            Exit::Branch { condition, yes, no } => {
                match condition.and_then(|id| constant_bool(function, id)) {
                    Some(true) => vec![yes],
                    Some(false) => vec![no],
                    None if condition.is_none() => vec![yes],
                    None => vec![yes, no],
                }
            }
            Exit::Iterate { yes, no } => vec![yes, no],
            Exit::Stop => Vec::new(),
        }
    }
    pub(super) fn lower(function: &hir::Function) -> Option<Self> {
        if function.locals.len() > 2048
            || function.statements.len() + function.expressions.len() > 40_000
        {
            return None;
        }
        let mut builder = Builder {
            function,
            graph: Self {
                blocks: vec![Block::default()],
                events: Vec::new(),
                expression_events: vec![None; function.expressions.len()],
                slots: function.locals.len(),
            },
            current: Some(BlockId(0)),
            scopes: vec![
                function
                    .parameters
                    .iter()
                    .copied()
                    .map(Cleanup::Local)
                    .collect(),
            ],
            loops: Vec::new(),
            limited: false,
            operations: 0,
            depth: 0,
        };
        for (index, expression) in function.expressions.iter().enumerate() {
            let kind = match expression.kind {
                hir::ExprKind::Local(_)
                | hir::ExprKind::Field { .. }
                | hir::ExprKind::Index { .. } => Some(EventKind::Read),
                hir::ExprKind::Unary {
                    op: UnaryOp::Move, ..
                } => Some(EventKind::Move),
                hir::ExprKind::Unary {
                    op: UnaryOp::Borrow,
                    ..
                } => Some(EventKind::BorrowShared),
                hir::ExprKind::Unary {
                    op: UnaryOp::BorrowMut,
                    ..
                } => Some(EventKind::BorrowExclusive),
                hir::ExprKind::Call { .. } => Some(EventKind::Call),
                _ => None,
            };
            if let Some(kind) = kind {
                let local = match expression.kind {
                    hir::ExprKind::Local(local) => Some(local),
                    _ => None,
                };
                let event = builder.event(kind, expression.span, local);
                builder.graph.expression_events[index] = Some(event);
            }
        }
        for &local in &function.parameters {
            let event = builder.event(
                EventKind::Parameter,
                function.locals[local.0 as usize].span,
                Some(local),
            );
            builder.emit(Operation::Parameter { local, event });
        }
        builder.block(&function.body);
        builder.end_scopes(0, function.body.span);
        if builder.limited
            || builder
                .graph
                .blocks
                .len()
                .saturating_mul(builder.graph.slots.max(1))
                > 250_000
        {
            return None;
        }
        Some(builder.graph)
    }
    pub(super) fn validate(&self, function: &hir::Function) -> Result<(), hir::InvariantError> {
        let fail = || hir::InvariantError("invalid local CFG reference".into());
        let local = |id: LocalId| (id.0 as usize) < function.locals.len();
        let slot = |id: LocalId| (id.0 as usize) < self.slots;
        let expression = |id: ExprId| (id.0 as usize) < function.expressions.len();
        let event = |id: EventId| (id.0 as usize) < self.events.len();
        for block in &self.blocks {
            let valid_exit = match block.exit {
                Exit::Goto(target) => (target.0 as usize) < self.blocks.len(),
                Exit::Branch { condition, yes, no } => {
                    condition.is_none_or(expression)
                        && (yes.0 as usize) < self.blocks.len()
                        && (no.0 as usize) < self.blocks.len()
                }
                Exit::Iterate { yes, no } => {
                    (yes.0 as usize) < self.blocks.len() && (no.0 as usize) < self.blocks.len()
                }
                Exit::Stop => true,
            };
            if !valid_exit {
                return Err(fail());
            }
            for operation in &block.operations {
                let valid = match *operation {
                    Operation::Parameter {
                        local: id,
                        event: source,
                    } => local(id) && event(source),
                    Operation::Declare {
                        local: id,
                        initializer,
                        event: source,
                    } => local(id) && initializer.is_none_or(expression) && event(source),
                    Operation::Evaluate(value) => expression(value),
                    Operation::Assign {
                        target,
                        value,
                        event: source,
                        ..
                    } => expression(target) && expression(value) && event(source),
                    Operation::EndStorage {
                        local: id,
                        event: source,
                    } => slot(id) && event(source),
                    Operation::Return { value, .. } => value.is_none_or(expression),
                    Operation::IterationStart {
                        slot: id,
                        value,
                        event: source,
                    } => slot(id) && expression(value) && event(source),
                    Operation::IterationValue {
                        slot: id,
                        local: value,
                        event: source,
                    } => slot(id) && local(value) && event(source),
                };
                if !valid {
                    return Err(fail());
                }
            }
        }
        Ok(())
    }
}

pub(super) fn constant_bool(function: &hir::Function, mut id: ExprId) -> Option<bool> {
    let mut invert = false;
    for _ in 0..128 {
        match function.expressions[id.0 as usize].kind {
            hir::ExprKind::Constant(hir::Constant::Bool(value)) => return Some(value != invert),
            hir::ExprKind::Group(inner) => id = inner,
            hir::ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                invert = !invert;
                id = operand;
            }
            _ => return None,
        }
    }
    None
}

impl Builder<'_> {
    fn event(&mut self, kind: EventKind, span: Span, local: Option<LocalId>) -> EventId {
        if self.graph.events.len() >= 65_536 {
            self.limited = true;
            return EventId(0);
        }
        let id = EventId(self.graph.events.len() as u32);
        self.graph.events.push(Event { kind, span, local });
        id
    }
    fn emit(&mut self, operation: Operation) {
        if self.limited {
            return;
        }
        if self.operations >= 65_536 {
            self.limited = true;
            return;
        }
        if let Some(current) = self.current {
            self.operations += 1;
            self.graph.blocks[current.0 as usize]
                .operations
                .push(operation);
        }
    }
    fn fresh(&mut self) -> BlockId {
        if self.graph.blocks.len() >= 8192 {
            self.limited = true;
            return BlockId(0);
        }
        let id = BlockId(self.graph.blocks.len() as u32);
        self.graph.blocks.push(Block::default());
        id
    }
    fn terminate(&mut self, exit: Exit) {
        if let Some(current) = self.current.take() {
            self.graph.blocks[current.0 as usize].exit = exit;
        }
    }
    fn end_scopes(&mut self, depth: usize, span: Span) {
        let actions: Vec<_> = self.scopes[depth..]
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev().copied())
            .collect();
        for action in actions {
            if self.limited {
                break;
            }
            let Cleanup::Local(local) = action else {
                if let Cleanup::Defer(id) = action
                    && let StmtKind::Defer { body, .. } =
                        &self.function.statements[id.0 as usize].kind
                {
                    self.block(body);
                }
                continue;
            };
            let end = Span::new(
                span.file,
                span.end.saturating_sub(1).max(span.start),
                span.end,
            );
            let event = self.event(EventKind::StorageEnd, end, Some(local));
            self.emit(Operation::EndStorage { local, event });
        }
    }
    fn block(&mut self, block: &hir::Block) {
        if self.depth >= 128 {
            self.limited = true;
            return;
        }
        self.depth += 1;
        self.scopes.push(Vec::new());
        for &statement in &block.statements {
            if self.current.is_none() || self.limited {
                break;
            }
            self.statement(statement);
        }
        self.end_scopes(self.scopes.len() - 1, block.span);
        self.scopes.pop();
        self.depth -= 1;
    }
    fn statement(&mut self, id: hir::StmtId) {
        if self.depth >= 128 {
            self.limited = true;
            return;
        }
        self.depth += 1;
        self.statement_inner(id);
        self.depth -= 1;
    }
    fn register_defer(&mut self, id: hir::StmtId, captures: &[(LocalId, ExprId)], span: Span) {
        for &(local, initializer) in captures {
            self.scopes
                .last_mut()
                .expect("defer scope")
                .push(Cleanup::Local(local));
            let event = self.event(EventKind::Initialize, span, Some(local));
            self.emit(Operation::Declare {
                local,
                initializer: Some(initializer),
                event,
            });
        }
        self.scopes
            .last_mut()
            .expect("defer scope")
            .push(Cleanup::Defer(id));
    }
    fn statement_inner(&mut self, id: hir::StmtId) {
        let function = self.function;
        let statement = &function.statements[id.0 as usize];
        match &statement.kind {
            StmtKind::Declare { local, initializer } => {
                self.scopes
                    .last_mut()
                    .expect("lexical scope")
                    .push(Cleanup::Local(*local));
                let event = self.event(
                    if initializer.is_some() {
                        EventKind::Initialize
                    } else {
                        EventKind::Declare
                    },
                    statement.span,
                    Some(*local),
                );
                self.emit(Operation::Declare {
                    local: *local,
                    initializer: *initializer,
                    event,
                });
            }
            StmtKind::Expression(value) => self.emit(Operation::Evaluate(*value)),
            StmtKind::Assign { target, op, value } => {
                let event = self.event(EventKind::Initialize, statement.span, None);
                self.emit(Operation::Assign {
                    target: *target,
                    value: *value,
                    compound: op.is_some(),
                    event,
                });
            }
            StmtKind::Return(value) => {
                self.emit(Operation::Return {
                    value: *value,
                    span: statement.span,
                });
                self.end_scopes(0, statement.span);
                self.terminate(Exit::Stop);
            }
            StmtKind::Block(block) => self.block(block),
            StmtKind::Defer { captures, .. } => self.register_defer(id, captures, statement.span),
            StmtKind::If {
                condition,
                then_block,
                otherwise,
            } => {
                let yes = self.fresh();
                let no = self.fresh();
                let join = self.fresh();
                self.terminate(Exit::Branch {
                    condition: Some(*condition),
                    yes,
                    no,
                });
                self.current = Some(yes);
                self.block(then_block);
                self.terminate(Exit::Goto(join));
                self.current = Some(no);
                if let Some(otherwise) = otherwise {
                    self.statement(*otherwise);
                }
                self.terminate(Exit::Goto(join));
                self.current = Some(join);
            }
            StmtKind::While { condition, body } => {
                self.loop_body(None, Some(*condition), None, body, statement.span);
            }
            StmtKind::For {
                initialize,
                condition,
                update,
                body,
            } => {
                self.scopes.push(Vec::new());
                if let Some(initialize) = initialize {
                    self.statement(*initialize);
                }
                self.loop_body(None, *condition, *update, body, statement.span);
                self.end_scopes(self.scopes.len() - 1, statement.span);
                self.scopes.pop();
            }
            StmtKind::ForIn {
                local,
                iterable,
                body,
            } => {
                self.scopes.push(Vec::new());
                let slot = LocalId(self.graph.slots as u32);
                self.graph.slots += 1;
                self.scopes
                    .last_mut()
                    .expect("iterator scope")
                    .push(Cleanup::Local(slot));
                let event = self.event(EventKind::Initialize, statement.span, Some(slot));
                self.emit(Operation::IterationStart {
                    slot,
                    value: *iterable,
                    event,
                });
                self.loop_body(Some((slot, *local)), None, None, body, statement.span);
                self.end_scopes(self.scopes.len() - 1, statement.span);
                self.scopes.pop();
            }
            StmtKind::Break | StmtKind::Continue => {
                let control = self
                    .loops
                    .last()
                    .expect("type checker validates loop exits");
                let target = if matches!(statement.kind, StmtKind::Break) {
                    control.stop
                } else {
                    control.next
                };
                let depth = control.scope_depth;
                self.end_scopes(depth, statement.span);
                self.terminate(Exit::Goto(target));
            }
            StmtKind::Empty => {}
            StmtKind::Error => unreachable!("validated typed HIR"),
        }
    }
    fn loop_body(
        &mut self,
        iteration: Option<(LocalId, LocalId)>,
        condition: Option<ExprId>,
        update: Option<hir::StmtId>,
        body: &hir::Block,
        span: Span,
    ) {
        let header = self.fresh();
        let start = self.fresh();
        let next = self.fresh();
        let stop = self.fresh();
        self.terminate(Exit::Goto(header));
        self.current = Some(header);
        self.terminate(if iteration.is_some() {
            Exit::Iterate {
                yes: start,
                no: stop,
            }
        } else {
            Exit::Branch {
                condition,
                yes: start,
                no: stop,
            }
        });
        self.loops.push(Loop {
            stop,
            next,
            scope_depth: self.scopes.len(),
        });
        self.current = Some(start);
        if let Some((slot, local)) = iteration {
            self.scopes.push(vec![Cleanup::Local(local)]);
            let event = self.event(EventKind::Initialize, span, Some(local));
            self.emit(Operation::IterationValue { slot, local, event });
        }
        self.block(body);
        if iteration.is_some() {
            self.end_scopes(self.scopes.len() - 1, span);
            self.scopes.pop();
        }
        self.terminate(Exit::Goto(next));
        self.current = Some(next);
        if let Some(update) = update {
            self.statement(update);
        }
        self.terminate(Exit::Goto(header));
        self.loops.pop();
        self.current = Some(stop);
    }
}
