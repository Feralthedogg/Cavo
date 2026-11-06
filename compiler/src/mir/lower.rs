use super::*;
use crate::{
    hir::{ExprKind as H, StmtKind as S},
    local::properties::Properties,
    types::Ty,
};
use std::collections::HashMap;

mod contracts;
mod deferred;
mod dynamic;
mod logical;
mod task_scopes;

mod iteration;
mod owned_iteration;
mod patterns;

#[derive(Debug)]
pub struct LowerError {
    pub span: Span,
    pub message: String,
}
impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for LowerError {}

/// Lower only validated HIR. This does not promote the existing HIR borrow
/// report to a proof about the newly introduced abnormal execution paths.
pub fn lower(program: &mut hir::Program) -> Result<Program, LowerError> {
    if let Err(error) = program.validate() {
        return Err(LowerError {
            span: program
                .functions
                .first()
                .map_or(Span::new(crate::source::FileId(0), 0, 0), |f| f.body.span),
            message: format!("invalid input HIR: {error}"),
        });
    }
    // This API is also used directly by passes/tests, outside Compilation's
    // source checks. Abort successors alone cannot establish cleanup effects.
    let mut diagnostics = Vec::new();
    super::effects::validate_defers(program, &mut diagnostics);
    if let Some(error) = diagnostics.into_iter().next() {
        return Err(LowerError {
            span: error.primary,
            message: error.message,
        });
    }
    // Iteration counters are internal usize values even when source code never
    // names that primitive type.
    let usize_ty = program.types.intern(Ty::Integer {
        signed: false,
        bits: 0,
    });
    let properties = Properties::compute(program);
    let mut functions = Vec::with_capacity(program.functions.len());
    for function in &program.functions {
        functions.push(Builder::new(program, function, &properties, usize_ty).build()?);
    }
    Ok(Program { functions })
}

struct ActiveScope {
    id: ScopeId,
    registrations: Vec<Registration>,
    task: Option<(u32, LocalId)>,
}
#[derive(Clone, Copy)]
enum Registration {
    Local(LocalId),
    Defer(hir::StmtId),
}
#[derive(Clone, Copy)]
struct Loop {
    exit: BlockId,
    update: BlockId,
    depth: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Cleanup {
    TaskDrain(ScopeId, LocalId, super::tasks::ScopeExit),
    Drop(LocalId),
    Dead(LocalId),
    Exit(ScopeId),
    Defer(hir::StmtId),
}

struct Builder<'a> {
    program: &'a hir::Program,
    source: &'a hir::Function,
    properties: &'a Properties,
    usize_ty: TyId,
    body: Body,
    current: Option<BlockId>,
    scopes: Vec<ActiveScope>,
    loops: Vec<Loop>,
    sources: Vec<Option<LocalId>>,
    pattern_bindings: HashMap<hir::LocalId, Place>,
    cleanup: HashMap<(Cleanup, BlockId, ExitKind), BlockId>,
    scope_cleanup: HashMap<(ScopeId, BlockId, ExitKind), Vec<BlockId>>,
    returned: BlockId,
    panicked: BlockId,
    cancelled: BlockId,
    abort: BlockId,
    remaining: usize,
    depth: usize,
    cleanup_depth: usize,
    old_parameters: Vec<(hir::LocalId, LocalId)>,
    contract_calls: Vec<hir::DefId>,
}

impl<'a> Builder<'a> {
    fn new(
        program: &'a hir::Program,
        source: &'a hir::Function,
        properties: &'a Properties,
        usize_ty: TyId,
    ) -> Self {
        let span = source.body.span;
        let mut body = Body {
            definition: source.definition,
            result: source.result,
            locals: Vec::new(),
            scopes: vec![Scope { parent: None, span }],
            blocks: Vec::new(),
            entry: BlockId(0),
            return_local: LocalId(0),
        };
        for terminator in [
            Terminator::Unreachable,
            Terminator::Return,
            Terminator::Resume(ExitKind::Panic),
            Terminator::Resume(ExitKind::Cancel),
            Terminator::Abort,
        ] {
            body.blocks.push(Block {
                statements: Vec::new(),
                terminator,
                span,
                cleanup: None,
            });
        }
        Self {
            program,
            source,
            properties,
            usize_ty,
            body,
            current: Some(BlockId(0)),
            scopes: vec![ActiveScope {
                id: ScopeId(0),
                registrations: Vec::new(),
                task: None,
            }],
            loops: Vec::new(),
            sources: vec![None; source.locals.len()],
            pattern_bindings: HashMap::new(),
            cleanup: HashMap::new(),
            scope_cleanup: HashMap::new(),
            returned: BlockId(1),
            panicked: BlockId(2),
            cancelled: BlockId(3),
            abort: BlockId(4),
            remaining: 200_000,
            depth: 0,
            cleanup_depth: 0,
            old_parameters: Vec::new(),
            contract_calls: Vec::new(),
        }
    }

    fn build(mut self) -> Result<Body, LowerError> {
        let span = self.source.body.span;
        self.emit(StatementKind::EnterScope(ScopeId(0)), span);
        self.body.locals.push(Local {
            ty: self.source.result,
            kind: LocalKind::Return,
            scope: ScopeId(0),
            name: None,
            span,
        });
        self.emit(StatementKind::StorageLive(LocalId(0)), span);
        for &parameter in &self.source.parameters {
            let local = self.source_local(parameter, LocalKind::Parameter)?;
            self.emit(
                StatementKind::Argument(local),
                self.source.locals[parameter].span,
            );
        }
        self.prepare_contracts()?;
        for &statement in &self.source.body.statements {
            self.statement(statement)?;
        }
        if self.current.is_some() {
            if self.source.result == TyId::VOID {
                self.assign(
                    Place::local(self.body.return_local),
                    Rvalue::Use(Operand::Unit),
                    span,
                );
            }
            self.contract_guards(crate::syntax::ast::ClauseKind::Ensures)?;
            let target = self.cleanup_to(0, self.returned, ExitKind::Normal)?;
            self.terminate(Terminator::Goto(target));
        }
        Ok(self.body)
    }

    fn fail<T>(&self, span: Span, message: &str) -> Result<T, LowerError> {
        Err(LowerError {
            span,
            message: message.into(),
        })
    }
    fn charge(&mut self, span: Span) -> Result<(), LowerError> {
        if self.remaining == 0 {
            return self.fail(span, "MIR lowering exceeds its per-function work limit");
        }
        self.remaining -= 1;
        Ok(())
    }
    fn new_block(&mut self, span: Span, cleanup: Option<ExitKind>) -> Result<BlockId, LowerError> {
        self.charge(span)?;
        let id = BlockId(self.body.blocks.len() as u32);
        self.body.blocks.push(Block {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
            span,
            cleanup,
        });
        Ok(id)
    }
    fn emit(&mut self, kind: StatementKind, span: Span) {
        self.body.blocks[self.current.expect("reachable lowering block").0 as usize]
            .statements
            .push(Statement { kind, span });
    }
    fn terminate(&mut self, terminator: Terminator) {
        self.body.blocks[self.current.take().expect("unterminated lowering block").0 as usize]
            .terminator = terminator;
    }
    fn goto(&mut self, target: BlockId) {
        if self.current.is_some() {
            self.terminate(Terminator::Goto(target));
        }
    }
    fn assign(&mut self, destination: Place, value: Rvalue, span: Span) {
        self.emit(StatementKind::Assign { destination, value }, span);
    }
    fn local(
        &mut self,
        ty: TyId,
        kind: LocalKind,
        name: Option<Symbol>,
        span: Span,
    ) -> Result<LocalId, LowerError> {
        self.charge(span)?;
        let local = LocalId(self.body.locals.len() as u32);
        let scope = self.scopes.last_mut().expect("active lexical scope");
        scope.registrations.push(Registration::Local(local));
        self.body.locals.push(Local {
            ty,
            kind,
            scope: scope.id,
            name,
            span,
        });
        self.emit(StatementKind::StorageLive(local), span);
        Ok(local)
    }
    fn source_local(&mut self, id: hir::LocalId, kind: LocalKind) -> Result<LocalId, LowerError> {
        let source = &self.source.locals[id];
        let local = self.local(source.ty, kind, Some(source.name), source.span)?;
        self.sources[id.0 as usize] = Some(local);
        Ok(local)
    }
    fn enter(&mut self, span: Span) -> Result<(), LowerError> {
        self.charge(span)?;
        let id = ScopeId(self.body.scopes.len() as u32);
        self.body.scopes.push(Scope {
            parent: self.scopes.last().map(|s| s.id),
            span,
        });
        self.scopes.push(ActiveScope {
            id,
            registrations: Vec::new(),
            task: None,
        });
        self.emit(StatementKind::EnterScope(id), span);
        Ok(())
    }
    fn leave(&mut self, span: Span) -> Result<(), LowerError> {
        if self.current.is_some() {
            let next = self.new_block(span, None)?;
            let target = self.cleanup_to(self.scopes.len() - 1, next, ExitKind::Normal)?;
            self.terminate(Terminator::Goto(target));
            self.current = Some(next);
        }
        self.scopes.pop();
        Ok(())
    }

    /// Prefixes are persistent: registering another local adds a cleanup head.
    /// Calls reuse earlier tails without rescanning every preceding declaration.
    /// A snapshot contains only storage whose declaration has been reached.
    fn cleanup_to(
        &mut self,
        depth: usize,
        target: BlockId,
        reason: ExitKind,
    ) -> Result<BlockId, LowerError> {
        let exit = match reason {
            ExitKind::Normal => super::tasks::ScopeExit::Fallthrough,
            ExitKind::Panic => super::tasks::ScopeExit::Panic,
            ExitKind::Cancel => super::tasks::ScopeExit::Cancel,
        };
        self.cleanup_to_exit(depth, target, reason, exit)
    }

    fn cleanup_to_exit(
        &mut self,
        depth: usize,
        target: BlockId,
        reason: ExitKind,
        exit: super::tasks::ScopeExit,
    ) -> Result<BlockId, LowerError> {
        let mut next = target;
        for index in depth..self.scopes.len() {
            let scope = self.scopes[index].id;
            let count = self.scopes[index].registrations.len();
            let key = (scope, next, reason);
            let cached = self.scope_cleanup.get(&key);
            if let Some(&tail) = cached.and_then(|prefixes| prefixes.get(count)) {
                next = tail;
                if let Some((_, registry)) = self.scopes[index].task {
                    next = self.cleanup_action(
                        Cleanup::TaskDrain(scope, registry, exit),
                        next,
                        reason,
                    )?;
                }
                continue;
            }
            let mut prefixes = self.scope_cleanup.remove(&key).unwrap_or_default();
            if prefixes.is_empty() {
                prefixes.push(self.cleanup_action(Cleanup::Exit(scope), next, reason)?);
            }
            let start = prefixes.len() - 1;
            for local_index in start..count {
                let tail = *prefixes.last().expect("cleanup prefix");
                let registration = self.scopes[index].registrations[local_index];
                let head = self.cleanup_registration(registration, tail, reason)?;
                prefixes.push(head);
            }
            next = prefixes[count];
            if let Some((_, registry)) = self.scopes[index].task {
                next =
                    self.cleanup_action(Cleanup::TaskDrain(scope, registry, exit), next, reason)?;
            }
            self.scope_cleanup.insert(key, prefixes);
        }
        if reason != ExitKind::Normal {
            let dead = self.cleanup_action(Cleanup::Dead(self.body.return_local), next, reason)?;
            next = self.cleanup_action(Cleanup::Drop(self.body.return_local), dead, reason)?;
        }
        Ok(next)
    }
    fn cleanup_action(
        &mut self,
        action: Cleanup,
        next: BlockId,
        reason: ExitKind,
    ) -> Result<BlockId, LowerError> {
        // StorageDead clears trivial initialization state; values without glue
        // need no conditional Drop block or impossible destructor-failure edge.
        if let Cleanup::Drop(local) = action
            && !self.properties.get(self.body.local(local).ty).may_drop
        {
            return Ok(next);
        }
        if let Some(&block) = self.cleanup.get(&(action, next, reason)) {
            return Ok(block);
        }
        if let Cleanup::Defer(id) = action {
            let block = self.emit_deferred(id, next, reason)?;
            self.cleanup.insert((action, next, reason), block);
            return Ok(block);
        }
        let span = match action {
            Cleanup::Drop(l) | Cleanup::Dead(l) => self.body.local(l).span,
            Cleanup::Exit(s) | Cleanup::TaskDrain(s, _, _) => self.body.scopes[s.0 as usize].span,
            Cleanup::Defer(_) => unreachable!("handled above"),
        };
        let id = self.new_block(span, Some(reason))?;
        let block = &mut self.body.blocks[id];
        block.terminator = match action {
            Cleanup::TaskDrain(scope, registry, exit) => Terminator::TaskDrain {
                scope,
                registry,
                exit,
                next,
                abort: self.abort,
            },
            Cleanup::Drop(local) => Terminator::Drop {
                place: Place::local(local),
                next,
                unwind: self.abort,
            },
            Cleanup::Dead(local) => {
                block.statements.push(Statement {
                    kind: StatementKind::StorageDead(local),
                    span,
                });
                Terminator::Goto(next)
            }
            Cleanup::Exit(scope) => {
                block.statements.push(Statement {
                    kind: StatementKind::ExitScope(scope),
                    span,
                });
                Terminator::Goto(next)
            }
            Cleanup::Defer(_) => unreachable!("handled above"),
        };
        self.cleanup.insert((action, next, reason), id);
        Ok(id)
    }
    fn abnormal(&mut self, reason: ExitKind) -> Result<BlockId, LowerError> {
        if self.cleanup_depth != 0 {
            return Ok(self.abort);
        }
        let target = match reason {
            ExitKind::Panic => self.panicked,
            ExitKind::Cancel => self.cancelled,
            ExitKind::Normal => unreachable!(),
        };
        self.cleanup_to(0, target, reason)
    }
    fn block(&mut self, block: &hir::Block) -> Result<(), LowerError> {
        self.enter(block.span)?;
        for &statement in &block.statements {
            self.statement(statement)?;
        }
        self.leave(block.span)
    }
    fn statement(&mut self, id: hir::StmtId) -> Result<(), LowerError> {
        if self.current.is_none() {
            return Ok(());
        }
        let statement = &self.source.statements[id];
        let span = statement.span;
        self.charge(span)?;
        if self.depth >= 512 {
            return self.fail(span, "MIR lowering exceeds its nesting limit");
        }
        self.depth += 1;
        let result = self.statement_inner(id, &statement.kind, span);
        self.depth -= 1;
        result
    }
    fn statement_inner(
        &mut self,
        id: hir::StmtId,
        statement: &S,
        span: Span,
    ) -> Result<(), LowerError> {
        match statement {
            S::TaskScope { scope, body } => self.task_scope(*scope, body)?,
            S::Assume(assumption) => self.lower_assumption(assumption, span)?,
            S::Declare { local, initializer } => {
                // Registration precedes initialization: a failed initializer
                // cleans its temporaries, but never drops an uninitialized value.
                let local = self.source_local(*local, LocalKind::Source)?;
                if let Some(value) = initializer {
                    self.enter(span)?;
                    let value = self.eval(*value)?;
                    self.assign(Place::local(local), Rvalue::Use(value), span);
                    self.leave(span)?;
                }
            }
            S::Expression(value) => {
                self.enter(span)?;
                self.eval(*value)?;
                self.leave(span)?;
            }
            S::Assign { target, op, value } => {
                self.enter(span)?;
                let target_ty = self.source.expressions[target].ty;
                let place = self.place(*target)?;
                let destination = self.capture(place, target_ty, span)?;
                // Both the address and compound-assignment old value precede
                // RHS effects. Re-evaluating the source place here is unsound.
                let old = if op.is_some() {
                    Some(self.materialize(
                        target_ty,
                        Rvalue::Use(Operand::Copy(destination.clone())),
                        span,
                    )?)
                } else {
                    None
                };
                let value = self.eval(*value)?;
                let value = if let (Some(op), Some(left)) = (op, old) {
                    self.operation(
                        target_ty,
                        Rvalue::Binary {
                            op: *op,
                            left,
                            right: value,
                        },
                        span,
                    )?
                } else {
                    value
                };
                if self.properties.get(target_ty).may_drop {
                    let next = self.new_block(span, None)?;
                    self.terminate(Terminator::Drop {
                        place: destination.clone(),
                        next,
                        unwind: self.abort,
                    });
                    self.current = Some(next);
                }
                self.assign(destination, Rvalue::Use(value), span);
                self.leave(span)?;
            }
            S::Return(value) => {
                self.enter(span)?;
                let value = match value {
                    Some(value) => self.eval(*value)?,
                    None => Operand::Unit,
                };
                self.assign(
                    Place::local(self.body.return_local),
                    Rvalue::Use(value),
                    span,
                );
                self.contract_guards(crate::syntax::ast::ClauseKind::Ensures)?;
                let target = self.cleanup_to_exit(
                    0,
                    self.returned,
                    ExitKind::Normal,
                    super::tasks::ScopeExit::Return,
                )?;
                self.terminate(Terminator::Goto(target));
                self.scopes.pop();
            }
            S::Block(block) => self.block(block)?,
            S::Defer { captures, .. } => self.register_defer(id, captures, span)?,
            S::If {
                condition,
                then_block,
                otherwise,
            } => {
                let yes = self.new_block(span, None)?;
                let no = self.new_block(span, None)?;
                let next = self.new_block(span, None)?;
                self.condition(*condition, yes, no)?;
                self.current = Some(yes);
                self.block(then_block)?;
                self.goto(next);
                self.current = Some(no);
                if let Some(otherwise) = otherwise {
                    self.statement(*otherwise)?;
                }
                self.goto(next);
                self.current = Some(next);
            }
            S::While { condition, body } => {
                self.loop_statement(None, Some(*condition), None, body, span)?
            }
            S::For {
                initialize,
                condition,
                update,
                body,
            } => self.loop_statement(*initialize, *condition, *update, body, span)?,
            S::ForIn {
                local,
                iterable,
                body,
            } => self.for_in(*local, *iterable, body, span)?,
            S::Break | S::Continue => {
                let Some(loop_) = self.loops.last().copied() else {
                    return self.fail(span, "loop exit has no enclosing loop");
                };
                let (depth, target) = if matches!(statement, S::Break) {
                    (loop_.depth - 1, loop_.exit)
                } else {
                    (loop_.depth, loop_.update)
                };
                let exit = if matches!(statement, S::Break) {
                    super::tasks::ScopeExit::Break
                } else {
                    super::tasks::ScopeExit::Continue
                };
                let target = self.cleanup_to_exit(depth, target, ExitKind::Normal, exit)?;
                self.terminate(Terminator::Goto(target));
            }
            S::Empty => {}
            S::Error => return self.fail(span, "error statement cannot be lowered"),
        }
        Ok(())
    }
    fn loop_statement(
        &mut self,
        initialize: Option<hir::StmtId>,
        condition: Option<hir::ExprId>,
        update: Option<hir::StmtId>,
        body: &hir::Block,
        span: Span,
    ) -> Result<(), LowerError> {
        self.enter(span)?;
        if let Some(initialize) = initialize {
            self.statement(initialize)?;
        }
        let header = self.new_block(span, None)?;
        let entered = self.new_block(span, None)?;
        let updated = self.new_block(span, None)?;
        let exit = self.new_block(span, None)?;
        self.goto(header);
        self.current = Some(header);
        if let Some(condition) = condition {
            let stopped = self.cleanup_to(self.scopes.len() - 1, exit, ExitKind::Normal)?;
            self.condition(condition, entered, stopped)?;
        } else {
            self.terminate(Terminator::Goto(entered));
        }
        self.loops.push(Loop {
            exit,
            update: updated,
            depth: self.scopes.len(),
        });
        self.current = Some(entered);
        self.block(body)?;
        self.goto(updated);
        self.current = Some(updated);
        if let Some(update) = update {
            self.statement(update)?;
        }
        self.goto(header);
        self.loops.pop();
        self.scopes.pop();
        self.current = Some(exit);
        Ok(())
    }
    fn condition(
        &mut self,
        value: hir::ExprId,
        yes: BlockId,
        no: BlockId,
    ) -> Result<(), LowerError> {
        let span = self.source.expressions[value].span;
        self.enter(span)?;
        let condition = self.eval(value)?;
        let yes = self.cleanup_to(self.scopes.len() - 1, yes, ExitKind::Normal)?;
        let no = self.cleanup_to(self.scopes.len() - 1, no, ExitKind::Normal)?;
        self.terminate(Terminator::Switch { condition, yes, no });
        self.scopes.pop();
        Ok(())
    }

    fn take(&self, place: Place, ty: TyId) -> Operand {
        if self.properties.get(ty).copy {
            Operand::Copy(place)
        } else {
            Operand::Move(place)
        }
    }
    fn materialize(&mut self, ty: TyId, value: Rvalue, span: Span) -> Result<Operand, LowerError> {
        let local = self.local(ty, LocalKind::Temporary, None, span)?;
        self.assign(Place::local(local), value, span);
        Ok(self.take(Place::local(local), ty))
    }
    fn capture(&mut self, place: Place, ty: TyId, span: Span) -> Result<Place, LowerError> {
        let local = self.local(ty, LocalKind::Address, None, span)?;
        self.assign(Place::local(local), Rvalue::AddressOf(place), span);
        Ok(Place::local(local).project(Projection::Deref))
    }
    fn eval(&mut self, id: hir::ExprId) -> Result<Operand, LowerError> {
        let expression = &self.source.expressions[id];
        self.charge(expression.span)?;
        if self.depth >= 512 {
            return self.fail(expression.span, "MIR lowering exceeds its nesting limit");
        }
        self.depth += 1;
        let result = self.eval_inner(id);
        self.depth -= 1;
        result
    }
    fn eval_inner(&mut self, id: hir::ExprId) -> Result<Operand, LowerError> {
        let expression = &self.source.expressions[id];
        let ty = expression.ty;
        let span = expression.span;
        match &expression.kind {
            H::Spawn { .. } => self.spawn_expression(expression),
            H::Match {
                subject,
                temporary,
                arms,
            } => self.match_value(*subject, *temporary, arms, ty, span),
            H::BlockValue { body, value } => self.block_value(body, *value, ty, span),
            H::IsVariant { base, variant } => {
                let place = self.place(*base)?;
                self.materialize(
                    ty,
                    Rvalue::IsVariant {
                        place,
                        variant: *variant,
                    },
                    span,
                )
            }
            H::ConstTerm(value) => Ok(Operand::ConstTerm { value: *value, ty }),
            H::Constant(value) => Ok(Operand::Constant {
                value: value.clone(),
                ty,
            }),
            H::Definition(definition) => match self.program.definitions[definition].kind {
                hir::DefinitionKind::Function => Ok(Operand::Function {
                    definition: *definition,
                    ty,
                }),
                hir::DefinitionKind::Variant { .. }
                    if !matches!(
                        self.program.types.get(ty),
                        Ty::Function { .. } | Ty::ForAll { .. }
                    ) =>
                {
                    self.materialize(
                        ty,
                        Rvalue::Variant {
                            definition: *definition,
                            fields: Vec::new(),
                        },
                        span,
                    )
                }
                _ => self.fail(span, "MIR global value lowering is not implemented"),
            },
            H::Group(inner) => self.eval(*inner),
            H::Local(_)
            | H::Field { .. }
            | H::VariantField { .. }
            | H::Index { .. }
            | H::Unary {
                op: UnaryOp::Dereference,
                ..
            } => {
                let place = self.place(id)?;
                let operand = self.take(place, ty);
                self.materialize(ty, Rvalue::Use(operand), span)
            }
            H::Unary {
                op: UnaryOp::Move,
                operand,
            } => self.eval(*operand),
            H::Unary {
                op: UnaryOp::Borrow | UnaryOp::BorrowMut,
                operand,
            } => {
                let place = self.place(*operand)?;
                let mutable = matches!(
                    expression.kind,
                    H::Unary {
                        op: UnaryOp::BorrowMut,
                        ..
                    }
                );
                self.materialize(ty, Rvalue::Borrow { mutable, place }, span)
            }
            H::Unary { op, operand } => {
                let operand = self.eval(*operand)?;
                self.operation(ty, Rvalue::Unary { op: *op, operand }, span)
            }
            H::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                left,
                right,
            } => {
                let local = self.local(TyId::BOOL, LocalKind::Temporary, None, span)?;
                let left = self.eval(*left)?;
                let rhs = self.new_block(span, None)?;
                let short = self.new_block(span, None)?;
                let next = self.new_block(span, None)?;
                let and = matches!(
                    expression.kind,
                    H::Binary {
                        op: BinaryOp::And,
                        ..
                    }
                );
                let (yes, no) = if and { (rhs, short) } else { (short, rhs) };
                self.terminate(Terminator::Switch {
                    condition: left,
                    yes,
                    no,
                });
                self.current = Some(short);
                self.assign(
                    Place::local(local),
                    Rvalue::Use(Operand::Constant {
                        value: hir::Constant::Bool(!and),
                        ty: TyId::BOOL,
                    }),
                    span,
                );
                self.terminate(Terminator::Goto(next));
                self.current = Some(rhs);
                // RHS-only temporaries have their own dynamic lifetime, so the
                // short edge never cleans storage whose StorageLive was skipped.
                self.enter(span)?;
                let right = self.eval(*right)?;
                self.assign(Place::local(local), Rvalue::Use(right), span);
                self.leave(span)?;
                self.terminate(Terminator::Goto(next));
                self.current = Some(next);
                Ok(Operand::Copy(Place::local(local)))
            }
            H::Binary { op, left, right } => {
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                self.operation(
                    ty,
                    Rvalue::Binary {
                        op: *op,
                        left,
                        right,
                    },
                    span,
                )
            }
            H::Call {
                callee,
                type_arguments,
                arguments,
                parameter_types,
            } => self.call(
                *callee,
                type_arguments,
                arguments,
                parameter_types,
                ty,
                span,
            ),
            H::Array(elements) => {
                let values = elements
                    .iter()
                    .map(|&value| self.eval(value))
                    .collect::<Result<_, _>>()?;
                self.materialize(ty, Rvalue::Array(values), span)
            }
            H::RepeatConst { value, count } => {
                let value = self.eval(*value)?;
                self.materialize(
                    ty,
                    Rvalue::RepeatConst {
                        value,
                        count: *count,
                    },
                    span,
                )
            }
            H::Repeat { value, count } => {
                let value = self.eval(*value)?;
                self.materialize(
                    ty,
                    Rvalue::Repeat {
                        value,
                        count: *count,
                    },
                    span,
                )
            }
            H::Record { definition, fields } => {
                let mut values = Vec::with_capacity(fields.len());
                for &(field, value) in fields {
                    values.push((field, self.eval(value)?));
                }
                self.materialize(
                    ty,
                    Rvalue::Record {
                        definition: *definition,
                        fields: values,
                    },
                    span,
                )
            }
            H::CoerceArrayToSlice(value) => {
                let value = self.eval(*value)?;
                self.materialize(ty, Rvalue::ArrayToSlice(value), span)
            }
            H::DynCoerce { value, vtable } => self.dyn_coerce(*value, *vtable, ty, span),
            H::DynCall {
                receiver,
                trait_method,
                arguments,
                parameter_types,
            } => self.dyn_call(id, *receiver, *trait_method, arguments, parameter_types),
            H::Old(value) => self.old_expression(*value),
            H::Error => self.fail(span, "error expression cannot be lowered"),
        }
    }
    fn operation(&mut self, ty: TyId, value: Rvalue, span: Span) -> Result<Operand, LowerError> {
        let checked = match &value {
            Rvalue::Unary {
                op: UnaryOp::Negate,
                ..
            } => matches!(self.program.types.get(ty), Ty::Integer { .. }),
            Rvalue::Binary { op, .. } => {
                matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Subtract
                        | BinaryOp::Multiply
                        | BinaryOp::Divide
                        | BinaryOp::Remainder
                        | BinaryOp::ShiftLeft
                        | BinaryOp::ShiftRight
                ) && matches!(self.program.types.get(ty), Ty::Integer { .. })
            }
            _ => false,
        };
        if !checked {
            return self.materialize(ty, value, span);
        }
        let local = self.local(ty, LocalKind::Temporary, None, span)?;
        let normal = self.new_block(span, None)?;
        self.terminate(Terminator::Checked {
            value,
            destination: Place::local(local),
            normal,
            trap: self.abort,
        });
        self.current = Some(normal);
        Ok(self.take(Place::local(local), ty))
    }
    fn call(
        &mut self,
        callee: hir::ExprId,
        type_arguments: &[crate::types::GenericArg],
        arguments: &[hir::ExprId],
        parameter_types: &[TyId],
        ty: TyId,
        span: Span,
    ) -> Result<Operand, LowerError> {
        let mut resolved_callee = callee;
        while let H::Group(inner) = self.source.expressions[resolved_callee].kind {
            resolved_callee = inner;
        }
        let variant = match self.source.expressions[resolved_callee].kind {
            H::Definition(definition)
                if matches!(
                    self.program.definitions[definition].kind,
                    hir::DefinitionKind::Variant { .. }
                ) =>
            {
                Some(definition)
            }
            _ => None,
        };
        let function = if variant.is_some() {
            None
        } else {
            Some(self.eval(callee)?)
        };
        let values = self.call_arguments(arguments, parameter_types)?;
        if let Some(definition) = variant {
            return self.materialize(
                ty,
                Rvalue::Variant {
                    definition,
                    fields: values,
                },
                span,
            );
        }
        if let Some(Operand::Function { definition, .. }) = &function {
            self.call_contracts(*definition, &values, span)?;
        }
        let local = self.local(ty, LocalKind::Temporary, None, span)?;
        let normal = self.new_block(span, None)?;
        let panic = self.abnormal(ExitKind::Panic)?;
        let cancel = self.abnormal(ExitKind::Cancel)?;
        self.terminate(Terminator::Call {
            callee: function.expect("non-variant callee"),
            type_arguments: type_arguments.to_vec(),
            arguments: values,
            parameter_types: parameter_types.to_vec(),
            destination: Place::local(local),
            normal,
            panic,
            cancel,
        });
        self.current = Some(normal);
        Ok(self.take(Place::local(local), ty))
    }
    fn call_arguments(
        &mut self,
        arguments: &[hir::ExprId],
        parameter_types: &[TyId],
    ) -> Result<Vec<Operand>, LowerError> {
        arguments
            .iter()
            .zip(parameter_types)
            .map(|(&argument, &parameter)| self.call_argument(argument, parameter))
            .collect()
    }
    fn call_argument(
        &mut self,
        argument: hir::ExprId,
        parameter: TyId,
    ) -> Result<Operand, LowerError> {
        let expression = &self.source.expressions[argument];
        if let Ty::Reference { mutable, .. } = self.program.types.get(parameter)
            && matches!(
                self.program.types.get(expression.ty),
                Ty::Reference { mutable: true, .. }
            )
            && !matches!(
                expression.kind,
                H::Unary {
                    op: UnaryOp::Move | UnaryOp::BorrowMut,
                    ..
                }
            )
        {
            let place = self.place(argument)?.project(Projection::Deref);
            return self.materialize(
                parameter,
                Rvalue::Borrow {
                    mutable: *mutable,
                    place,
                },
                expression.span,
            );
        }
        self.eval(argument)
    }
    fn place(&mut self, id: hir::ExprId) -> Result<Place, LowerError> {
        let expression = &self.source.expressions[id];
        self.charge(expression.span)?;
        if self.depth >= 512 {
            return self.fail(
                expression.span,
                "MIR place lowering exceeds its nesting limit",
            );
        }
        self.depth += 1;
        let result = self.place_inner(id);
        self.depth -= 1;
        result
    }
    fn place_inner(&mut self, id: hir::ExprId) -> Result<Place, LowerError> {
        let expression = &self.source.expressions[id];
        match &expression.kind {
            H::Local(local) => self
                .pattern_bindings
                .get(local)
                .cloned()
                .or_else(|| self.sources[local.0 as usize].map(Place::local))
                .ok_or_else(|| LowerError {
                    span: expression.span,
                    message: "local is used before its MIR storage declaration".into(),
                }),
            H::Group(inner) => self.place(*inner),
            H::VariantField {
                base,
                variant,
                index,
            } => {
                let mut place = self.place(*base)?;
                if matches!(
                    self.program.types.get(self.source.expressions[base].ty),
                    Ty::Reference { .. }
                ) {
                    place = place.project(Projection::Deref);
                }
                Ok(place
                    .project(Projection::Downcast(*variant))
                    .project(Projection::Field(*index)))
            }
            H::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => Ok(self.place(*operand)?.project(Projection::Deref)),
            H::Field { base, index } => {
                let mut place = self.place(*base)?;
                if matches!(
                    self.program.types.get(self.source.expressions[base].ty),
                    Ty::Reference { .. }
                ) {
                    place = place.project(Projection::Deref);
                }
                Ok(place.project(Projection::Field(*index)))
            }
            H::Index { base, index } => {
                let mut place = self.place(*base)?;
                let mut ty = self.source.expressions[base].ty;
                if let Ty::Reference { inner, .. } = self.program.types.get(ty) {
                    ty = *inner;
                    place = place.project(Projection::Deref);
                }
                let base = self.capture(place, ty, expression.span)?;
                let value = self.eval(*index)?;
                let index_ty = self.source.expressions[index].ty;
                let index = self.local(index_ty, LocalKind::Temporary, None, expression.span)?;
                self.assign(Place::local(index), Rvalue::Use(value), expression.span);
                let normal = self.new_block(expression.span, None)?;
                self.terminate(Terminator::Bounds {
                    base: base.clone(),
                    index,
                    normal,
                    trap: self.abort,
                });
                self.current = Some(normal);
                Ok(base.project(Projection::Index(index)))
            }
            _ => {
                let value = self.eval(id)?;
                let local =
                    self.local(expression.ty, LocalKind::Temporary, None, expression.span)?;
                self.assign(Place::local(local), Rvalue::Use(value), expression.span);
                Ok(Place::local(local))
            }
        }
    }
}
