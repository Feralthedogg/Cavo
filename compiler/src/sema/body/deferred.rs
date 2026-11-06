//! Deferred code captures places through references, never by executing its body
//! at registration. Hidden bindings let ordinary region/NLL machinery retain the
//! capture loans until every cleanup use has finished.

use super::*;
use std::collections::BTreeMap;

impl Body<'_, '_> {
    pub(super) fn deferred(&mut self, source: &ast::Block) -> S {
        if let Some(span) = forbidden_control(self.context.ast, source) {
            self.context.error(
                "E-DEFER-CONTROL",
                "deferred cleanup must be finite and cannot return, break, or continue",
                span,
            );
            return S::Error;
        }
        let before = self.states.clone();
        let outer = self.function.locals.len();
        let first_expression = self.function.expressions.len();
        let first_statement = self.function.statements.len();
        let (body, _) = self.block(source);
        self.restore(&before);
        let expression_end = self.function.expressions.len();
        let modes = self.capture_modes(outer, first_expression, first_statement);
        let captures = self.bind_captures(modes, source.span);
        self.rewrite_captures(first_expression..expression_end, &captures);
        S::Defer {
            captures: captures.into_values().collect(),
            body,
        }
    }

    fn capture_modes(
        &self,
        outer: usize,
        first_expression: usize,
        first_statement: usize,
    ) -> BTreeMap<u32, bool> {
        let mut modes = BTreeMap::new();
        for expression in &self.function.expressions[first_expression..] {
            if let H::Local(local) = expression.kind
                && (local.0 as usize) < outer
            {
                modes.entry(local.0).or_insert(false);
            }
        }
        for expression in &self.function.expressions[first_expression..] {
            match &expression.kind {
                H::Unary {
                    op: U::BorrowMut,
                    operand,
                } => self.exclusive_capture(*operand, &mut modes),
                H::Call {
                    arguments,
                    parameter_types,
                    ..
                } => {
                    for (&argument, &ty) in arguments.iter().zip(parameter_types) {
                        if matches!(self.type_kind(ty), Ty::Reference { mutable: true, .. }) {
                            self.exclusive_capture(argument, &mut modes);
                        }
                    }
                }
                _ => {}
            }
        }
        for statement in &self.function.statements[first_statement..] {
            if let S::Assign { target, .. } = statement.kind {
                self.exclusive_capture(target, &mut modes);
            }
        }
        modes
    }

    fn exclusive_capture(&self, mut expression: ExprId, modes: &mut BTreeMap<u32, bool>) {
        for _ in 0..256 {
            expression = match self.expr(expression).kind {
                H::Local(local) => {
                    if let Some(mutable) = modes.get_mut(&local.0) {
                        *mutable = true;
                    }
                    return;
                }
                H::Field { base, .. } | H::Index { base, .. } => base,
                H::Group(inner)
                | H::CoerceArrayToSlice(inner)
                | H::Unary { operand: inner, .. } => inner,
                _ => return,
            };
        }
    }

    fn bind_captures(
        &mut self,
        modes: BTreeMap<u32, bool>,
        span: Span,
    ) -> BTreeMap<u32, (LocalId, ExprId)> {
        let mut captures = BTreeMap::new();
        for (original, mutable) in modes {
            let original = LocalId(original);
            let binding = &self.function.locals[original.0 as usize];
            let (name, inner) = (binding.name, binding.ty);
            if mutable && !binding.mutable {
                self.context.error(
                    "E-DEFER-CAPTURE",
                    "deferred mutable access requires a mutable captured binding",
                    span,
                );
            }
            let region = self.context.program.types.fresh_region();
            let ty = self.context.program.types.intern(Ty::Reference {
                region,
                mutable,
                inner,
            });
            let operand = self.add_expr(H::Local(original), inner, span);
            let initializer = self.add_expr(
                H::Unary {
                    op: if mutable { U::BorrowMut } else { U::Borrow },
                    operand,
                },
                ty,
                span,
            );
            let local = LocalId(self.function.locals.len() as u32);
            self.function.locals.push(hir::Local {
                name,
                ty,
                mutable: false,
                span,
            });
            self.states.push(Init::Initialized);
            captures.insert(original.0, (local, initializer));
        }
        captures
    }

    fn rewrite_captures(
        &mut self,
        expressions: std::ops::Range<usize>,
        captures: &BTreeMap<u32, (LocalId, ExprId)>,
    ) {
        for index in expressions {
            let H::Local(original) = self.function.expressions[index].kind else {
                continue;
            };
            let Some(&(captured, _)) = captures.get(&original.0) else {
                continue;
            };
            let ty = self.function.locals[captured.0 as usize].ty;
            let span = self.function.expressions[index].span;
            let operand = self.add_expr(H::Local(captured), ty, span);
            self.function.expressions[index].kind = H::Unary {
                op: U::Dereference,
                operand,
            };
        }
    }
}

fn forbidden_control(ast: &ast::Ast, source: &ast::Block) -> Option<Span> {
    let mut pending = source.statements.clone();
    while let Some(id) = pending.pop() {
        let statement = ast.stmt(id);
        match &statement.kind {
            StmtKind::Return(_)
            | StmtKind::Break
            | StmtKind::Continue
            | StmtKind::While { .. }
            | StmtKind::For { .. }
            | StmtKind::ForIn { .. }
            | StmtKind::Scope { .. } => return Some(statement.span),
            StmtKind::Block(body) | StmtKind::Defer(body) => pending.extend(&body.statements),
            StmtKind::If {
                then_block,
                otherwise,
                ..
            } => {
                pending.extend(&then_block.statements);
                pending.extend(otherwise);
            }
            _ => {}
        }
    }
    None
}
