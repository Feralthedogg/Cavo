//! Source ownership spelling remains mandatory when execution MIR replaces the
//! older expression-atomic local CFG. This pass grants no loan/region proofs.

use crate::{
    diagnostic::{Diagnostic, report},
    hir::{self, ExprId, ExprKind as H, StmtId, StmtKind as S},
    local::properties::Properties,
    syntax::ast::UnaryOp,
    types::Ty,
};
use std::collections::HashSet;
mod copy_hint;
pub(crate) use copy_hint::suggest as suggest_copy;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Use {
    Value,
    Place,
    Move,
}
enum Work {
    Statement(StmtId),
    Expression(ExprId, Use),
}

pub(crate) fn validate(program: &mut hir::Program, diagnostics: &mut Vec<Diagnostic>) {
    let properties = Properties::compute(program);
    for function in &program.functions {
        Walker {
            program,
            function,
            properties: &properties,
            diagnostics,
            seen: HashSet::new(),
            pending: function
                .body
                .statements
                .iter()
                .copied()
                .map(Work::Statement)
                .collect(),
            remaining: 200_000,
        }
        .run();
    }
}

/// Structured expressions have early exits and arm-specific ownership commits;
/// the legacy expression-atomic CFG cannot represent their effects faithfully.
pub(crate) fn requires_execution_mir(program: &mut hir::Program) -> bool {
    if has_structured_forms(program) {
        return true;
    }
    let iterables: Vec<_> = program
        .functions
        .iter()
        .flat_map(|function| {
            function
                .statements
                .iter()
                .filter_map(|statement| match statement.kind {
                    S::ForIn { iterable, .. } => Some(function.expressions[iterable].ty),
                    _ => None,
                })
        })
        .collect();
    if iterables.is_empty() {
        return false;
    }
    let properties = Properties::compute(program);
    iterables.into_iter().any(|ty| !properties.get(ty).copy)
}

fn has_structured_forms(program: &hir::Program) -> bool {
    !program.modular.functions.is_empty()
        || program
            .definitions
            .iter()
            .any(|d| d.kind == hir::DefinitionKind::Union)
        || !program.tasks.scopes.is_empty()
        || !program.contracts.predicates.is_empty()
        || !program.contracts.intrinsics.is_empty()
        || program
            .contracts
            .signatures
            .values()
            .any(|function| !function.clauses.is_empty())
        || !program.implementations.is_empty()
        || !program.traits.is_empty()
        || !program.closures.is_empty()
        || program
            .types
            .values()
            .iter()
            .any(|ty| matches!(ty, Ty::Dynamic { .. } | Ty::SymbolicArray { .. }))
        || program.functions.iter().any(|function| {
            function
                .statements
                .iter()
                .any(|statement| matches!(statement.kind, S::Assume(_)))
                || (!function.clauses.is_empty()
                    && program.definitions[function.definition]
                        .const_origin
                        .is_some())
                || function.expressions.iter().any(|expression| {
                    if let H::Unary {
                        op: UnaryOp::Dereference,
                        operand,
                    } = expression.kind
                        && matches!(
                            program.types.get(function.expressions[operand].ty),
                            Ty::Pointer { .. }
                        )
                    {
                        return true;
                    }
                    matches!(
                        expression.kind,
                        H::Match { .. }
                            | H::BlockValue { .. }
                            | H::IsVariant { .. }
                            | H::VariantField { .. }
                            | H::DynCoerce { .. }
                            | H::DynCall { .. }
                            | H::ConstTerm(_)
                            | H::RepeatConst { .. }
                    )
                })
        })
}

struct Walker<'a> {
    program: &'a hir::Program,
    function: &'a hir::Function,
    properties: &'a Properties,
    diagnostics: &'a mut Vec<Diagnostic>,
    seen: HashSet<(ExprId, Use)>,
    pending: Vec<Work>,
    remaining: usize,
}

impl Walker<'_> {
    fn run(mut self) {
        while let Some(work) = self.pending.pop() {
            let Some(remaining) = self.remaining.checked_sub(1) else {
                report(
                    self.diagnostics,
                    Diagnostic::error(
                        "E-MOVE-LIMIT",
                        "source ownership checking exceeds its work limit",
                        self.function.body.span,
                    ),
                );
                break;
            };
            self.remaining = remaining;
            match work {
                Work::Statement(id) => self.statement(id),
                Work::Expression(id, mode) => self.expression(id, mode),
            }
        }
    }

    fn push(&mut self, value: ExprId, mode: Use) {
        self.pending.push(Work::Expression(value, mode));
    }
    fn block(&mut self, body: &hir::Block) {
        self.pending
            .extend(body.statements.iter().copied().map(Work::Statement));
    }

    fn statement(&mut self, id: StmtId) {
        let kind = &self.function.statements[id].kind;
        match kind {
            S::Declare {
                initializer: Some(value),
                ..
            }
            | S::Return(Some(value))
            | S::Expression(value) => self.push(*value, Use::Value),
            S::Assign { target, value, .. } => {
                self.push(*target, Use::Place);
                self.push(*value, Use::Value);
            }
            _ => self.control_statement(kind),
        }
    }

    fn control_statement(&mut self, kind: &S) {
        match kind {
            S::TaskScope { body, .. } => self.block(body),
            S::Assume(assumption) => self.push(assumption.predicate, Use::Place),
            S::Block(body) => self.block(body),
            S::Defer { captures, body } => {
                for (_, value) in captures {
                    self.push(*value, Use::Value);
                }
                self.block(body);
            }
            S::If {
                condition,
                then_block,
                otherwise,
            } => {
                self.push(*condition, Use::Value);
                self.block(then_block);
                self.pending
                    .extend(otherwise.iter().copied().map(Work::Statement));
            }
            S::While { condition, body } => {
                self.push(*condition, Use::Value);
                self.block(body);
            }
            S::For {
                initialize,
                condition,
                update,
                body,
            } => {
                self.pending.extend(
                    initialize
                        .iter()
                        .chain(update)
                        .copied()
                        .map(Work::Statement),
                );
                if let Some(condition) = condition {
                    self.push(*condition, Use::Value);
                }
                self.block(body);
            }
            S::ForIn { iterable, body, .. } => {
                self.push(*iterable, Use::Value);
                self.block(body);
            }
            S::Declare {
                initializer: None, ..
            }
            | S::Return(None)
            | S::Break
            | S::Continue
            | S::Empty
            | S::Error => {}
            S::Declare {
                initializer: Some(_),
                ..
            }
            | S::Return(Some(_))
            | S::Expression(_)
            | S::Assign { .. } => unreachable!("value statements handled before control traversal"),
        }
    }

    fn expression(&mut self, id: ExprId, mode: Use) {
        if !self.seen.insert((id, mode)) {
            return;
        }
        self.place_use(id, mode);
        let kind = &self.function.expressions[id].kind;
        if matches!(kind, H::Match { .. } | H::BlockValue { .. }) {
            self.control_expression(kind);
            return;
        }
        match kind {
            H::Spawn {
                callee, arguments, ..
            } => {
                self.push(*callee, Use::Value);
                for &argument in arguments {
                    self.push(argument, Use::Value);
                }
            }
            H::Unary {
                op: UnaryOp::Move,
                operand,
            } => self.push(*operand, Use::Move),
            H::Unary {
                op: UnaryOp::Borrow | UnaryOp::BorrowMut,
                operand,
            } => self.push(*operand, Use::Place),
            H::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => self.push(*operand, Use::Place),
            H::Unary { operand, .. }
            | H::CoerceArrayToSlice(operand)
            | H::Old(operand)
            | H::DynCoerce { value: operand, .. } => self.push(*operand, Use::Value),
            H::Group(value) => self.push(*value, mode),
            H::Field { base, .. } | H::VariantField { base, .. } | H::IsVariant { base, .. } => {
                self.push(*base, Use::Place)
            }
            H::Index { base, index } => {
                self.push(*base, Use::Place);
                self.push(*index, Use::Value);
            }
            H::Binary { left, right, .. } => {
                self.push(*left, Use::Value);
                self.push(*right, Use::Value);
            }
            H::Call { .. } | H::DynCall { .. } => self.call_expression(kind),
            H::Array(values) => {
                for &value in values {
                    self.push(value, Use::Value);
                }
            }
            H::Repeat { value, .. } | H::RepeatConst { value, .. } => self.push(*value, Use::Value),
            H::Record { fields, .. } => {
                for &(_, value) in fields {
                    self.push(value, Use::Value);
                }
            }
            H::Constant(_) | H::ConstTerm(_) | H::Local(_) | H::Definition(_) | H::Error => {}
            H::Match { .. } | H::BlockValue { .. } => {
                unreachable!("control expressions handled before value traversal")
            }
        }
    }

    fn control_expression(&mut self, kind: &H) {
        match kind {
            H::Match { subject, arms, .. } => {
                self.push(*subject, Use::Value);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    self.pending
                        .extend(arm.guard.map(|id| Work::Expression(id, Use::Value)));
                    self.push(arm.value, Use::Value);
                }
            }
            H::BlockValue { body, value } => {
                self.block(body);
                if let Some(value) = value {
                    self.push(*value, Use::Value);
                }
            }
            _ => unreachable!("only block and match expressions contain statements"),
        }
    }

    fn arguments(&mut self, arguments: &[ExprId], parameters: &[crate::types::TyId]) {
        for (&value, &formal) in arguments.iter().zip(parameters) {
            let actual = self.function.expressions[value].ty;
            let reborrow = matches!(
                self.program.types.get(actual),
                Ty::Reference { mutable: true, .. }
            ) && matches!(self.program.types.get(formal), Ty::Reference { .. });
            self.push(value, if reborrow { Use::Place } else { Use::Value });
        }
    }

    fn call_expression(&mut self, kind: &H) {
        match kind {
            H::Call {
                callee,
                arguments,
                parameter_types,
                ..
            } => {
                self.push(*callee, Use::Value);
                self.arguments(arguments, parameter_types);
            }
            H::DynCall {
                receiver,
                arguments,
                parameter_types,
                ..
            } => {
                self.push(*receiver, Use::Place);
                self.arguments(arguments, parameter_types);
            }
            _ => unreachable!("call traversal requires a call expression"),
        }
    }

    fn place_use(&mut self, id: ExprId, mode: Use) {
        let expression = &self.function.expressions[id];
        if self.properties.get(expression.ty).copy || mode == Use::Place || !self.is_lvalue(id) {
            return;
        }
        let problem = if mode == Use::Value {
            Some((
                "E-MOVE-EXPLICIT",
                "transferring a non-Copy place requires `move`",
            ))
        } else {
            self.invalid_move(id)
        };
        if let Some((code, message)) = problem {
            report(
                self.diagnostics,
                Diagnostic::error(code, message, expression.span),
            );
        }
    }

    fn is_lvalue(&self, mut id: ExprId) -> bool {
        for _ in 0..128 {
            id = match self.function.expressions[id].kind {
                H::Local(_)
                | H::Unary {
                    op: UnaryOp::Dereference,
                    ..
                } => return true,
                H::Group(value) => value,
                H::Field { base, .. } | H::VariantField { base, .. } | H::Index { base, .. } => {
                    base
                }
                _ => return false,
            };
        }
        false
    }

    fn pattern(&mut self, root: &hir::Pattern) {
        let mut pending = vec![(root, false)];
        while let Some((pattern, protected)) = pending.pop() {
            match &pattern.kind {
                hir::PatternKind::Variant { fields, .. } => {
                    let protected = protected || hir::traits::has_drop(self.program, pattern.ty);
                    pending.extend(fields.iter().map(|field| (field, protected)));
                }
                hir::PatternKind::Binding {
                    mode: hir::BindingMode::Move,
                    ..
                } if protected => report(
                    self.diagnostics,
                    Diagnostic::error(
                        "E-MOVE-DROP",
                        "cannot destructure non-Copy fields of a value with user Drop",
                        pattern.span,
                    ),
                ),
                _ => {}
            }
        }
    }

    fn invalid_move(&self, mut id: ExprId) -> Option<(&'static str, &'static str)> {
        for _ in 0..128 {
            id = match self.function.expressions[id].kind {
                H::Unary {
                    op: UnaryOp::Dereference,
                    ..
                } => {
                    return Some((
                        "E-MOVE-REFERENCE",
                        "cannot move a non-Copy value out of borrowed storage",
                    ));
                }
                H::Index { .. } => {
                    return Some((
                        "E-MOVE-INDEX",
                        "moving a non-Copy indexed value requires an ownership-aware iterator or replacement operation",
                    ));
                }
                H::Field { base, .. } | H::VariantField { base, .. } => {
                    let ty = self.function.expressions[base].ty;
                    if matches!(self.program.types.get(ty), Ty::Reference { .. }) {
                        return Some((
                            "E-MOVE-REFERENCE",
                            "cannot move a non-Copy field out of borrowed storage",
                        ));
                    }
                    if hir::traits::has_drop(self.program, ty) {
                        return Some((
                            "E-MOVE-DROP",
                            "cannot partially move a value with a user Drop implementation",
                        ));
                    }
                    base
                }
                H::Group(inner) => inner,
                _ => return None,
            };
        }
        Some((
            "E-MOVE-LIMIT",
            "move projection exceeds its analysis depth limit",
        ))
    }
}
