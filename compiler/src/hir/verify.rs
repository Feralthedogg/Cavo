use super::*;
use crate::types::Ty;
use std::fmt;
mod body;
mod program;
mod types;

#[derive(Debug, PartialEq, Eq)]
pub struct InvariantError(pub String);

impl fmt::Display for InvariantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for InvariantError {}

impl Program {
    /// Structural validation for frontend output and future pass boundaries.
    /// This does not prove borrow, effect, contract, or arithmetic equivalence.
    pub fn validate(&self) -> Result<(), InvariantError> {
        let types = self.types.values().len();
        types::validate(self)?;
        program::metadata(self)?;
        for function in &self.functions {
            self.validate_function(function, types)?;
        }
        crate::hir::traits::validate(self)?;
        self.validate_closures()?;
        self.constants
            .validate(self)
            .map_err(|error| InvariantError(error.to_string()))?;
        Ok(())
    }

    fn validate_function(&self, function: &Function, types: usize) -> Result<(), InvariantError> {
        body::function_header(self, function)?;
        require(
            self.definitions
                .get(function.definition.0 as usize)
                .is_some_and(|definition| definition.kind == DefinitionKind::Function),
            "function has an invalid definition ID",
        )?;
        require(
            (function.result.0 as usize) < types && function.result != TyId::ERROR,
            "function has an invalid result type",
        )?;
        body::locals_and_clauses(self, function)?;
        for expression in &function.expressions {
            require(
                expression.ty != TyId::ERROR && (expression.ty.0 as usize) < types,
                "expression has an invalid type",
            )?;
            require(
                self.types.valid_region_scope(expression.ty),
                "expression has an escaping bound region",
            )?;
            body::expression(self, function, expression)?;
        }
        body::statements(self, function)?;
        body_graph(function)
    }
}

fn body_graph(function: &Function) -> Result<(), InvariantError> {
    let expressions = function.expressions.len();
    let statements = function.statements.len();
    let total = expressions + statements;
    validate_graph(total, "body", |index, visitor| {
        if index < expressions {
            let kind = &function.expressions[index].kind;
            expr_children(kind, &mut |id| {
                visitor(if (id.0 as usize) < expressions {
                    id.0 as usize
                } else {
                    total
                })
            });
            body::expression_statements(kind, &mut |id| {
                visitor(if (id.0 as usize) < statements {
                    expressions + id.0 as usize
                } else {
                    total
                })
            });
        } else {
            let kind = &function.statements[index - expressions].kind;
            stmt_expressions(kind, &mut |id| {
                visitor(if (id.0 as usize) < expressions {
                    id.0 as usize
                } else {
                    total
                })
            });
            stmt_children(kind, &mut |id| {
                visitor(if (id.0 as usize) < statements {
                    expressions + id.0 as usize
                } else {
                    total
                })
            });
        }
    })
}

fn require(condition: bool, message: &str) -> Result<(), InvariantError> {
    if condition {
        Ok(())
    } else {
        Err(InvariantError(message.into()))
    }
}

fn expr_children(kind: &ExprKind, visit: &mut dyn FnMut(ExprId)) {
    match kind {
        ExprKind::Unary { operand, .. }
        | ExprKind::Group(operand)
        | ExprKind::Old(operand)
        | ExprKind::CoerceArrayToSlice(operand)
        | ExprKind::DynCoerce { value: operand, .. } => visit(*operand),
        ExprKind::Binary { left, right, .. } => {
            visit(*left);
            visit(*right);
        }
        ExprKind::Call {
            callee, arguments, ..
        } => {
            visit(*callee);
            for &argument in arguments {
                visit(argument);
            }
        }
        ExprKind::Field { base, .. }
        | ExprKind::IsVariant { base, .. }
        | ExprKind::VariantField { base, .. } => visit(*base),
        ExprKind::Index { base, index } => {
            visit(*base);
            visit(*index);
        }
        ExprKind::Array(values) => {
            for &value in values {
                visit(value);
            }
        }
        ExprKind::Repeat { value, .. } | ExprKind::RepeatConst { value, .. } => visit(*value),
        ExprKind::DynCall {
            receiver,
            arguments,
            ..
        } => {
            visit(*receiver);
            for &argument in arguments {
                visit(argument);
            }
        }
        ExprKind::Match { subject, arms, .. } => {
            visit(*subject);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    visit(guard);
                }
                visit(arm.value);
            }
        }
        ExprKind::BlockValue {
            value: Some(value), ..
        } => visit(*value),
        ExprKind::Record { fields, .. } => {
            for &(_, value) in fields {
                visit(value);
            }
        }
        _ => {}
    }
}

fn stmt_expressions(kind: &StmtKind, visit: &mut dyn FnMut(ExprId)) {
    match kind {
        StmtKind::Defer { captures, .. } => {
            for &(_, initializer) in captures {
                visit(initializer);
            }
        }
        StmtKind::Declare {
            initializer: Some(value),
            ..
        }
        | StmtKind::Return(Some(value))
        | StmtKind::Expression(value) => visit(*value),
        StmtKind::Assign { target, value, .. } => {
            visit(*target);
            visit(*value);
        }
        StmtKind::If { condition, .. } | StmtKind::While { condition, .. } => visit(*condition),
        StmtKind::For {
            condition: Some(condition),
            ..
        } => visit(*condition),
        StmtKind::ForIn { iterable, .. } => visit(*iterable),
        _ => {}
    }
}

fn stmt_children(kind: &StmtKind, visit: &mut dyn FnMut(StmtId)) {
    let mut block = |body: &Block| {
        for &statement in &body.statements {
            visit(statement);
        }
    };
    match kind {
        StmtKind::Block(body)
        | StmtKind::Defer { body, .. }
        | StmtKind::While { body, .. }
        | StmtKind::ForIn { body, .. } => block(body),
        StmtKind::If {
            then_block,
            otherwise,
            ..
        } => {
            block(then_block);
            if let Some(id) = otherwise {
                visit(*id);
            }
        }
        StmtKind::For {
            initialize,
            update,
            body,
            ..
        } => {
            block(body);
            if let Some(id) = initialize {
                visit(*id);
            }
            if let Some(id) = update {
                visit(*id);
            }
        }
        _ => {}
    }
}

fn validate_graph(
    count: usize,
    label: &str,
    mut visit: impl FnMut(usize, &mut dyn FnMut(usize)),
) -> Result<(), InvariantError> {
    let mut colors = vec![0_u8; count];
    let mut stack = Vec::new();
    for root in 0..count {
        if colors[root] != 0 {
            continue;
        }
        stack.push((root, false));
        while let Some((index, finish)) = stack.pop() {
            if finish {
                colors[index] = 2;
                continue;
            }
            if colors[index] == 2 {
                continue;
            }
            if colors[index] == 1 {
                return Err(InvariantError(format!("cyclic {label} graph")));
            }
            colors[index] = 1;
            stack.push((index, true));
            let mut invalid = false;
            visit(index, &mut |child| {
                if child >= count {
                    invalid = true;
                } else {
                    stack.push((child, false));
                }
            });
            if invalid {
                return Err(InvariantError(format!("invalid {label} child ID")));
            }
        }
    }
    Ok(())
}
