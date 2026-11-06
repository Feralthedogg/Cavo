use super::*;
use crate::hir::{ExprId, ExprKind as H, Function};
use crate::syntax::ast::ClauseKind;

impl Context<'_> {
    pub(in crate::sema) fn validate_trait_contracts(&mut self) {
        let mut failures = Vec::new();
        for implementation in &self.program.implementations {
            for method in &implementation.methods {
                let Some(declaration) = method.declaration else {
                    continue;
                };
                if method.implementation == declaration {
                    continue;
                }
                let Some(inherited) = self.program.contracts.signatures.get(&declaration) else {
                    if !self.definition(declaration).declaration_clauses.is_empty() {
                        failures.push(self.definition(method.implementation).span);
                    }
                    continue;
                };
                let Some(own) = self
                    .program
                    .contracts
                    .signatures
                    .get(&method.implementation)
                else {
                    if !inherited.clauses.is_empty()
                        || !self
                            .definition(method.implementation)
                            .declaration_clauses
                            .is_empty()
                    {
                        failures.push(self.definition(method.implementation).span);
                    }
                    continue;
                };
                let mut remaining = 16_384;
                if !clauses_refine(own, inherited, &mut remaining) {
                    failures.push(self.definition(method.implementation).span);
                }
            }
        }
        for span in failures {
            self.error(
                "E-CONTRACT-REFINE",
                concat!("cannot establish trait-contract refinement: ",
                    "implementation preconditions must not be stronger and inherited postconditions must be retained"),
                span,
            );
        }
    }
}

fn clauses_refine(own: &Function, inherited: &Function, remaining: &mut usize) -> bool {
    own.clauses
        .iter()
        .filter(|clause| clause.kind == ClauseKind::Requires)
        .all(|clause| {
            inherited
                .clauses
                .iter()
                .filter(|other| other.kind == ClauseKind::Requires)
                .any(|other| {
                    equivalent(own, clause.predicate, inherited, other.predicate, remaining)
                })
        })
        && inherited
            .clauses
            .iter()
            .filter(|clause| clause.kind == ClauseKind::Ensures)
            .all(|clause| {
                own.clauses
                    .iter()
                    .filter(|other| other.kind == ClauseKind::Ensures)
                    .any(|other| {
                        equivalent(inherited, clause.predicate, own, other.predicate, remaining)
                    })
            })
}

fn binding(function: &Function, local: hir::LocalId) -> Option<usize> {
    function
        .parameters
        .iter()
        .position(|&parameter| parameter == local)
        .or_else(|| {
            function
                .clauses
                .iter()
                .any(|clause| clause.result_local == Some(local))
                .then_some(usize::MAX)
        })
}

fn equivalent(
    left: &Function,
    a: ExprId,
    right: &Function,
    b: ExprId,
    remaining: &mut usize,
) -> bool {
    let mut pending = vec![(a, b)];
    while let Some((a, b)) = pending.pop() {
        let Some(rest) = remaining.checked_sub(1) else {
            return false;
        };
        *remaining = rest;
        match (&left.expressions[a].kind, &right.expressions[b].kind) {
            (H::Group(inner), _) => pending.push((*inner, b)),
            (_, H::Group(inner)) => pending.push((a, *inner)),
            (H::Local(a), H::Local(b))
                if binding(left, *a).is_some() && binding(left, *a) == binding(right, *b) => {}
            (H::Definition(a), H::Definition(b)) if a == b => {}
            (H::Constant(a), H::Constant(b)) if same_constant(a, b) => {}
            (H::ConstTerm(a), H::ConstTerm(b)) if a == b => {}
            (H::Old(a), H::Old(b)) => pending.push((*a, *b)),
            (H::Unary { op: a, operand: x }, H::Unary { op: b, operand: y }) if a == b => {
                pending.push((*x, *y))
            }
            (
                H::Binary {
                    op: a,
                    left: ax,
                    right: ay,
                },
                H::Binary {
                    op: b,
                    left: bx,
                    right: by,
                },
            ) if a == b => pending.extend([(*ax, *bx), (*ay, *by)]),
            (H::Field { base: a, index: x }, H::Field { base: b, index: y }) if x == y => {
                pending.push((*a, *b))
            }
            (H::Index { base: a, index: x }, H::Index { base: b, index: y }) => {
                pending.extend([(*a, *b), (*x, *y)])
            }
            (
                H::Call {
                    callee: a,
                    type_arguments: x,
                    arguments: ax,
                    ..
                },
                H::Call {
                    callee: b,
                    type_arguments: y,
                    arguments: bx,
                    ..
                },
            ) if x == y && ax.len() == bx.len() => {
                pending.push((*a, *b));
                pending.extend(ax.iter().copied().zip(bx.iter().copied()));
            }
            _ => return false,
        }
    }
    true
}

fn same_constant(a: &hir::Constant, b: &hir::Constant) -> bool {
    use hir::Constant as C;
    match (a, b) {
        (
            C::Integer {
                magnitude: a,
                negative: x,
            },
            C::Integer {
                magnitude: b,
                negative: y,
            },
        ) => a == b && x == y,
        (C::Float(a), C::Float(b)) => a.to_bits() == b.to_bits(),
        (C::Bool(a), C::Bool(b)) => a == b,
        (C::Char(a), C::Char(b)) => a == b,
        (C::String(a), C::String(b)) => a == b,
        (C::Null, C::Null) => true,
        _ => false,
    }
}
