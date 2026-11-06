//! Runtime guards for the scalar predicates of checked const functions.
//! `old` retains entry values, but evaluates its expression only when reached.

use super::*;
use crate::syntax::ast::ClauseKind;
use std::collections::BTreeSet;

impl Builder<'_> {
    pub(super) fn prepare_contracts(&mut self) -> Result<(), LowerError> {
        if self.source.clauses.is_empty() {
            return Ok(());
        }
        let mut old = BTreeSet::new();
        for clause in &self.source.clauses {
            if let Some(result) = clause.result_local {
                self.sources[result.0 as usize] = Some(self.body.return_local);
            }
            self.contract_observations(clause.predicate, clause.result_local, &mut old)?;
        }
        for index in old {
            let source = hir::LocalId(index);
            let original = self.sources[index as usize].expect("entry parameter has storage");
            let declaration = &self.source.locals[index as usize];
            let snapshot =
                self.local(declaration.ty, LocalKind::Temporary, None, declaration.span)?;
            self.assign(
                Place::local(snapshot),
                Rvalue::Use(Operand::Copy(Place::local(original))),
                declaration.span,
            );
            self.old_parameters.push((source, snapshot));
        }
        self.contract_guards(ClauseKind::Requires)
    }

    fn contract_observations(
        &self,
        root: hir::ExprId,
        result: Option<hir::LocalId>,
        old: &mut BTreeSet<u32>,
    ) -> Result<(), LowerError> {
        let mut pending = vec![(root, false)];
        let mut remaining = 200_000usize;
        while let Some((id, entry)) = pending.pop() {
            let expression = &self.source.expressions[id];
            if remaining == 0 {
                return self.fail(
                    expression.span,
                    "runtime contract analysis exceeds its work limit",
                );
            }
            remaining -= 1;
            match &expression.kind {
                H::Local(local) => {
                    let property = self.properties.get(expression.ty);
                    if entry && (!property.copy || property.references)
                        || (!self.source.parameters.contains(local) && Some(*local) != result)
                    {
                        return self.fail(expression.span, "runtime const contracts may observe only Copy values without references from parameters or result");
                    }
                    if entry {
                        if Some(*local) == result {
                            return self
                                .fail(expression.span, "result has no entry-state value for old");
                        }
                        old.insert(local.0);
                    }
                }
                H::Old(value) => pending.push((*value, true)),
                _ => {
                    self.contract_children(&expression.kind, entry, &mut pending, expression.span)?
                }
            }
        }
        Ok(())
    }

    fn contract_children(
        &self,
        kind: &H,
        entry: bool,
        pending: &mut Vec<(hir::ExprId, bool)>,
        span: Span,
    ) -> Result<(), LowerError> {
        match kind {
            H::Constant(_) | H::ConstTerm(_) | H::Definition(_) => {}
            H::Group(value)
            | H::Unary { operand: value, .. }
            | H::Repeat { value, .. }
            | H::RepeatConst { value, .. } => pending.push((*value, entry)),
            H::Binary { left, right, .. } => pending.extend([(*left, entry), (*right, entry)]),
            H::Index { base, index } => pending.extend([(*base, entry), (*index, entry)]),
            H::Array(values) => pending.extend(values.iter().map(|&value| (value, entry))),
            H::Call {
                callee, arguments, ..
            } => {
                let logical = match self.source.expressions[callee].kind {
                    H::Definition(definition) => {
                        self.program.contracts.predicates.contains_key(&definition)
                    }
                    _ => false,
                };
                if !logical {
                    self.require_pure_callee(*callee, span)?;
                    pending.push((*callee, entry));
                }
                pending.extend(arguments.iter().map(|&value| (value, entry)));
            }
            _ => {
                return self.fail(
                    span,
                    "runtime const contract expression is outside its checked scalar domain",
                );
            }
        }
        Ok(())
    }

    fn require_pure_callee(&self, mut callee: hir::ExprId, span: Span) -> Result<(), LowerError> {
        for _ in 0..128 {
            match self.source.expressions[callee].kind {
                H::Group(inner) => callee = inner,
                H::Definition(definition) => {
                    if crate::contracts::purity::eligible(self.program, definition) {
                        return Ok(());
                    }
                    break;
                }
                _ => break,
            }
        }
        self.fail(
            span,
            "contract calls require checked pure, nosuspend and noalloc source functions",
        )
    }

    pub(super) fn contract_guards(&mut self, kind: ClauseKind) -> Result<(), LowerError> {
        for clause in &self.source.clauses {
            if clause.kind != kind {
                continue;
            }
            if self.is_logical(clause.predicate) {
                let action = if kind == ClauseKind::Requires {
                    crate::contracts::Action::Precondition
                } else {
                    crate::contracts::Action::Postcondition
                };
                self.logical_clause(
                    self.source,
                    clause.predicate,
                    &HashMap::new(),
                    action,
                    &mut Vec::new(),
                )?;
                continue;
            }
            let span = self.source.expressions[clause.predicate].span;
            self.enter(span)?;
            let condition = self.eval(clause.predicate)?;
            let passed = self.new_block(span, None)?;
            self.terminate(Terminator::Switch {
                condition,
                yes: passed,
                no: self.abort,
            });
            self.current = Some(passed);
            self.leave(span)?;
        }
        Ok(())
    }

    pub(super) fn old_expression(
        &mut self,
        expression: hir::ExprId,
    ) -> Result<Operand, LowerError> {
        let saved: Vec<_> = self
            .old_parameters
            .iter()
            .map(|&(local, snapshot)| (local, self.sources[local.0 as usize].replace(snapshot)))
            .collect();
        let value = self.eval(expression);
        for (local, previous) in saved {
            self.sources[local.0 as usize] = previous;
        }
        value
    }
}
