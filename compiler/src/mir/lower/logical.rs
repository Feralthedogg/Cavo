use super::*;
use crate::contracts::{Action, Atom, MemoryPredicate, Statement as ContractStatement};

impl Builder<'_> {
    pub(super) fn is_logical(&self, root: hir::ExprId) -> bool {
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            match &self.source.expressions[id].kind {
                H::Call { callee, .. }
                    if predicate_target(self.program, self.source, *callee).is_some() =>
                {
                    return true;
                }
                H::Binary { left, right, .. } => pending.extend([*left, *right]),
                H::Group(value) => pending.push(*value),
                _ => {}
            }
        }
        false
    }

    pub(super) fn lower_assumption(
        &mut self,
        assumption: &crate::contracts::SourceAssumption,
        span: Span,
    ) -> Result<(), LowerError> {
        self.logical_clause(
            self.source,
            assumption.predicate,
            &HashMap::new(),
            Action::Assume {
                reason: assumption.reason.clone(),
            },
            &mut Vec::new(),
        )?;
        self.charge(span)
    }

    pub(super) fn logical_clause(
        &mut self,
        source: &hir::Function,
        id: hir::ExprId,
        bindings: &HashMap<hir::LocalId, Operand>,
        action: Action,
        visiting: &mut Vec<hir::DefId>,
    ) -> Result<(), LowerError> {
        let expression = &source.expressions[id];
        match &expression.kind {
            H::Group(inner) => self.logical_clause(source, *inner, bindings, action, visiting),
            H::Binary {
                op: BinaryOp::And,
                left,
                right,
            } => {
                self.logical_clause(source, *left, bindings, action.clone(), visiting)?;
                self.logical_clause(source, *right, bindings, action, visiting)
            }
            H::Call {
                callee,
                type_arguments,
                arguments,
                ..
            } if predicate_target(self.program, source, *callee).is_some() => {
                let definition =
                    predicate_target(self.program, source, *callee).expect("checked predicate");
                let values = arguments
                    .iter()
                    .map(|&id| self.contract_value(source, id, bindings))
                    .collect::<Result<Vec<_>, _>>()?;
                self.logical_call(
                    definition,
                    type_arguments,
                    values,
                    action,
                    expression.span,
                    visiting,
                )
            }
            _ => {
                let value = self.contract_value(source, id, bindings)?;
                if matches!(action, Action::Assume { .. }) {
                    self.emit_contract(
                        action,
                        MemoryPredicate::Scalar,
                        Vec::new(),
                        vec![value],
                        expression.span,
                    );
                } else {
                    self.guard(value, expression.span)?;
                }
                Ok(())
            }
        }
    }

    fn logical_call(
        &mut self,
        definition: hir::DefId,
        types: &[crate::types::GenericArg],
        values: Vec<Operand>,
        action: Action,
        span: Span,
        visiting: &mut Vec<hir::DefId>,
    ) -> Result<(), LowerError> {
        let predicate = &self.program.contracts.predicates[&definition];
        if let Some(kind) = predicate.memory {
            self.emit_contract(action, kind, types.to_vec(), values, span);
            return Ok(());
        }
        if visiting.len() >= 64 || visiting.contains(&definition) {
            return self.fail(
                span,
                "named contract expansion is cyclic or exceeds its depth budget",
            );
        }
        let Some(body) = &predicate.body else {
            return self.fail(span, "named contract has no checked predicate body");
        };
        let Some(returned) = body
            .statements
            .iter()
            .find_map(|statement| match statement.kind {
                S::Return(Some(value)) => Some(value),
                _ => None,
            })
        else {
            return self.fail(span, "named contract has no predicate result");
        };
        let bindings = body.parameters.iter().copied().zip(values).collect();
        visiting.push(definition);
        let result = self.logical_clause(body, returned, &bindings, action, visiting);
        visiting.pop();
        result
    }

    fn emit_contract(
        &mut self,
        action: Action,
        predicate: MemoryPredicate,
        type_arguments: Vec<crate::types::GenericArg>,
        arguments: Vec<Operand>,
        span: Span,
    ) {
        self.emit(
            StatementKind::Contract(ContractStatement {
                action,
                atom: Atom {
                    predicate,
                    type_arguments,
                    arguments,
                    declaration: span,
                },
            }),
            span,
        );
    }

    fn guard(&mut self, condition: Operand, span: Span) -> Result<(), LowerError> {
        let passed = self.new_block(span, None)?;
        self.terminate(Terminator::Switch {
            condition,
            yes: passed,
            no: self.abort,
        });
        self.current = Some(passed);
        Ok(())
    }

    pub(super) fn call_contracts(
        &mut self,
        definition: hir::DefId,
        arguments: &[Operand],
        span: Span,
    ) -> Result<(), LowerError> {
        let Some(signature) = self.program.contracts.signatures.get(&definition) else {
            return Ok(());
        };
        let inherited = self
            .program
            .implementations
            .iter()
            .flat_map(|item| &item.methods)
            .find(|method| method.implementation == definition)
            .and_then(|method| method.declaration)
            .filter(|&declaration| declaration != definition)
            .and_then(|declaration| self.program.contracts.signatures.get(&declaration));
        if signature.clauses.is_empty() && inherited.is_none_or(|header| header.clauses.is_empty())
        {
            return Ok(());
        }
        if self.contract_calls.len() >= 64 || self.contract_calls.contains(&definition) {
            return self.fail(
                span,
                "contract precondition expansion is cyclic or exceeds its depth budget",
            );
        }
        self.contract_calls.push(definition);
        let result = self
            .call_requirements(signature, arguments, span)
            .and_then(|()| {
                if let Some(header) = inherited {
                    self.call_requirements(header, arguments, span)
                } else {
                    Ok(())
                }
            });
        self.contract_calls.pop();
        result
    }

    fn call_requirements(
        &mut self,
        signature: &hir::Function,
        arguments: &[Operand],
        span: Span,
    ) -> Result<(), LowerError> {
        let bindings = signature
            .parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect();
        for clause in &signature.clauses {
            if clause.kind == crate::syntax::ast::ClauseKind::Requires {
                self.logical_clause(
                    signature,
                    clause.predicate,
                    &bindings,
                    Action::Requirement,
                    &mut Vec::new(),
                )?;
            }
        }
        self.charge(span)
    }

    fn contract_value(
        &mut self,
        source: &hir::Function,
        id: hir::ExprId,
        bindings: &HashMap<hir::LocalId, Operand>,
    ) -> Result<Operand, LowerError> {
        if std::ptr::eq(source, self.source) && bindings.is_empty() {
            return self.eval(id);
        }
        let expression = &source.expressions[id];
        match &expression.kind {
            H::Local(local) => bindings.get(local).cloned().ok_or_else(|| LowerError {
                span: expression.span, message: "contract argument is not bound at this call".into(),
            }),
            H::Definition(definition) => Ok(Operand::Function { definition: *definition, ty: expression.ty }),
            H::Constant(value) => Ok(Operand::Constant { value: value.clone(), ty: expression.ty }),
            H::ConstTerm(value) => Ok(Operand::ConstTerm { value: *value, ty: expression.ty }),
            H::Group(value) => self.contract_value(source, *value, bindings),
            H::Binary { op, left, right } if !matches!(op, BinaryOp::And | BinaryOp::Or) => {
                let left = self.contract_value(source, *left, bindings)?;
                let right = self.contract_value(source, *right, bindings)?;
                let value = Rvalue::Binary { op: *op, left, right };
                self.operation(expression.ty, value, expression.span)
            }
            H::Unary { op, operand } => {
                let operand = self.contract_value(source, *operand, bindings)?;
                if *op == UnaryOp::Dereference { return self.contract_projection(operand, Projection::Deref, expression.span); }
                let value = Rvalue::Unary { op: *op, operand };
                self.operation(expression.ty, value, expression.span)
            }
            H::Field { base, index } => {
                let value = self.contract_value(source, *base, bindings)?;
                let ty = source.expressions[*base].ty;
                let value = if matches!(self.program.types.get(ty), Ty::Reference { .. }) {
                    self.contract_projection(value, Projection::Deref, expression.span)?
                } else { value };
                self.contract_projection(value, Projection::Field(*index), expression.span)
            }
            H::Call { .. } => self.contract_call(source, expression, bindings),
            _ => self.fail(expression.span,
                "contract substitution cannot establish this expression; bind its pure scalar inputs explicitly"),
        }
    }
    fn contract_projection(
        &self,
        value: Operand,
        projection: Projection,
        span: Span,
    ) -> Result<Operand, LowerError> {
        match value {
            Operand::Copy(mut place) | Operand::Move(mut place) => {
                place.projection.push(projection);
                Ok(Operand::Copy(place))
            }
            _ => self.fail(span, "contract projection needs a stable typed place"),
        }
    }

    fn contract_call(
        &mut self,
        source: &hir::Function,
        expression: &hir::Expr,
        bindings: &HashMap<hir::LocalId, Operand>,
    ) -> Result<Operand, LowerError> {
        let H::Call {
            callee,
            type_arguments,
            arguments,
            parameter_types,
        } = &expression.kind
        else {
            unreachable!("contract call");
        };
        let callee = self.contract_value(source, *callee, bindings)?;
        let Operand::Function { definition, .. } = callee else {
            return self.fail(
                expression.span,
                "a contract helper requires an established pure direct target",
            );
        };
        if !crate::contracts::purity::eligible(self.program, definition) {
            return self.fail(
                expression.span,
                "contract helper is not established as pure, nosuspend and noalloc",
            );
        }
        let arguments = arguments
            .iter()
            .map(|&id| self.contract_value(source, id, bindings))
            .collect::<Result<Vec<_>, _>>()?;
        self.call_contracts(definition, &arguments, expression.span)?;
        let destination = self.local(expression.ty, LocalKind::Temporary, None, expression.span)?;
        let normal = self.new_block(expression.span, None)?;
        self.terminate(Terminator::Call {
            callee,
            type_arguments: type_arguments.clone(),
            arguments,
            parameter_types: parameter_types.clone(),
            destination: Place::local(destination),
            normal,
            panic: self.abort,
            cancel: self.abort,
        });
        self.current = Some(normal);
        Ok(Operand::Copy(Place::local(destination)))
    }
}

fn predicate_target(
    program: &hir::Program,
    source: &hir::Function,
    mut id: hir::ExprId,
) -> Option<hir::DefId> {
    for _ in 0..128 {
        match source.expressions[id].kind {
            H::Group(inner) => id = inner,
            H::Definition(definition) if program.contracts.predicates.contains_key(&definition) => {
                return Some(definition);
            }
            _ => return None,
        }
    }
    None
}
