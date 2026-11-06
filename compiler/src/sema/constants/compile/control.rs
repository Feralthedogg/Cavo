use super::*;
use crate::ctfe::StatementKind as S;

impl Compiler<'_, '_> {
    pub(super) fn block(&mut self, block: &ast::Block) -> Result<(Vec<Statement>, bool), Error> {
        self.scopes.push(HashMap::new());
        let mut statements = Vec::with_capacity(block.statements.len());
        let mut falls = true;
        for &statement in &block.statements {
            let (statement, current_falls) = self.statement(statement)?;
            statements.push(statement);
            falls &= current_falls;
        }
        self.scopes.pop();
        Ok((statements, falls))
    }
    fn statement(&mut self, id: ast::StmtId) -> Result<(Statement, bool), Error> {
        let statement = self.context.ast.stmt(id);
        self.charge(statement.span)?;
        self.depth += 1;
        let result = self.statement_kind(&statement.kind, statement.span);
        self.depth -= 1;
        result.map(|(kind, falls)| {
            (
                Statement {
                    span: statement.span,
                    kind,
                },
                falls,
            )
        })
    }
    fn statement_kind(
        &mut self,
        statement: &ast::StmtKind,
        span: Span,
    ) -> Result<(S, bool), Error> {
        match statement {
            ast::StmtKind::Variable(variable) => self.declare(variable).map(|kind| (kind, true)),
            ast::StmtKind::Assign { target, op, value } => self
                .assign(*target, *op, *value, span)
                .map(|kind| (kind, true)),
            ast::StmtKind::Expression(value) => {
                Ok((S::Evaluate(self.expression(*value, None)?), true))
            }
            ast::StmtKind::Return(value) => self.return_statement(*value, span),
            ast::StmtKind::Block(block) => self
                .block(block)
                .map(|(body, falls)| (S::Block(body), falls)),
            ast::StmtKind::If {
                condition,
                then_block,
                otherwise,
            } => self.conditional(*condition, then_block, *otherwise),
            ast::StmtKind::While { condition, body } => {
                self.loop_statement(None, Some(*condition), None, body)
            }
            ast::StmtKind::For {
                initialize,
                condition,
                update,
                body,
            } => self.loop_statement(*initialize, *condition, *update, body),
            ast::StmtKind::Break | ast::StmtKind::Continue => self.loop_exit(statement, span),
            ast::StmtKind::StaticAssert(assertion) => {
                self.static_assert(assertion).map(|kind| (kind, true))
            }
            ast::StmtKind::Empty => Ok((S::Block(Vec::new()), true)),
            _ => Err(Error::new(
                "E-CONST-CONTEXT",
                "statement is outside the pure const-function subset",
                span,
            )),
        }
    }
    fn return_statement(
        &mut self,
        value: Option<ast::ExprId>,
        span: Span,
    ) -> Result<(S, bool), Error> {
        let value = value
            .map(|value| self.expression(value, Some(self.result)))
            .transpose()?;
        if value.is_none() && self.result != TyId::VOID {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "non-void const function must return a value",
                span,
            ));
        }
        Ok((S::Return(value), false))
    }
    fn loop_exit(&self, statement: &ast::StmtKind, span: Span) -> Result<(S, bool), Error> {
        if self.loops.is_empty() {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant loop exit has no enclosing loop",
                span,
            ));
        }
        Ok((
            if matches!(statement, ast::StmtKind::Break) {
                S::Break
            } else {
                S::Continue
            },
            false,
        ))
    }
    fn declare(&mut self, variable: &ast::Variable) -> Result<S, Error> {
        let hint = if matches!(self.context.ast.ty(variable.ty).kind, TypeKind::Infer) {
            None
        } else {
            Some(self.resolve_type(variable.ty)?)
        };
        let value = variable
            .initializer
            .map(|value| self.expression(value, hint))
            .transpose()?;
        let ty = hint
            .or_else(|| value.map(|value| self.ty(value)))
            .ok_or_else(|| {
                Error::new(
                    "E-CONST-CONTEXT",
                    "const auto local requires an initializer",
                    variable.name.span,
                )
            })?;
        if !matches!(
            self.context.program.types.get(ty),
            Ty::Integer { .. } | Ty::Bool | Ty::Char | Ty::Parameter { .. }
        ) {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "const-function locals require scalar values",
                variable.name.span,
            ));
        }
        let constant = self.constant_initializer(variable, ty);
        let local = self.bind(
            variable.name,
            ty,
            variable.constant,
            if value.is_some() { Init::Yes } else { Init::No },
        )?;
        if let Some(value) = constant {
            self.constant_values.insert(local, value);
        }
        Ok(S::Declare { local, value })
    }
    fn assign(
        &mut self,
        target: ast::ExprId,
        op: Option<BinaryOp>,
        value: ast::ExprId,
        span: Span,
    ) -> Result<S, Error> {
        let ast::ExprKind::Path(path) = &self.context.ast.expr(target).kind else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "const functions may assign only their own scalar locals",
                span,
            ));
        };
        let local = if path.len() == 1 {
            self.local(path[0].symbol)
        } else {
            None
        }
        .ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "constant assignment cannot mutate external state",
                span,
            )
        })?;
        let initialized = self.initialized[local.id as usize];
        if local.constant
            && (initialized != Init::No
                || self.loops.iter().any(|&base| (local.id as usize) < base))
        {
            return Err(Error::new(
                "E-ASSIGN-CONST",
                "cannot reassign this immutable constant local",
                span,
            ));
        }
        if op.is_some() && initialized != Init::Yes {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "compound assignment requires an initialized constant local",
                span,
            ));
        }
        if op.is_some() && !self.context.program.types.integer(local.ty) {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant compound assignment requires an integer",
                span,
            ));
        }
        let value = self.expression(value, Some(local.ty))?;
        self.initialized[local.id as usize] = Init::Yes;
        Ok(S::Assign {
            local: local.id,
            op,
            value,
        })
    }
    fn conditional(
        &mut self,
        condition: ast::ExprId,
        yes: &ast::Block,
        otherwise: Option<ast::StmtId>,
    ) -> Result<(S, bool), Error> {
        let condition = self.expression(condition, Some(TyId::BOOL))?;
        let before = self.initialized.clone();
        let (yes, yes_falls) = self.block(yes)?;
        let after_yes = self.initialized.clone();
        self.initialized[..before.len()].copy_from_slice(&before);
        let (no, no_falls) = match otherwise {
            Some(id) => {
                let (statement, falls) = self.statement(id)?;
                (vec![statement], falls)
            }
            None => (Vec::new(), true),
        };
        let after_no = self.initialized.clone();
        match (yes_falls, no_falls) {
            (true, true) => self.merge(&after_yes[..before.len()], &after_no),
            (true, false) => {
                self.initialized[..before.len()].copy_from_slice(&after_yes[..before.len()])
            }
            (false, true) => {}
            (false, false) => self.initialized[..before.len()].copy_from_slice(&before),
        }
        Ok((S::If { condition, yes, no }, yes_falls || no_falls))
    }
    fn loop_statement(
        &mut self,
        initialize: Option<ast::StmtId>,
        condition: Option<ast::ExprId>,
        update: Option<ast::StmtId>,
        body: &ast::Block,
    ) -> Result<(S, bool), Error> {
        self.scopes.push(HashMap::new());
        let initialize = initialize
            .map(|statement| {
                self.statement(statement)
                    .map(|(statement, _)| vec![statement])
            })
            .transpose()?
            .unwrap_or_default();
        let condition = condition
            .map(|condition| self.expression(condition, Some(TyId::BOOL)))
            .transpose()?;
        let before = self.initialized.clone();
        self.loops.push(self.locals.len());
        let (body, _) = self.block(body)?;
        let update = update
            .map(|statement| {
                self.statement(statement)
                    .map(|(statement, _)| vec![statement])
            })
            .transpose()?
            .unwrap_or_default();
        self.loops.pop();
        let after = self.initialized.clone();
        self.merge(&before, &after);
        self.scopes.pop();
        Ok((
            S::For {
                initialize,
                condition,
                update,
                body,
            },
            true,
        ))
    }
    fn static_assert(&mut self, assertion: &ast::StaticAssert) -> Result<S, Error> {
        // Value parameters remain runtime bindings for a declaration assertion;
        // only type-level const parameters or independently constant data qualify.
        let bindings = self.constant_bindings();
        self.context
            .check_static_assert(assertion, self.module, self.owner, &bindings)?;
        Ok(S::Block(Vec::new()))
    }
}
