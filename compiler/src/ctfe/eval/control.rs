use super::*;

pub(super) enum Flow {
    Next,
    Return(Value),
    Break,
    Continue,
}

impl Evaluator<'_> {
    pub(super) fn block(
        &mut self,
        block: &[Statement],
        frame: &mut Frame<'_>,
    ) -> Result<Flow, Error> {
        for statement in block {
            self.charge(1, 0, statement.span)?;
            let flow = self.statement(statement, frame)?;
            if !matches!(flow, Flow::Next) {
                return Ok(flow);
            }
        }
        Ok(Flow::Next)
    }
    fn statement(&mut self, statement: &Statement, frame: &mut Frame<'_>) -> Result<Flow, Error> {
        match &statement.kind {
            StatementKind::Declare { local, value } => {
                frame.locals[*local as usize] =
                    value.map(|value| self.eval(value, frame)).transpose()?;
            }
            StatementKind::Assign { local, op, value } => {
                self.assign(*local, *op, *value, frame, statement.span)?
            }
            StatementKind::Evaluate(value) => {
                self.eval(*value, frame)?;
            }
            StatementKind::Return(value) => {
                let value = value
                    .map(|value| self.eval(value, frame))
                    .transpose()?
                    .unwrap_or(Value {
                        ty: TyId::VOID,
                        kind: ValueKind::Unit,
                    });
                return Ok(Flow::Return(value));
            }
            StatementKind::Block(body) => return self.block(body, frame),
            StatementKind::If { condition, yes, no } => {
                let branch = if self.condition(*condition, frame)? {
                    yes
                } else {
                    no
                };
                return self.block(branch, frame);
            }
            StatementKind::While { condition, body } => {
                return self.loop_body(Some(*condition), &[], body, frame);
            }
            StatementKind::For {
                initialize,
                condition,
                update,
                body,
            } => match self.block(initialize, frame)? {
                Flow::Next => return self.loop_body(*condition, update, body, frame),
                other => return Ok(other),
            },
            StatementKind::Break => return Ok(Flow::Break),
            StatementKind::Continue => return Ok(Flow::Continue),
            StatementKind::Assert { condition, message } => {
                if !self.condition(*condition, frame)? {
                    return Err(Error::new("E-CONST-ASSERT", message, statement.span));
                }
            }
        }
        Ok(Flow::Next)
    }
    fn condition(&mut self, expression: ExprId, frame: &mut Frame<'_>) -> Result<bool, Error> {
        self.eval(expression, frame)?.boolean().ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "constant condition must be bool",
                frame.expressions[expression].span,
            )
        })
    }
    fn loop_body(
        &mut self,
        condition: Option<ExprId>,
        update: &[Statement],
        body: &[Statement],
        frame: &mut Frame<'_>,
    ) -> Result<Flow, Error> {
        loop {
            if let Some(condition) = condition
                && !self.condition(condition, frame)?
            {
                return Ok(Flow::Next);
            }
            match self.block(body, frame)? {
                Flow::Break => return Ok(Flow::Next),
                Flow::Return(value) => return Ok(Flow::Return(value)),
                Flow::Next | Flow::Continue => {}
            }
            match self.block(update, frame)? {
                Flow::Next | Flow::Continue => {}
                Flow::Break => return Ok(Flow::Next),
                Flow::Return(value) => return Ok(Flow::Return(value)),
            }
            // Empty for(;;) loops still consume fuel.
            let span =
                self.frames
                    .last()
                    .copied()
                    .unwrap_or(Span::new(crate::source::FileId(0), 0, 0));
            self.charge(1, 0, span)?;
        }
    }
    fn assign(
        &mut self,
        local: u32,
        op: Option<BinaryOp>,
        expression: ExprId,
        frame: &mut Frame<'_>,
        span: Span,
    ) -> Result<(), Error> {
        let old = frame.locals[local as usize].clone();
        let value = self.eval(expression, frame)?;
        let value = match op {
            Some(op) => integer::binary(
                &self.program.types,
                op,
                old.ok_or_else(|| {
                    Error::new(
                        "E-CONST-CONTEXT",
                        "compound assignment reads an uninitialized constant local",
                        span,
                    )
                })?,
                value,
                self.limits.pointer_bits,
                span,
            )?,
            None => value,
        };
        frame.locals[local as usize] = Some(value);
        Ok(())
    }
}
