use super::*;
use crate::arena::Access as _;

impl Evaluator<'_> {
    pub(super) fn eval(&mut self, id: ExprId, frame: &Frame<'_>) -> Result<Value, Error> {
        self.eval_view(id, frame.view())
    }
    fn eval_view(&mut self, id: ExprId, frame: View<'_>) -> Result<Value, Error> {
        let expression = frame.expressions.get_id(id).ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "invalid constant expression ID",
                Span::new(crate::source::FileId(0), 0, 0),
            )
        })?;
        self.charge(1, 0, expression.span)?;
        if self.expression_depth >= 256 {
            return Err(limit(expression.span));
        }
        self.expression_depth += 1;
        let result = self.eval_inner(expression, frame);
        self.expression_depth -= 1;
        result
    }
    fn eval_inner(&mut self, expression: &Expr, frame: View<'_>) -> Result<Value, Error> {
        match &expression.kind {
            ExprKind::IntegerBound { maximum } => integer::bound(
                &self.program.types,
                expression.ty,
                *maximum,
                self.limits.pointer_bits,
                expression.span,
            ),
            ExprKind::Value(value) => self.literal_value(value, expression.span),
            ExprKind::Local(local) => frame
                .locals
                .get(*local as usize)
                .cloned()
                .flatten()
                .ok_or_else(|| {
                    Error::new(
                        "E-CONST-CONTEXT",
                        "constant reads an uninitialized local",
                        expression.span,
                    )
                }),
            ExprKind::Global(definition) => self.global(*definition),
            ExprKind::ConstParameter { owner, index } => {
                self.constant_parameter(*owner, *index, frame.bindings, expression.span)
            }
            ExprKind::Unary { op, operand } => self.unary(*op, *operand, frame, expression.span),
            ExprKind::Binary { op, left, right } => {
                self.binary(*op, *left, *right, frame, expression.span)
            }
            ExprKind::Call {
                function,
                generics,
                arguments,
            } => self.evaluate_call(*function, generics, arguments, frame),
            ExprKind::Old(inner) => self.eval_view(
                *inner,
                View {
                    locals: frame.entry,
                    result: None,
                    ..frame
                },
            ),
            ExprKind::Result => frame.result.cloned().ok_or_else(|| {
                Error::new(
                    "E-CONST-CONTRACT",
                    "result is unavailable before const return",
                    expression.span,
                )
            }),
            ExprKind::Array(values) => self.array(values, expression.ty, frame, expression.span),
            ExprKind::Repeat { value, count } => {
                self.repeat(*value, *count, expression.ty, frame, expression.span)
            }
            ExprKind::Index { base, index } => self.index(*base, *index, frame, expression.span),
        }
    }
    fn literal_value(&mut self, value: &Value, span: Span) -> Result<Value, Error> {
        integer::validate(&self.program.types, value, self.limits.pointer_bits, span)?;
        self.charge(0, value_cost(value, span)?, span)?;
        Ok(value.clone())
    }
    fn unary(
        &mut self,
        op: UnaryOp,
        operand: ExprId,
        frame: View<'_>,
        span: Span,
    ) -> Result<Value, Error> {
        let value = self.eval_view(operand, frame)?;
        integer::unary(
            &self.program.types,
            op,
            value,
            self.limits.pointer_bits,
            span,
        )
    }
    pub(in crate::ctfe) fn constant_parameter(
        &self,
        owner: hir::DefId,
        index: u32,
        bindings: &Bindings,
        span: Span,
    ) -> Result<Value, Error> {
        if bindings.owner == Some(owner)
            && let Some(Binding::Const(value)) = bindings.values.get(index as usize)
        {
            return Ok(value.clone());
        }
        Err(Error::new(
            "E-CONST-CONTEXT",
            "constant parameter is not concretely instantiated",
            span,
        ))
    }
    fn binary(
        &mut self,
        op: BinaryOp,
        left: ExprId,
        right: ExprId,
        frame: View<'_>,
        span: Span,
    ) -> Result<Value, Error> {
        let left = self.eval_view(left, frame)?;
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            let left = left.boolean().ok_or_else(|| {
                Error::new(
                    "E-CONST-CONTEXT",
                    "logical const operands must be bool",
                    span,
                )
            })?;
            if left == (op == BinaryOp::Or) {
                return Ok(Value {
                    ty: TyId::BOOL,
                    kind: ValueKind::Bool(left),
                });
            }
            return self.eval_view(right, frame);
        }
        let right = self.eval_view(right, frame)?;
        integer::binary(
            &self.program.types,
            op,
            left,
            right,
            self.limits.pointer_bits,
            span,
        )
    }
    fn evaluate_call(
        &mut self,
        definition: hir::DefId,
        generics: &[GenericArg],
        arguments: &[ExprId],
        frame: View<'_>,
    ) -> Result<Value, Error> {
        let bindings = self.resolve_bindings(definition, generics, frame.bindings)?;
        let mut values = Vec::with_capacity(arguments.len());
        for &argument in arguments {
            values.push(self.eval_view(argument, frame)?);
        }
        self.invoke(definition, bindings, values)
    }
    fn array(
        &mut self,
        expressions: &[ExprId],
        ty: TyId,
        frame: View<'_>,
        span: Span,
    ) -> Result<Value, Error> {
        self.charge(0, expressions.len() as u64 * 16, span)?;
        let mut values = Vec::with_capacity(expressions.len());
        for &expression in expressions {
            values.push(self.eval_view(expression, frame)?);
        }
        Ok(Value {
            ty,
            kind: ValueKind::Array(values),
        })
    }
    fn repeat(
        &mut self,
        value: ExprId,
        count: ExprId,
        ty: TyId,
        frame: View<'_>,
        span: Span,
    ) -> Result<Value, Error> {
        let value = self.eval_view(value, frame)?;
        let count = self.eval_view(count, frame)?.usize_value().ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "constant repeat length must be usize",
                span,
            )
        })?;
        let bytes = value_cost(&value, span)?
            .checked_mul(count)
            .ok_or_else(|| limit(span))?;
        self.charge(0, bytes, span)?;
        let count = usize::try_from(count).map_err(|_| limit(span))?;
        Ok(Value {
            ty,
            kind: ValueKind::Array(vec![value; count]),
        })
    }
    fn index(
        &mut self,
        base: ExprId,
        index: ExprId,
        frame: View<'_>,
        span: Span,
    ) -> Result<Value, Error> {
        let base = self.eval_view(base, frame)?;
        let index = self
            .eval_view(index, frame)?
            .usize_value()
            .ok_or_else(|| Error::new("E-CONST-CONTEXT", "constant index must be usize", span))?;
        let ValueKind::Array(values) = base.kind else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant indexing requires array data",
                span,
            ));
        };
        values.get(index as usize).cloned().ok_or_else(|| {
            Error::new(
                "E-CONST-EVAL",
                "constant array index is out of bounds",
                span,
            )
        })
    }
}

pub(super) fn value_cost(value: &Value, span: Span) -> Result<u64, Error> {
    let mut pending = vec![value];
    let mut cost = 0u64;
    while let Some(value) = pending.pop() {
        cost = cost.checked_add(16).ok_or_else(|| limit(span))?;
        if cost > 1_048_576 {
            return Err(limit(span));
        }
        match &value.kind {
            ValueKind::String(value) => {
                cost = cost
                    .checked_add(value.len() as u64)
                    .ok_or_else(|| limit(span))?
            }
            ValueKind::Array(values) | ValueKind::Record { fields: values, .. } => {
                if pending.len().saturating_add(values.len()) > 65_536 {
                    return Err(limit(span));
                }
                pending.extend(values);
            }
            _ => {}
        }
    }
    Ok(cost)
}
