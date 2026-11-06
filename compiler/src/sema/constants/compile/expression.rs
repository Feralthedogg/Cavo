use super::*;
use crate::syntax::ast::{ExprKind as A, LiteralKind};

impl Compiler<'_, '_> {
    fn term(
        &mut self,
        id: crate::types::ConstId,
        span: Span,
        depth: usize,
    ) -> Result<ExprId, Error> {
        use crate::types::{ConstKind, ConstValue};
        if depth >= 128 {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant binding nesting limit exceeded",
                span,
            ));
        }
        let term = self.context.program.types.const_term(id).clone();
        let kind = match term.kind {
            ConstKind::Value(ConstValue::Usize(value)) => ExprKind::Value(Value {
                ty: term.ty,
                kind: ctfe::ValueKind::Integer {
                    magnitude: value.into(),
                    negative: false,
                },
            }),
            ConstKind::Value(ConstValue::Bool(value)) => ExprKind::Value(Value {
                ty: TyId::BOOL,
                kind: ctfe::ValueKind::Bool(value),
            }),
            ConstKind::Parameter { owner, index } => ExprKind::ConstParameter { owner, index },
            ConstKind::Global(definition) => {
                self.context.prepare_constant(definition)?;
                ExprKind::Global(definition)
            }
            ConstKind::Unary { op, operand } => ExprKind::Unary {
                op,
                operand: self.term(operand, span, depth + 1)?,
            },
            ConstKind::Binary { op, left, right } => ExprKind::Binary {
                op,
                left: self.term(left, span, depth + 1)?,
                right: self.term(right, span, depth + 1)?,
            },
            ConstKind::Call {
                definition,
                type_arguments,
                arguments,
            } => {
                self.context.const_function_type(definition)?;
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    values.push(self.term(argument, span, depth + 1)?);
                }
                ExprKind::Call {
                    function: definition,
                    generics: type_arguments,
                    arguments: values,
                }
            }
        };
        Ok(self.add(kind, term.ty, span))
    }
    pub(super) fn expression(
        &mut self,
        id: ast::ExprId,
        expected: Option<TyId>,
    ) -> Result<ExprId, Error> {
        let span = self.context.ast.expr(id).span;
        self.charge(span)?;
        self.depth += 1;
        let result = self.expression_inner(id, expected);
        self.depth -= 1;
        let result = result?;
        if let Some(expected) = expected {
            self.expect(self.ty(result), expected, span)?;
        }
        Ok(result)
    }
    fn expression_inner(
        &mut self,
        id: ast::ExprId,
        expected: Option<TyId>,
    ) -> Result<ExprId, Error> {
        let expression = self.context.ast.expr(id);
        let span = expression.span;
        match &expression.kind {
            A::Literal(kind) => self.literal(*kind, span, expected, false),
            A::Path(path) => self.path(path, span),
            A::Group(inner) => self.expression(*inner, expected),
            A::Unary {
                op: UnaryOp::Negate,
                operand,
            } if matches!(
                self.context.ast.expr(*operand).kind,
                A::Literal(LiteralKind::Integer | LiteralKind::Float)
            ) =>
            {
                let operand = self.context.ast.expr(*operand);
                let A::Literal(kind) = operand.kind else {
                    unreachable!()
                };
                self.literal(kind, operand.span, expected, true)
            }
            A::Unary { op, operand } => self.unary(*op, *operand, expected, span),
            A::Binary { op, left, right } => self.binary(*op, *left, *right, expected, span),
            A::Call {
                callee,
                type_arguments,
                arguments,
            } => self.call(*callee, type_arguments, arguments, span),
            A::Array(values) => self.array(values, expected, span),
            A::Repeat { value, count } => self.repeat(*value, *count, expected, span),
            A::Index { base, index } => self.index(*base, *index, span),
            _ => Err(Error::new(
                "E-CONST-CONTEXT",
                "expression is outside the supported constant-evaluation subset",
                span,
            )),
        }
    }
    fn literal(
        &mut self,
        kind: LiteralKind,
        span: Span,
        expected: Option<TyId>,
        negative: bool,
    ) -> Result<ExprId, Error> {
        let text = self.context.sources.file(span.file).slice(span);
        let mut diagnostics = Vec::new();
        let (ty, constant) = literal::check(
            text,
            kind,
            expected,
            negative,
            span,
            &mut self.context.program.types,
            &mut diagnostics,
        );
        if let Some(diagnostic) = diagnostics.into_iter().next() {
            return Err(Error::new("E-CONST-EVAL", diagnostic.message, span));
        }
        let value = Value::from_scalar(ty, constant).ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "constant initializer cannot contain a raw pointer",
                span,
            )
        })?;
        Ok(self.add(ExprKind::Value(value), ty, span))
    }
    fn path(&mut self, path: &[Name], span: Span) -> Result<ExprId, Error> {
        if path.len() == 1
            && let Some(value) = self.local_path(path[0].symbol, span)?
        {
            return Ok(value);
        }
        if let Some(value) = self.context.integer_constant(path, span)? {
            let maximum = self.context.symbols.get(path[1].symbol) == "MAX";
            return Ok(self.add(ExprKind::IntegerBound { maximum }, value.ty, span));
        }
        let definition = self.context.resolve(self.module, path).ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "unknown name in constant expression",
                span,
            )
        })?;
        self.context.prepare_constant(definition)?;
        Ok(self.add(
            ExprKind::Global(definition),
            self.context.definition(definition).ty,
            span,
        ))
    }
    fn local_path(&mut self, name: Symbol, span: Span) -> Result<Option<ExprId>, Error> {
        if self.phase == Phase::Ensures && self.context.symbols.get(name) == "result" {
            return Ok(Some(self.add(ExprKind::Result, self.result, span)));
        }
        if let Some(local) = self.local(name) {
            if self.initialized[local.id as usize] != Init::Yes {
                return Err(Error::new(
                    "E-CONST-CONTEXT",
                    "constant local is not definitely initialized",
                    span,
                ));
            }
            return Ok(Some(self.add(ExprKind::Local(local.id), local.ty, span)));
        }
        if let Some(value) = self.external.get(&name) {
            return match value {
                ConstBinding::Value(value) => Ok(Some(self.add(
                    ExprKind::Value(value.clone()),
                    value.ty,
                    span,
                ))),
                ConstBinding::Term(term) => self.term(*term, span, 0).map(Some),
                ConstBinding::Runtime => Err(Error::new(
                    "E-CONST-CONTEXT",
                    "runtime binding cannot be used as a constant",
                    span,
                )),
            };
        }
        if let Some(index) = self.const_parameter(name) {
            let ty = self
                .context
                .program
                .types
                .builtin("usize")
                .expect("usize type");
            return Ok(Some(self.add(
                ExprKind::ConstParameter {
                    owner: self.owner,
                    index,
                },
                ty,
                span,
            )));
        }
        Ok(None)
    }
    fn const_parameter(&self, name: Symbol) -> Option<u32> {
        self.context
            .program
            .types
            .generic_parameters(self.owner)
            .iter()
            .enumerate()
            .find_map(|(index, &(symbol, kind))| {
                (symbol == name && kind == GenericParamKind::Const).then_some(index as u32)
            })
    }
    fn unary(
        &mut self,
        op: UnaryOp,
        operand: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
    ) -> Result<ExprId, Error> {
        let operand = self.expression(operand, expected)?;
        // CTFE values are immutable data; concrete function arguments are checked
        // to be scalar. Runtime HIR retains the original ownership transfer.
        if op == UnaryOp::Move {
            return Ok(operand);
        }
        let ty = self.ty(operand);
        let valid = match op {
            UnaryOp::Not => ty == TyId::BOOL,
            UnaryOp::Positive | UnaryOp::Negate | UnaryOp::BitNot => {
                self.context.program.types.integer(ty)
            }
            _ => false,
        };
        if !valid {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "operator is not a constant scalar operation",
                span,
            ));
        }
        Ok(self.add(ExprKind::Unary { op, operand }, ty, span))
    }
    fn binary(
        &mut self,
        op: BinaryOp,
        left: ast::ExprId,
        right: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
    ) -> Result<ExprId, Error> {
        let comparison = matches!(
            op,
            BinaryOp::Equal
                | BinaryOp::NotEqual
                | BinaryOp::Less
                | BinaryOp::LessEqual
                | BinaryOp::Greater
                | BinaryOp::GreaterEqual
        );
        let logical = matches!(op, BinaryOp::And | BinaryOp::Or);
        let hint = if logical {
            Some(TyId::BOOL)
        } else if comparison {
            None
        } else {
            expected
        };
        let left = self.expression(left, hint)?;
        let ty = self.ty(left);
        let right = self.expression(right, Some(ty))?;
        let valid = if logical {
            ty == TyId::BOOL
        } else if matches!(op, BinaryOp::Equal | BinaryOp::NotEqual) {
            self.context.program.types.integer(ty)
                || matches!(self.context.program.types.get(ty), Ty::Bool | Ty::Char)
        } else {
            self.context.program.types.integer(ty)
        };
        if !valid {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "operator does not accept these constant operands",
                span,
            ));
        }
        Ok(self.add(
            ExprKind::Binary { op, left, right },
            if comparison || logical {
                TyId::BOOL
            } else {
                ty
            },
            span,
        ))
    }
    fn call(
        &mut self,
        callee: ast::ExprId,
        generics: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        span: Span,
    ) -> Result<ExprId, Error> {
        let ast = self.context.ast;
        let mut callee = callee;
        for _ in 0..128 {
            if let A::Group(inner) = ast.expr(callee).kind {
                callee = inner;
            } else {
                break;
            }
        }
        let A::Path(path) = &ast.expr(callee).kind else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant calls require a direct function name",
                span,
            ));
        };
        if self.phase != Phase::Body
            && path.len() == 1
            && self.context.symbols.get(path[0].symbol) == "old"
        {
            return self.old_call(generics, arguments, span);
        }
        self.require_direct_callee(path, span)?;
        let definition = self
            .context
            .resolve(self.module, path)
            .ok_or_else(|| Error::new("E-CONST-CONTEXT", "unknown const function", span))?;
        let ty = self.context.const_function_type(definition)?;
        let Ty::Function { parameters, result } = self.context.program.types.get(ty).clone() else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant callee is not a function",
                span,
            ));
        };
        if parameters.len() != arguments.len() {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant call has the wrong argument count",
                span,
            ));
        }
        let generics = self.generic_arguments(definition, generics, span)?;
        let values = self.call_arguments(definition, &generics, &parameters, arguments, span)?;
        let result = self
            .context
            .program
            .types
            .substitute_generics(result, definition, &generics)
            .map_err(|error| Error::new("E-CONST-CONTEXT", error.to_string(), span))?;
        Ok(self.add(
            ExprKind::Call {
                function: definition,
                generics,
                arguments: values,
            },
            result,
            span,
        ))
    }
    fn require_direct_callee(&self, path: &[Name], span: Span) -> Result<(), Error> {
        if path.first().is_some_and(|name| {
            self.local(name.symbol).is_some()
                || self.external.contains_key(&name.symbol)
                || self.const_parameter(name.symbol).is_some()
        }) {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "runtime or indirect callable cannot be used in a constant expression",
                span,
            ));
        }
        Ok(())
    }
    fn call_arguments(
        &mut self,
        definition: DefId,
        generics: &[GenericArg],
        parameters: &[TyId],
        arguments: &[ast::ExprId],
        span: Span,
    ) -> Result<Vec<ExprId>, Error> {
        let mut values = Vec::with_capacity(arguments.len());
        for (&argument, &parameter) in arguments.iter().zip(parameters) {
            let parameter = self
                .context
                .program
                .types
                .substitute_generics(parameter, definition, generics)
                .map_err(|error| Error::new("E-CONST-CONTEXT", error.to_string(), span))?;
            values.push(self.expression(argument, Some(parameter))?);
        }
        Ok(values)
    }
    fn old_call(
        &mut self,
        generics: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        span: Span,
    ) -> Result<ExprId, Error> {
        if self.phase != Phase::Ensures || arguments.len() != 1 || !generics.is_empty() {
            return Err(Error::new(
                "E-CONST-CONTRACT",
                "old requires one ensures expression",
                span,
            ));
        }
        let first = self.expressions.len();
        let expression = self.expression(arguments[0], None)?;
        if self.expressions[first..]
            .iter()
            .any(|expression| matches!(expression.kind, ExprKind::Result))
        {
            return Err(Error::new(
                "E-CONST-CONTRACT",
                "result has no entry-state value for old",
                span,
            ));
        }
        Ok(self.add(ExprKind::Old(expression), self.ty(expression), span))
    }
    fn generic_arguments(
        &mut self,
        definition: DefId,
        arguments: &[ast::GenericArg],
        span: Span,
    ) -> Result<Vec<GenericArg>, Error> {
        let bindings = self.constant_bindings();
        let scope = crate::sema::const_generics::TypeScope {
            module: self.module,
            owner: self.owner,
            parameters: &self.types,
        };
        self.context
            .resolve_generic_arguments(definition, arguments, scope, &bindings, span)
    }
    fn array(
        &mut self,
        values: &[ast::ExprId],
        expected: Option<TyId>,
        span: Span,
    ) -> Result<ExprId, Error> {
        let mut inner = expected.and_then(|ty| match self.context.program.types.get(ty) {
            Ty::Array { inner, .. } => Some(*inner),
            _ => None,
        });
        let mut expressions = Vec::with_capacity(values.len());
        for &value in values {
            let value = self.expression(value, inner)?;
            inner.get_or_insert(self.ty(value));
            expressions.push(value);
        }
        let inner = inner.ok_or_else(|| {
            Error::new(
                "E-CONST-CONTEXT",
                "empty constant array requires a type",
                span,
            )
        })?;
        let ty = self.context.program.types.intern(Ty::Array {
            inner,
            length: values.len() as u64,
        });
        Ok(self.add(ExprKind::Array(expressions), ty, span))
    }
    fn repeat(
        &mut self,
        value: ast::ExprId,
        count: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
    ) -> Result<ExprId, Error> {
        let inner = expected.and_then(|ty| match self.context.program.types.get(ty) {
            Ty::Array { inner, .. } => Some(*inner),
            _ => None,
        });
        let value = self.expression(value, inner)?;
        let usize_ty = self
            .context
            .program
            .types
            .builtin("usize")
            .expect("usize type");
        let length = self
            .context
            .eval_constant(self.module, self.owner, count, usize_ty, self.external)?
            .usize_value()
            .ok_or_else(|| Error::new("E-CONST-CONTEXT", "repeat length must be usize", span))?;
        let count = self.expression(count, Some(usize_ty))?;
        let ty = self.context.program.types.intern(Ty::Array {
            inner: self.ty(value),
            length,
        });
        Ok(self.add(ExprKind::Repeat { value, count }, ty, span))
    }
    fn index(
        &mut self,
        base: ast::ExprId,
        index: ast::ExprId,
        span: Span,
    ) -> Result<ExprId, Error> {
        let base = self.expression(base, None)?;
        let Ty::Array { inner, .. } = *self.context.program.types.get(self.ty(base)) else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant indexing requires an array",
                span,
            ));
        };
        let usize_ty = self
            .context
            .program
            .types
            .builtin("usize")
            .expect("usize type");
        let index = self.expression(index, Some(usize_ty))?;
        Ok(self.add(ExprKind::Index { base, index }, inner, span))
    }
}
