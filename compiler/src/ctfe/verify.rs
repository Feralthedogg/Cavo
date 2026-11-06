use super::*;
use crate::types::Ty;

const LIMIT: usize = 200_000;

impl Program {
    /// Structural/type boundary only; it never executes a query or invokes HIR validation.
    pub fn validate(&self, hir: &hir::Program) -> Result<(), Error> {
        for (&definition, function) in &self.functions {
            validate_function(hir, definition, function)?;
        }
        for (&definition, global) in &self.globals {
            validate_global(hir, definition, global)?;
        }
        for assertion in &self.assertions {
            owner(hir, assertion.owner, assertion.span)?;
            let term = hir
                .types
                .constant_terms()
                .get(assertion.condition.0 as usize)
                .ok_or_else(|| invalid("invalid assertion constant ID", assertion.span))?;
            compatible(hir, term.ty, TyId::BOOL, assertion.span)?;
        }
        Ok(())
    }
}

fn validate_function(
    hir: &hir::Program,
    definition: hir::DefId,
    function: &Function,
) -> Result<(), Error> {
    let span = function.span;
    ensure(
        definition == function.definition,
        "constant function key mismatch",
        span,
    )?;
    owner(hir, definition, span)?;
    let declaration = &hir.definitions[definition];
    ensure(
        declaration.kind == hir::DefinitionKind::Function && declaration.foreign_abi.is_none(),
        "constant function must have a source function declaration",
        span,
    )?;
    validate_signature(hir, declaration.ty, function)?;
    ensure(
        function.parameters.len() <= function.locals.len(),
        "constant parameter/local count mismatch",
        span,
    )?;
    for &ty in function
        .parameters
        .iter()
        .chain(&function.locals)
        .chain([&function.result])
    {
        valid_type(hir, ty, span)?;
    }
    for (&parameter, &local) in function.parameters.iter().zip(&function.locals) {
        compatible(hir, parameter, local, span)?;
    }
    let verifier = Body {
        hir,
        expressions: &function.expressions,
        locals: function.locals.iter().copied().map(Some).collect(),
        span,
    };
    verifier.expressions()?;
    verifier.statements(&function.body, function.result)?;
    for &clause in function.requires.iter().chain(&function.ensures) {
        compatible(hir, verifier.ty(clause)?, TyId::BOOL, span)?;
    }
    Ok(())
}

fn validate_signature(hir: &hir::Program, ty: TyId, function: &Function) -> Result<(), Error> {
    valid_type(hir, ty, function.span)?;
    let Ty::Function { parameters, result } = hir.types.get(ty) else {
        return Err(invalid(
            "constant declaration is not a function",
            function.span,
        ));
    };
    ensure(
        parameters.len() == function.parameters.len(),
        "constant function signature arity mismatch",
        function.span,
    )?;
    for (&declared, &actual) in parameters.iter().zip(&function.parameters) {
        compatible(hir, actual, declared, function.span)?;
    }
    compatible(hir, function.result, *result, function.span)
}

fn validate_global(
    hir: &hir::Program,
    definition: hir::DefId,
    global: &Global,
) -> Result<(), Error> {
    ensure(
        definition == global.definition,
        "constant global key mismatch",
        global.span,
    )?;
    owner(hir, definition, global.span)?;
    valid_type(hir, global.ty, global.span)?;
    let declaration = &hir.definitions[definition];
    ensure(
        declaration.kind == hir::DefinitionKind::Global,
        "constant initializer has no global declaration",
        global.span,
    )?;
    compatible(hir, global.ty, declaration.ty, global.span)?;
    let verifier = Body {
        hir,
        expressions: &global.expressions,
        locals: Vec::new(),
        span: global.span,
    };
    verifier.expressions()?;
    compatible(
        hir,
        verifier.ty(global.initializer)?,
        global.ty,
        global.span,
    )
}

pub(super) fn expression_body(
    hir: &hir::Program,
    expressions: &[Expr],
    root: ExprId,
    locals: &[Option<Value>],
) -> Result<(), Error> {
    let span = expressions
        .get(root.0 as usize)
        .map_or(Span::new(crate::source::FileId(0), 0, 0), |expression| {
            expression.span
        });
    let verifier = Body {
        hir,
        expressions,
        locals: locals
            .iter()
            .map(|value| value.as_ref().map(|value| value.ty))
            .collect(),
        span,
    };
    verifier.expressions()?;
    verifier.ty(root)?;
    for value in locals.iter().flatten() {
        valid_value(hir, value, span)?;
    }
    Ok(())
}

struct Body<'a> {
    hir: &'a hir::Program,
    expressions: &'a [Expr],
    locals: Vec<Option<TyId>>,
    span: Span,
}
impl Body<'_> {
    fn ty(&self, id: ExprId) -> Result<TyId, Error> {
        self.expressions
            .get(id.0 as usize)
            .map(|expression| expression.ty)
            .ok_or_else(|| invalid("invalid constant expression ID", self.span))
    }
    fn expressions(&self) -> Result<(), Error> {
        ensure(
            self.expressions.len() <= LIMIT && self.locals.len() <= LIMIT,
            "constant arena resource limit exceeded",
            self.span,
        )?;
        let mut depths = Vec::<usize>::with_capacity(self.expressions.len());
        for (index, expression) in self.expressions.iter().enumerate() {
            valid_type(self.hir, expression.ty, expression.span)?;
            let mut depth = 1;
            for child in children(&expression.kind) {
                // Typed constant expressions are emitted child-first. Requiring
                // this prevents cycles and bounds recursive evaluation depth.
                ensure(
                    (child.0 as usize) < index,
                    "constant expression is cyclic or has a forward child",
                    expression.span,
                )?;
                depth = depth.max(depths[child.0 as usize] + 1);
            }
            ensure(
                depth <= 128,
                "constant expression nesting limit exceeded",
                expression.span,
            )?;
            depths.push(depth);
            self.expression(expression)?;
        }
        Ok(())
    }
    fn expression(&self, expression: &Expr) -> Result<(), Error> {
        let span = expression.span;
        match &expression.kind {
            ExprKind::IntegerBound { .. } => ensure(
                self.hir.types.integer(expression.ty),
                "integer bound has noninteger type",
                span,
            ),
            ExprKind::Value(value) => {
                valid_value(self.hir, value, span)?;
                compatible(self.hir, value.ty, expression.ty, span)
            }
            ExprKind::Local(local) => {
                let local = self
                    .locals
                    .get(*local as usize)
                    .ok_or_else(|| invalid("constant expression has invalid local ID", span))?;
                if let Some(ty) = local {
                    compatible(self.hir, *ty, expression.ty, span)?;
                }
                Ok(())
            }
            ExprKind::Global(definition) => {
                let global = self.hir.constants.globals.get(definition).ok_or_else(|| {
                    invalid("constant expression references an unchecked global", span)
                })?;
                compatible(self.hir, global.ty, expression.ty, span)
            }
            ExprKind::ConstParameter {
                owner: definition,
                index,
            } => {
                owner(self.hir, *definition, span)?;
                ensure(
                    self.hir
                        .types
                        .generic_parameters(*definition)
                        .get(*index as usize)
                        .is_some_and(|(_, kind)| *kind == crate::types::GenericParamKind::Const),
                    "invalid constant parameter slot",
                    span,
                )
            }
            ExprKind::Unary { op, operand } => self.unary(*op, *operand, expression.ty, span),
            ExprKind::Binary { op, left, right } => {
                self.binary(*op, *left, *right, expression.ty, span)
            }
            ExprKind::Call {
                function,
                generics,
                arguments,
            } => self.call(*function, generics, arguments, expression.ty, span),
            ExprKind::Old(value) => compatible(self.hir, self.ty(*value)?, expression.ty, span),
            ExprKind::Result => Ok(()),
            ExprKind::Array(_) | ExprKind::Repeat { .. } | ExprKind::Index { .. } => {
                self.aggregate(expression)
            }
        }
    }
    fn aggregate(&self, expression: &Expr) -> Result<(), Error> {
        let span = expression.span;
        match &expression.kind {
            ExprKind::Array(values) => self.array(values, expression.ty, span),
            ExprKind::Repeat { value, count } => {
                ensure(
                    matches!(
                        self.hir.types.get(self.ty(*count)?),
                        Ty::Integer {
                            signed: false,
                            bits: 0
                        }
                    ),
                    "constant repeat count is not usize",
                    span,
                )?;
                let Ty::Array { inner, .. } = *self.hir.types.get(expression.ty) else {
                    return Err(invalid("constant repeat requires array type", span));
                };
                compatible(self.hir, self.ty(*value)?, inner, span)
            }
            ExprKind::Index { base, index } => {
                ensure(
                    matches!(
                        self.hir.types.get(self.ty(*index)?),
                        Ty::Integer {
                            signed: false,
                            bits: 0
                        }
                    ),
                    "constant index is not usize",
                    span,
                )?;
                let Ty::Array { inner, .. } = *self.hir.types.get(self.ty(*base)?) else {
                    return Err(invalid("constant index base is not an array", span));
                };
                compatible(self.hir, inner, expression.ty, span)
            }
            _ => unreachable!("aggregate expression dispatch"),
        }
    }
    fn unary(&self, op: UnaryOp, operand: ExprId, output: TyId, span: Span) -> Result<(), Error> {
        let input = self.ty(operand)?;
        compatible(self.hir, input, output, span)?;
        ensure(
            match op {
                UnaryOp::Not => input == TyId::BOOL,
                UnaryOp::Positive | UnaryOp::Negate | UnaryOp::BitNot => {
                    self.hir.types.integer(input)
                }
                _ => false,
            },
            "invalid constant unary operation",
            span,
        )
    }
    fn binary(
        &self,
        op: BinaryOp,
        left: ExprId,
        right: ExprId,
        output: TyId,
        span: Span,
    ) -> Result<(), Error> {
        let left = self.ty(left)?;
        compatible(self.hir, left, self.ty(right)?, span)?;
        let valid = match op {
            BinaryOp::And | BinaryOp::Or => left == TyId::BOOL && output == TyId::BOOL,
            BinaryOp::Equal | BinaryOp::NotEqual => {
                output == TyId::BOOL
                    && (self.hir.types.integer(left)
                        || matches!(self.hir.types.get(left), Ty::Bool | Ty::Char))
            }
            BinaryOp::Less | BinaryOp::LessEqual | BinaryOp::Greater | BinaryOp::GreaterEqual => {
                output == TyId::BOOL && self.hir.types.integer(left)
            }
            _ => self.hir.types.integer(left) && left == output,
        };
        ensure(valid, "invalid constant binary operation", span)
    }
    fn call(
        &self,
        definition: hir::DefId,
        generics: &[GenericArg],
        arguments: &[ExprId],
        output: TyId,
        span: Span,
    ) -> Result<(), Error> {
        let function = self
            .hir
            .constants
            .functions
            .get(&definition)
            .ok_or_else(|| invalid("constant call has no checked source body", span))?;
        ensure(
            function.parameters.len() == arguments.len(),
            "constant call argument count mismatch",
            span,
        )?;
        let kinds = &self.hir.definitions[definition].generic_parameter_kinds;
        ensure(
            generics.len() == kinds.len(),
            "constant call generic argument count mismatch",
            span,
        )?;
        for (&argument, &kind) in generics.iter().zip(kinds) {
            ensure(
                argument.kind() == kind,
                "constant call generic argument kind mismatch",
                span,
            )?;
            self.hir
                .types
                .validate_generic_arg(argument)
                .map_err(|error| invalid(error.to_string(), span))?;
        }
        for (&argument, &parameter) in arguments.iter().zip(&function.parameters) {
            let expected = self.instantiated_scalar(parameter, definition, generics, span)?;
            compatible(self.hir, self.ty(argument)?, expected, span)?;
        }
        compatible(
            self.hir,
            output,
            self.instantiated_scalar(function.result, definition, generics, span)?,
            span,
        )?;
        Ok(())
    }
    fn instantiated_scalar(
        &self,
        ty: TyId,
        owner: hir::DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> Result<TyId, Error> {
        if let Ty::Parameter {
            owner: found,
            index,
        } = self.hir.types.get(ty)
            && *found == owner
        {
            return arguments
                .get(*index as usize)
                .copied()
                .and_then(GenericArg::ty)
                .ok_or_else(|| {
                    invalid(
                        "constant callable type parameter lacks a type argument",
                        span,
                    )
                });
        }
        Ok(ty)
    }
    fn array(&self, values: &[ExprId], ty: TyId, span: Span) -> Result<(), Error> {
        let Ty::Array { inner, length } = *self.hir.types.get(ty) else {
            return Err(invalid("constant data expression is not an array", span));
        };
        ensure(
            values.len() as u64 == length,
            "constant array length mismatch",
            span,
        )?;
        for &value in values {
            compatible(self.hir, self.ty(value)?, inner, span)?;
        }
        Ok(())
    }
    fn statements(&self, statements: &[Statement], result: TyId) -> Result<(), Error> {
        let mut pending: Vec<_> = statements.iter().map(|statement| (statement, 0)).collect();
        let mut remaining = LIMIT;
        while let Some((statement, depth)) = pending.pop() {
            ensure(
                depth < 128 && remaining > 0,
                "constant statement depth/work limit exceeded",
                statement.span,
            )?;
            remaining -= 1;
            self.statement(statement, result, depth, &mut pending)?;
        }
        Ok(())
    }
    fn statement<'a>(
        &self,
        statement: &'a Statement,
        result: TyId,
        depth: usize,
        pending: &mut Vec<(&'a Statement, usize)>,
    ) -> Result<(), Error> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Declare { local, value } => {
                let ty = self
                    .locals
                    .get(*local as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(|| invalid("invalid constant declaration local", span))?;
                if let Some(value) = value {
                    compatible(self.hir, self.ty(*value)?, ty, span)?;
                }
            }
            StatementKind::Assign { local, value, .. } => {
                let ty = self
                    .locals
                    .get(*local as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(|| invalid("invalid constant assignment local", span))?;
                compatible(self.hir, self.ty(*value)?, ty, span)?;
            }
            StatementKind::Evaluate(value) => {
                self.ty(*value)?;
            }
            StatementKind::Return(value) => compatible(
                self.hir,
                value
                    .map(|value| self.ty(value))
                    .transpose()?
                    .unwrap_or(TyId::VOID),
                result,
                span,
            )?,
            StatementKind::Block(_)
            | StatementKind::If { .. }
            | StatementKind::While { .. }
            | StatementKind::For { .. } => self.control_statement(statement, depth, pending)?,
            StatementKind::Assert { condition, .. } => {
                compatible(self.hir, self.ty(*condition)?, TyId::BOOL, span)?
            }
            StatementKind::Break | StatementKind::Continue => {}
        }
        Ok(())
    }
    fn control_statement<'a>(
        &self,
        statement: &'a Statement,
        depth: usize,
        pending: &mut Vec<(&'a Statement, usize)>,
    ) -> Result<(), Error> {
        let span = statement.span;
        match &statement.kind {
            StatementKind::Block(body) => {
                pending.extend(body.iter().map(|statement| (statement, depth + 1)))
            }
            StatementKind::If { condition, yes, no } => {
                compatible(self.hir, self.ty(*condition)?, TyId::BOOL, span)?;
                pending.extend(yes.iter().chain(no).map(|statement| (statement, depth + 1)));
            }
            StatementKind::While { condition, body } => {
                compatible(self.hir, self.ty(*condition)?, TyId::BOOL, span)?;
                pending.extend(body.iter().map(|statement| (statement, depth + 1)));
            }
            StatementKind::For {
                initialize,
                condition,
                update,
                body,
            } => {
                if let Some(condition) = condition {
                    compatible(self.hir, self.ty(*condition)?, TyId::BOOL, span)?;
                }
                pending.extend(
                    initialize
                        .iter()
                        .chain(update)
                        .chain(body)
                        .map(|statement| (statement, depth + 1)),
                );
            }
            _ => unreachable!("control statement dispatch"),
        }
        Ok(())
    }
}

pub(super) fn valid_value(hir: &hir::Program, root: &Value, span: Span) -> Result<(), Error> {
    let mut pending = vec![(root, 0)];
    let mut remaining = LIMIT;
    while let Some((value, depth)) = pending.pop() {
        ensure(
            depth < 128 && remaining > 0,
            "constant data nesting/work limit exceeded",
            span,
        )?;
        remaining -= 1;
        valid_type(hir, value.ty, span)?;
        let valid = match (&value.kind, hir.types.get(value.ty)) {
            (ValueKind::Integer { .. }, Ty::Integer { .. })
            | (ValueKind::Bool(_), Ty::Bool)
            | (ValueKind::Char(_), Ty::Char)
            | (ValueKind::Unit, Ty::Void) => true,
            (ValueKind::FloatBits(bits), Ty::Float { bits: width }) => {
                let value = f64::from_bits(*bits);
                value.is_finite()
                    && (*width == 64 || *width == 32 && f64::from(value as f32).to_bits() == *bits)
            }
            (
                ValueKind::String(_),
                Ty::Reference {
                    mutable: false,
                    inner,
                    ..
                },
            ) => *inner == TyId::STR,
            (ValueKind::Array(values), Ty::Array { inner, length }) => {
                for value in values {
                    compatible(hir, value.ty, *inner, span)?;
                }
                ensure(
                    pending.len().saturating_add(values.len()) <= LIMIT,
                    "constant data traversal limit exceeded",
                    span,
                )?;
                pending.extend(values.iter().map(|value| (value, depth + 1)));
                values.len() as u64 == *length
            }
            _ => false,
        };
        ensure(
            valid,
            "constant data does not match its declared type",
            span,
        )?;
    }
    Ok(())
}
fn children(kind: &ExprKind) -> Vec<ExprId> {
    match kind {
        ExprKind::Unary { operand, .. } | ExprKind::Old(operand) => vec![*operand],
        ExprKind::Binary { left, right, .. } => vec![*left, *right],
        ExprKind::Call { arguments, .. } | ExprKind::Array(arguments) => arguments.clone(),
        ExprKind::Repeat { value, count } => vec![*value, *count],
        ExprKind::Index { base, index } => vec![*base, *index],
        _ => Vec::new(),
    }
}
fn owner(hir: &hir::Program, definition: hir::DefId, span: Span) -> Result<(), Error> {
    ensure(
        (definition.0 as usize) < hir.definitions.len(),
        "invalid constant definition ID",
        span,
    )
}
fn valid_type(hir: &hir::Program, ty: TyId, span: Span) -> Result<(), Error> {
    ensure(
        ty != TyId::ERROR && (ty.0 as usize) < hir.types.values().len(),
        "invalid constant type ID",
        span,
    )
}
fn compatible(hir: &hir::Program, actual: TyId, expected: TyId, span: Span) -> Result<(), Error> {
    valid_type(hir, actual, span)?;
    valid_type(hir, expected, span)?;
    ensure(
        hir.types.compatible(actual, expected),
        "constant IR type mismatch",
        span,
    )
}
fn ensure(valid: bool, message: &str, span: Span) -> Result<(), Error> {
    if valid {
        Ok(())
    } else {
        Err(invalid(message, span))
    }
}
fn invalid(message: impl Into<String>, span: Span) -> Error {
    Error::new("E-CONST-CONTEXT", message, span)
}
