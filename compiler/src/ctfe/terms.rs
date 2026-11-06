use super::eval::{Binding, Bindings, Evaluator};
use super::*;
use crate::types::{ConstId, ConstKind, ConstValue, Ty};

pub fn evaluate_term(
    program: &mut hir::Program,
    term: ConstId,
    limits: Limits,
) -> Result<ConstId, Error> {
    require_type_target(program, limits)?;
    program.constants.validate(program)?;
    let value = Evaluator::new(program, limits).term(term, &Bindings::default(), 0)?;
    match value.kind {
        ValueKind::Bool(value) => Ok(program.types.const_bool(value)),
        ValueKind::Integer {
            magnitude,
            negative: false,
        } => {
            if !matches!(
                program.types.get(value.ty),
                Ty::Integer {
                    signed: false,
                    bits: 0
                }
            ) {
                return Err(Error::new(
                    "E-CONST-CONTEXT",
                    "type-level integer value must have usize type",
                    fallback(program),
                ));
            }
            let value = magnitude.try_into().map_err(|_| {
                Error::new(
                    "E-CONST-EVAL",
                    "constant term does not fit target usize",
                    fallback(program),
                )
            })?;
            Ok(program.types.const_value(value))
        }
        _ => Err(Error::new(
            "E-CONST-CONTEXT",
            "type-level constants require usize or bool values",
            fallback(program),
        )),
    }
}

pub fn check_assertions(
    program: &mut hir::Program,
    owner: hir::DefId,
    arguments: &[GenericArg],
    limits: Limits,
) -> Result<(), Error> {
    require_type_target(program, limits)?;
    let assertions: Vec<_> = program
        .constants
        .assertions
        .iter()
        .filter(|assertion| assertion.owner == owner)
        .cloned()
        .collect();
    for assertion in assertions {
        let term = program
            .types
            .const_substitute(assertion.condition, owner, arguments)
            .map_err(|error| Error::new("E-CONST-EVAL", error.to_string(), assertion.span))?;
        let term = evaluate_term(program, term, limits)?;
        if !matches!(
            program.types.const_term(term).kind,
            ConstKind::Value(ConstValue::Bool(true))
        ) {
            return Err(Error::new(
                "E-CONST-ASSERT",
                assertion.message,
                assertion.span,
            ));
        }
    }
    Ok(())
}

fn fallback(program: &hir::Program) -> Span {
    program
        .definitions
        .first()
        .map_or(Span::new(crate::source::FileId(0), 0, 0), |definition| {
            definition.span
        })
}

fn require_type_target(program: &hir::Program, limits: Limits) -> Result<(), Error> {
    // TypeContext's symbolic normalization is currently fixed to Cavo's supported
    // 64-bit targets. A folded term cannot be silently reinterpreted for a new ABI.
    if limits.pointer_bits != 64 {
        return Err(Error::new(
            "E-CONST-CONTEXT",
            "type-level constant queries require the program's 64-bit target",
            fallback(program),
        ));
    }
    Ok(())
}

impl Evaluator<'_> {
    pub(super) fn assertions(
        &mut self,
        owner: hir::DefId,
        bindings: &Bindings,
    ) -> Result<(), Error> {
        for assertion in &self.program.constants.assertions {
            if assertion.owner == owner
                && self.term(assertion.condition, bindings, 0)?.boolean() != Some(true)
            {
                return Err(Error::new(
                    "E-CONST-ASSERT",
                    &assertion.message,
                    assertion.span,
                ));
            }
        }
        Ok(())
    }
    pub(super) fn resolve_bindings(
        &mut self,
        owner: hir::DefId,
        arguments: &[GenericArg],
        outer: &Bindings,
    ) -> Result<Bindings, Error> {
        if self.limits.pointer_bits != 64
            && arguments
                .iter()
                .any(|argument| matches!(argument, GenericArg::Const(_)))
        {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant generic arguments require the program's 64-bit target",
                fallback(self.program),
            ));
        }
        let declaration = self
            .program
            .definitions
            .get(owner.0 as usize)
            .ok_or_else(|| {
                Error::new(
                    "E-CONST-CONTEXT",
                    "invalid constant callable definition",
                    fallback(self.program),
                )
            })?;
        if declaration.generic_parameter_kinds.len() != arguments.len()
            || declaration
                .generic_parameter_kinds
                .iter()
                .zip(arguments)
                .any(|(kind, argument)| *kind != argument.kind())
        {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant call generic arguments do not match declaration",
                declaration.span,
            ));
        }
        let mut values = Vec::with_capacity(arguments.len());
        for &argument in arguments {
            values.push(self.argument_binding(argument, outer, declaration.span)?);
        }
        Ok(Bindings {
            owner: Some(owner),
            values,
        })
    }
    fn argument_binding(
        &mut self,
        argument: GenericArg,
        outer: &Bindings,
        span: Span,
    ) -> Result<Binding, Error> {
        Ok(match argument {
            GenericArg::Type(ty) => Binding::Type(self.bound_type(ty, outer)),
            GenericArg::Lifetime(region) => Binding::Lifetime(region),
            GenericArg::Const(term) => {
                let value = self.term(term, outer, 0)?;
                if !matches!(
                    self.program.types.get(value.ty),
                    Ty::Integer {
                        signed: false,
                        bits: 0
                    }
                ) {
                    return Err(Error::new(
                        "E-CONST-CONTEXT",
                        "constant generic argument must have usize type",
                        span,
                    ));
                }
                Binding::Const(value)
            }
        })
    }

    pub(super) fn term(
        &mut self,
        id: ConstId,
        bindings: &Bindings,
        depth: usize,
    ) -> Result<Value, Error> {
        let span = fallback(self.program);
        if depth >= 128 {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant term nesting limit exceeded",
                span,
            ));
        }
        self.charge(1, 0, span)?;
        let term = self
            .program
            .types
            .constant_terms()
            .get(id.0 as usize)
            .ok_or_else(|| Error::new("E-CONST-CONTEXT", "invalid constant term ID", span))?;
        let value = self.term_value(term, bindings, depth, span)?;
        if !self.program.types.compatible(value.ty, term.ty) {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant term result type mismatch",
                span,
            ));
        }
        integer::validate(&self.program.types, &value, self.limits.pointer_bits, span)?;
        Ok(value)
    }
    fn term_value(
        &mut self,
        term: &crate::types::ConstTerm,
        bindings: &Bindings,
        depth: usize,
        span: Span,
    ) -> Result<Value, Error> {
        match &term.kind {
            ConstKind::Value(ConstValue::Usize(value)) => Ok(Value {
                ty: term.ty,
                kind: ValueKind::Integer {
                    magnitude: u128::from(*value),
                    negative: false,
                },
            }),
            ConstKind::Value(ConstValue::Bool(value)) => Ok(Value {
                ty: TyId::BOOL,
                kind: ValueKind::Bool(*value),
            }),
            ConstKind::Parameter { owner, index } => {
                self.constant_parameter(*owner, *index, bindings, span)
            }
            ConstKind::Global(definition) => self.global(*definition),
            ConstKind::Unary { op, operand } => {
                let value = self.term(*operand, bindings, depth + 1)?;
                integer::unary(
                    &self.program.types,
                    *op,
                    value,
                    self.limits.pointer_bits,
                    span,
                )
            }
            ConstKind::Binary { op, left, right } => {
                self.term_binary(*op, *left, *right, bindings, depth, span)
            }
            ConstKind::Call {
                definition,
                type_arguments,
                arguments,
            } => {
                let called = self.resolve_bindings(*definition, type_arguments, bindings)?;
                let mut values = Vec::with_capacity(arguments.len());
                for &argument in arguments {
                    values.push(self.term(argument, bindings, depth + 1)?);
                }
                self.invoke(*definition, called, values)
            }
        }
    }
    fn term_binary(
        &mut self,
        op: BinaryOp,
        left: ConstId,
        right: ConstId,
        bindings: &Bindings,
        depth: usize,
        span: Span,
    ) -> Result<Value, Error> {
        let left = self.term(left, bindings, depth + 1)?;
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            let value = left.boolean().ok_or_else(|| {
                Error::new("E-CONST-CONTEXT", "constant logic requires bool", span)
            })?;
            if value == (op == BinaryOp::Or) {
                return Ok(left);
            }
            return self.term(right, bindings, depth + 1);
        }
        let right = self.term(right, bindings, depth + 1)?;
        integer::binary(
            &self.program.types,
            op,
            left,
            right,
            self.limits.pointer_bits,
            span,
        )
    }
}
