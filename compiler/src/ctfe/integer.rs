use super::*;
use crate::types::{Ty, TypeContext};

#[derive(Clone, Copy)]
struct Integer {
    signed: bool,
    bits: u16,
}
impl Integer {
    fn of(types: &TypeContext, ty: TyId, pointer_bits: u16, span: Span) -> Result<Self, Error> {
        let Ty::Integer { signed, bits } = types.get(ty) else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "constant operation requires an integer",
                span,
            ));
        };
        let bits = if *bits == 0 { pointer_bits } else { *bits };
        if !matches!(bits, 8 | 16 | 32 | 64 | 128) {
            return Err(Error::new(
                "E-CONST-EVAL",
                "unsupported target integer width",
                span,
            ));
        }
        Ok(Self {
            signed: *signed,
            bits,
        })
    }
    fn mask(self) -> u128 {
        u128::MAX >> (128 - self.bits)
    }
    fn encode(self, value: &Value, span: Span) -> Result<u128, Error> {
        let ValueKind::Integer {
            magnitude,
            negative,
        } = value.kind
        else {
            return Err(invalid(span));
        };
        let limit = if self.signed {
            (1u128 << (self.bits - 1)) - u128::from(!negative)
        } else {
            self.mask()
        };
        if magnitude > limit || negative && !self.signed {
            return Err(overflow(span));
        }
        Ok(if negative {
            (!magnitude).wrapping_add(1) & self.mask()
        } else {
            magnitude
        })
    }
    fn decode(self, bits: u128, ty: TyId) -> Value {
        let negative = self.signed && bits & (1u128 << (self.bits - 1)) != 0;
        let magnitude = if negative {
            (!bits).wrapping_add(1) & self.mask()
        } else {
            bits
        };
        Value {
            ty,
            kind: ValueKind::Integer {
                magnitude,
                negative,
            },
        }
    }
    fn signed_value(self, bits: u128) -> i128 {
        if self.bits == 128 {
            bits as i128
        } else {
            ((bits << (128 - self.bits)) as i128) >> (128 - self.bits)
        }
    }
    fn checked_signed(self, value: i128, ty: TyId, span: Span) -> Result<Value, Error> {
        let result = Value {
            ty,
            kind: ValueKind::Integer {
                magnitude: value.unsigned_abs(),
                negative: value < 0,
            },
        };
        self.encode(&result, span)?;
        Ok(result)
    }
    fn checked_unsigned(self, value: u128, ty: TyId, span: Span) -> Result<Value, Error> {
        if value > self.mask() {
            return Err(overflow(span));
        }
        Ok(self.decode(value, ty))
    }
}

fn overflow(span: Span) -> Error {
    Error::new(
        "E-CONST-EVAL",
        "constant integer operation overflows its target type",
        span,
    )
}
fn invalid(span: Span) -> Error {
    Error::new("E-CONST-EVAL", "invalid typed constant operand", span)
}

pub(super) fn validate(
    types: &TypeContext,
    value: &Value,
    pointer_bits: u16,
    span: Span,
) -> Result<(), Error> {
    if matches!(value.kind, ValueKind::Integer { .. }) {
        Integer::of(types, value.ty, pointer_bits, span)?.encode(value, span)?;
    }
    Ok(())
}

pub(super) fn bound(
    types: &TypeContext,
    ty: TyId,
    maximum: bool,
    pointer_bits: u16,
    span: Span,
) -> Result<Value, Error> {
    let integer = Integer::of(types, ty, pointer_bits, span)?;
    let (magnitude, negative) = match (integer.signed, maximum) {
        (true, true) => ((1u128 << (integer.bits - 1)) - 1, false),
        (true, false) => (1u128 << (integer.bits - 1), true),
        (false, true) => (integer.mask(), false),
        (false, false) => (0, false),
    };
    Ok(Value {
        ty,
        kind: ValueKind::Integer {
            magnitude,
            negative,
        },
    })
}

pub(super) fn unary(
    types: &TypeContext,
    op: UnaryOp,
    value: Value,
    pointer_bits: u16,
    span: Span,
) -> Result<Value, Error> {
    if op == UnaryOp::Not {
        let Some(value) = value.boolean() else {
            return Err(invalid(span));
        };
        return Ok(Value {
            ty: TyId::BOOL,
            kind: ValueKind::Bool(!value),
        });
    }
    let integer = Integer::of(types, value.ty, pointer_bits, span)?;
    let bits = integer.encode(&value, span)?;
    match op {
        UnaryOp::Positive => Ok(value),
        UnaryOp::BitNot => Ok(integer.decode(!bits & integer.mask(), value.ty)),
        UnaryOp::Negate if integer.signed => {
            let result = integer
                .signed_value(bits)
                .checked_neg()
                .ok_or_else(|| overflow(span))?;
            integer.checked_signed(result, value.ty, span)
        }
        UnaryOp::Negate if bits == 0 => Ok(value),
        UnaryOp::Negate => Err(overflow(span)),
        _ => Err(Error::new(
            "E-CONST-CONTEXT",
            "operation is not available during constant evaluation",
            span,
        )),
    }
}

pub(super) fn binary(
    types: &TypeContext,
    op: BinaryOp,
    left: Value,
    right: Value,
    pointer_bits: u16,
    span: Span,
) -> Result<Value, Error> {
    if left.ty != right.ty {
        return Err(invalid(span));
    }
    if let Some(value) = scalar_comparison(op, &left.kind, &right.kind) {
        return Ok(Value {
            ty: TyId::BOOL,
            kind: ValueKind::Bool(value),
        });
    }
    let integer = Integer::of(types, left.ty, pointer_bits, span)?;
    let a = integer.encode(&left, span)?;
    let b = integer.encode(&right, span)?;
    if let Some(value) = comparison(integer, op, a, b) {
        return Ok(Value {
            ty: TyId::BOOL,
            kind: ValueKind::Bool(value),
        });
    }
    match op {
        BinaryOp::BitAnd => Ok(integer.decode(a & b, left.ty)),
        BinaryOp::BitOr => Ok(integer.decode(a | b, left.ty)),
        BinaryOp::BitXor => Ok(integer.decode(a ^ b, left.ty)),
        BinaryOp::ShiftLeft | BinaryOp::ShiftRight => shift(integer, op, a, b, left.ty, span),
        _ if integer.signed => signed(integer, op, a, b, left.ty, span),
        _ => unsigned(integer, op, a, b, left.ty, span),
    }
}

fn scalar_comparison(op: BinaryOp, left: &ValueKind, right: &ValueKind) -> Option<bool> {
    let equal = match (left, right) {
        (ValueKind::Bool(a), ValueKind::Bool(b)) => a == b,
        (ValueKind::Char(a), ValueKind::Char(b)) => a == b,
        _ => return None,
    };
    match op {
        BinaryOp::Equal => Some(equal),
        BinaryOp::NotEqual => Some(!equal),
        _ => None,
    }
}

fn comparison(integer: Integer, op: BinaryOp, a: u128, b: u128) -> Option<bool> {
    let order = if integer.signed {
        integer.signed_value(a).cmp(&integer.signed_value(b))
    } else {
        a.cmp(&b)
    };
    Some(match op {
        BinaryOp::Equal => order.is_eq(),
        BinaryOp::NotEqual => !order.is_eq(),
        BinaryOp::Less => order.is_lt(),
        BinaryOp::LessEqual => !order.is_gt(),
        BinaryOp::Greater => order.is_gt(),
        BinaryOp::GreaterEqual => !order.is_lt(),
        _ => return None,
    })
}

fn shift(
    integer: Integer,
    op: BinaryOp,
    a: u128,
    b: u128,
    ty: TyId,
    span: Span,
) -> Result<Value, Error> {
    if b >= u128::from(integer.bits) {
        return Err(Error::new(
            "E-CONST-EVAL",
            "constant shift is negative or exceeds the target width",
            span,
        ));
    }
    let value = if op == BinaryOp::ShiftLeft {
        (a << b) & integer.mask()
    } else if integer.signed {
        (integer.signed_value(a) >> b) as u128 & integer.mask()
    } else {
        a >> b
    };
    Ok(integer.decode(value, ty))
}

fn signed(
    integer: Integer,
    op: BinaryOp,
    a: u128,
    b: u128,
    ty: TyId,
    span: Span,
) -> Result<Value, Error> {
    let a = integer.signed_value(a);
    let b = integer.signed_value(b);
    let value = match op {
        BinaryOp::Add => a.checked_add(b),
        BinaryOp::Subtract => a.checked_sub(b),
        BinaryOp::Multiply => a.checked_mul(b),
        BinaryOp::Divide => a.checked_div(b),
        BinaryOp::Remainder => a.checked_rem(b),
        _ => return Err(invalid(span)),
    }
    .ok_or_else(|| arithmetic_error(op, b == 0, span))?;
    // MIN / -1 is invalid at the target width even when host i128 can hold it.
    let minimum = if integer.bits == 128 {
        i128::MIN
    } else {
        -(1i128 << (integer.bits - 1))
    };
    if matches!(op, BinaryOp::Divide | BinaryOp::Remainder) && a == minimum && b == -1 {
        return Err(overflow(span));
    }
    integer.checked_signed(value, ty, span)
}

fn unsigned(
    integer: Integer,
    op: BinaryOp,
    a: u128,
    b: u128,
    ty: TyId,
    span: Span,
) -> Result<Value, Error> {
    let value = match op {
        BinaryOp::Add => a.checked_add(b),
        BinaryOp::Subtract => a.checked_sub(b),
        BinaryOp::Multiply => a.checked_mul(b),
        BinaryOp::Divide => a.checked_div(b),
        BinaryOp::Remainder => a.checked_rem(b),
        _ => return Err(invalid(span)),
    }
    .ok_or_else(|| arithmetic_error(op, b == 0, span))?;
    integer.checked_unsigned(value, ty, span)
}

fn arithmetic_error(op: BinaryOp, zero: bool, span: Span) -> Error {
    if zero && matches!(op, BinaryOp::Divide | BinaryOp::Remainder) {
        Error::new(
            "E-CONST-EVAL",
            "division or remainder by zero in constant expression",
            span,
        )
    } else {
        overflow(span)
    }
}
