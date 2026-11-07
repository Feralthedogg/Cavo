use super::*;
use cavo_compiler::syntax::ast::{BinaryOp as B, UnaryOp as U};

impl Machine<'_> {
    pub(super) fn unary(&self, op: U, value: Value) -> Result<Value> {
        let ty = value.ty;
        if let ValueKind::FloatBits(bits) = value.kind {
            let number = self.float(ty, bits);
            return Ok(self.float_value(ty, if op == U::Negate { -number } else { number }));
        }
        let bits = value.unsigned()?;
        let (width, signed) = self.integer_type(ty)?;
        let mask = mask(width);
        let value = match op {
            U::Positive => bits & mask,
            U::Not => return Ok(Value::boolean(!value.boolean_value()?)),
            U::BitNot => !bits & mask,
            U::Negate if signed => {
                let result = signed_value(bits, width)
                    .checked_neg()
                    .ok_or(Error::Trap("integer overflow"))?;
                signed_bits(result, width)?
            }
            U::Negate if bits & mask == 0 => 0,
            _ => return Err(Error::Trap("invalid unary arithmetic")),
        };
        Ok(Value::bits(ty, value))
    }

    pub(super) fn binary(&self, op: B, left: Value, right: Value) -> Result<Value> {
        if let Some(value) = self.non_integer(op, &left, &right) {
            return value;
        }
        let (width, signed) = self.integer_type(left.ty)?;
        let a = left.unsigned()? & mask(width);
        let b = right.unsigned()? & mask(width);
        if let Some(result) = comparison(
            op,
            if signed {
                signed_value(a, width).cmp(&signed_value(b, width))
            } else {
                a.cmp(&b)
            },
        ) {
            return Ok(Value::boolean(result));
        }
        if matches!(op, B::And | B::Or) {
            let a = left.boolean_value()?;
            let b = right.boolean_value()?;
            return Ok(Value::boolean(if op == B::And { a && b } else { a || b }));
        }
        let bits = match op {
            B::BitAnd => a & b,
            B::BitOr => a | b,
            B::BitXor => a ^ b,
            B::ShiftLeft | B::ShiftRight => shift(op, a, right.unsigned()?, width, signed)?,
            _ if signed => {
                signed_arithmetic(op, signed_value(a, width), signed_value(b, width), width)?
            }
            _ => unsigned_arithmetic(op, a, b, width)?,
        };
        Ok(Value::bits(left.ty, bits))
    }

    fn non_integer(&self, op: B, left: &Value, right: &Value) -> Option<Result<Value>> {
        match (&left.kind, &right.kind) {
            (
                ValueKind::Pointer {
                    data: a,
                    metadata: x,
                },
                ValueKind::Pointer {
                    data: b,
                    metadata: y,
                },
            ) => {
                let same = match (a, b) {
                    (Some(a), Some(b)) => a.same_address(b),
                    (None, None) => true,
                    _ => false,
                } && x == y;
                Some(match op {
                    B::Equal => Ok(Value::boolean(same)),
                    B::NotEqual => Ok(Value::boolean(!same)),
                    _ => Err(Error::Unsupported("pointer ordering")),
                })
            }
            (ValueKind::Function(a), ValueKind::Function(b)) => Some(match op {
                B::Equal => Ok(Value::boolean(a == b)),
                B::NotEqual => Ok(Value::boolean(a != b)),
                _ => Err(Error::Unsupported("function pointer ordering")),
            }),
            (ValueKind::FloatBits(a), ValueKind::FloatBits(b)) => Some(self.float_binary(
                op,
                left.ty,
                self.float(left.ty, *a),
                self.float(right.ty, *b),
            )),
            _ => None,
        }
    }

    pub(super) fn integer_type(&self, ty: TyId) -> Result<(u32, bool)> {
        match self.program.hir.types.get(ty) {
            Ty::Integer { signed, bits } => {
                Ok((if *bits == 0 { 64 } else { (*bits).into() }, *signed))
            }
            Ty::Bool => Ok((8, false)),
            Ty::Char => Ok((32, false)),
            _ => Err(Error::Undefined("non-integer arithmetic type")),
        }
    }

    fn float(&self, ty: TyId, bits: u64) -> f64 {
        if matches!(self.program.hir.types.get(ty), Ty::Float { bits: 32 }) {
            f32::from_bits(bits as u32).into()
        } else {
            f64::from_bits(bits)
        }
    }
    pub(super) fn float_value(&self, ty: TyId, value: f64) -> Value {
        let bits = if matches!(self.program.hir.types.get(ty), Ty::Float { bits: 32 }) {
            (value as f32).to_bits().into()
        } else {
            value.to_bits()
        };
        Value {
            ty,
            kind: ValueKind::FloatBits(bits),
        }
    }
    fn float_binary(&self, op: B, ty: TyId, a: f64, b: f64) -> Result<Value> {
        let value = match op {
            B::Add => a + b,
            B::Subtract => a - b,
            B::Multiply => a * b,
            B::Divide => a / b,
            B::Remainder => a % b,
            B::Equal => return Ok(Value::boolean(a == b)),
            B::NotEqual => return Ok(Value::boolean(a != b)),
            B::Less => return Ok(Value::boolean(a < b)),
            B::LessEqual => return Ok(Value::boolean(a <= b)),
            B::Greater => return Ok(Value::boolean(a > b)),
            B::GreaterEqual => return Ok(Value::boolean(a >= b)),
            _ => return Err(Error::Unsupported("float operator")),
        };
        Ok(self.float_value(ty, value))
    }
}

pub(super) fn mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}
pub(super) fn signed_value(bits: u128, width: u32) -> i128 {
    ((bits & mask(width)) << (128 - width)) as i128 >> (128 - width)
}
fn signed_bits(value: i128, width: u32) -> Result<u128> {
    if width < 128 && (value < -(1i128 << (width - 1)) || value > (1i128 << (width - 1)) - 1) {
        return Err(Error::Trap("integer overflow"));
    }
    Ok(value as u128 & mask(width))
}
fn signed_arithmetic(op: B, a: i128, b: i128, width: u32) -> Result<u128> {
    let value = match op {
        B::Add => a.checked_add(b),
        B::Subtract => a.checked_sub(b),
        B::Multiply => a.checked_mul(b),
        B::Divide => a.checked_div(b),
        B::Remainder => a.checked_rem(b),
        _ => return Err(Error::Unsupported("signed integer operator")),
    }
    .ok_or(Error::Trap("integer overflow or division by zero"))?;
    // Remainder also traps for signed MIN/-1, matching the checked MIR rule.
    let minimum = if width == 128 {
        i128::MIN
    } else {
        -(1i128 << (width - 1))
    };
    if matches!(op, B::Divide | B::Remainder) && a == minimum && b == -1 {
        return Err(Error::Trap("signed division overflow"));
    }
    signed_bits(value, width)
}
fn unsigned_arithmetic(op: B, a: u128, b: u128, width: u32) -> Result<u128> {
    let value = match op {
        B::Add => a.checked_add(b),
        B::Subtract => a.checked_sub(b),
        B::Multiply => a.checked_mul(b),
        B::Divide => a.checked_div(b),
        B::Remainder => a.checked_rem(b),
        _ => return Err(Error::Unsupported("unsigned integer operator")),
    }
    .ok_or(Error::Trap("integer overflow or division by zero"))?;
    if value > mask(width) {
        return Err(Error::Trap("integer overflow"));
    }
    Ok(value)
}
fn shift(op: B, bits: u128, count: u128, width: u32, signed: bool) -> Result<u128> {
    if count >= width.into() {
        return Err(Error::Trap("invalid shift count"));
    }
    let count = count as u32;
    if op == B::ShiftRight {
        return Ok(if signed {
            (signed_value(bits, width) >> count) as u128 & mask(width)
        } else {
            bits >> count
        });
    }
    if signed {
        let value = signed_value(bits, width);
        let result = value.wrapping_shl(count);
        if result >> count != value {
            return Err(Error::Trap("shift overflow"));
        }
        signed_bits(result, width)
    } else {
        let result = bits.wrapping_shl(count);
        if result >> count != bits || result > mask(width) {
            return Err(Error::Trap("shift overflow"));
        }
        Ok(result)
    }
}
fn comparison(op: B, order: std::cmp::Ordering) -> Option<bool> {
    use std::cmp::Ordering::*;
    Some(match op {
        B::Equal => order == Equal,
        B::NotEqual => order != Equal,
        B::Less => order == Less,
        B::LessEqual => order != Greater,
        B::Greater => order == Greater,
        B::GreaterEqual => order != Less,
        _ => return None,
    })
}
