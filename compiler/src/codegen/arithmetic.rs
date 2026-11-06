use super::{body::Emitter, *};
use crate::syntax::ast::{BinaryOp as B, UnaryOp as U};

impl Emitter<'_, '_> {
    pub fn binary(
        &mut self,
        op: B,
        left: &mir::Operand,
        right: &mir::Operand,
    ) -> Result<(TyId, String), Error> {
        let (ty, left) = self.scalar(left)?;
        let (right_ty, mut right) = self.scalar(right)?;
        let llvm = self.module.scalar_type(ty)?;
        let signed = matches!(
            self.module.program.hir.types.get(ty),
            Ty::Integer { signed: true, .. }
        );
        let float = matches!(self.module.program.hir.types.get(ty), Ty::Float { .. });
        if matches!(op, B::ShiftLeft | B::ShiftRight) {
            right = self.resize(right_ty, ty, right)?;
        }
        if let Some(predicate) = comparison(op, signed, float) {
            let value = self.ir.temp(format!(
                "{} {predicate} {llvm} {left}, {right}",
                if float { "fcmp" } else { "icmp" }
            ));
            return Ok((TyId::BOOL, self.ir.temp(format!("zext i1 {value} to i8"))));
        }
        let operation = operation(op, signed, float)
            .ok_or_else(|| self.error("unsupported native scalar operation"))?;
        Ok((
            ty,
            self.ir.temp(format!("{operation} {llvm} {left}, {right}")),
        ))
    }

    pub fn unary(&mut self, op: U, operand: &mir::Operand) -> Result<(TyId, String), Error> {
        let (ty, value) = self.scalar(operand)?;
        let llvm = self.module.scalar_type(ty)?;
        let expression = match op {
            U::Positive | U::Move => return Ok((ty, value)),
            U::Not => format!("xor i8 {value}, 1"),
            U::BitNot => format!("xor {llvm} {value}, -1"),
            U::Negate if matches!(self.module.program.hir.types.get(ty), Ty::Float { .. }) => {
                format!("fneg {llvm} {value}")
            }
            U::Negate => format!("sub {llvm} 0, {value}"),
            _ => {
                return Err(
                    self.error("native unary operation was not lowered to a value or place")
                );
            }
        };
        Ok((ty, self.ir.temp(expression)))
    }

    pub fn checked(
        &mut self,
        value: &mir::Rvalue,
        destination: &mir::Place,
        normal: &str,
        trap: &str,
    ) -> Result<(), Error> {
        let (ty, left, right, op) = match value {
            mir::Rvalue::Binary { op, left, right } => {
                let (ty, left) = self.scalar(left)?;
                let (other, right) = self.scalar(right)?;
                (ty, left, (other, right), *op)
            }
            mir::Rvalue::Unary {
                op: U::Negate,
                operand,
            } => {
                let (ty, right) = self.scalar(operand)?;
                (ty, "0".into(), (ty, right), B::Subtract)
            }
            _ => return Err(self.error("checked MIR operation has no native arithmetic rule")),
        };
        let (bits, signed) = self.integer(ty)?;
        let llvm = format!("i{bits}");
        let (bad, result) = if matches!(op, B::Add | B::Subtract | B::Multiply) {
            self.overflow(op, &llvm, signed, &left, &right.1)?
        } else {
            (self.arithmetic_failure(op, ty, &left, &right)?, None)
        };
        let success = self.ir.fresh("checked_ok");
        self.ir
            .line(format!("br i1 {bad}, label %{trap}, label %{success}"));
        self.ir.start(&success);
        let result = if let Some(result) = result {
            result
        } else {
            let right = self.resize(right.0, ty, right.1)?;
            self.ir.temp(format!(
                "{} {llvm} {left}, {right}",
                operation(op, signed, false)
                    .ok_or_else(|| self.error("invalid checked arithmetic operator"))?
            ))
        };
        let destination = self.address(destination)?;
        self.store_scalar(&destination.pointer, ty, &result)?;
        self.ir.line(format!("br label %{normal}"));
        Ok(())
    }

    pub fn overflow(
        &mut self,
        op: B,
        llvm: &str,
        signed: bool,
        left: &str,
        right: &str,
    ) -> Result<(String, Option<String>), Error> {
        let operation = match op {
            B::Add => "add",
            B::Subtract => "sub",
            B::Multiply => "mul",
            _ => unreachable!("checked overflow operator"),
        };
        let name = format!(
            "__cavo_overflow_{}{operation}_{llvm}",
            if signed { "s" } else { "u" }
        );
        self.module
            .declare(&name, overflow_definition(&name, op, llvm, signed))?;
        let bits = llvm[1..]
            .parse::<u64>()
            .map_err(|_| self.error("invalid overflow helper width"))?;
        let slot = self.ir.alloca(bits / 8, (bits / 8).min(16));
        let status = self.ir.temp(format!(
            "call i32 @{name}({llvm} {left}, {llvm} {right}, ptr {slot})"
        ));
        let result = self.ir.temp(format!("load {llvm}, ptr {slot}, align 1"));
        let bad = self.ir.temp(format!("icmp ne i32 {status}, 0"));
        Ok((bad, Some(result)))
    }

    fn arithmetic_failure(
        &mut self,
        op: B,
        ty: TyId,
        left: &str,
        right: &(TyId, String),
    ) -> Result<String, Error> {
        let (bits, signed) = self.integer(ty)?;
        let llvm = format!("i{bits}");
        match op {
            B::Divide | B::Remainder => {
                let zero = self.ir.temp(format!("icmp eq {llvm} {}, 0", right.1));
                if !signed {
                    return Ok(zero);
                }
                let minimum = 1u128 << (bits - 1);
                let min = self.ir.temp(format!("icmp eq {llvm} {left}, -{minimum}"));
                let negative = self.ir.temp(format!("icmp eq {llvm} {}, -1", right.1));
                let overflow = self.ir.temp(format!("and i1 {min}, {negative}"));
                Ok(self.ir.temp(format!("or i1 {zero}, {overflow}")))
            }
            B::ShiftLeft | B::ShiftRight => {
                let rhs = self.module.scalar_type(right.0)?;
                Ok(self.ir.temp(format!("icmp uge {rhs} {}, {bits}", right.1)))
            }
            _ => Err(self.error("checked scalar operation is missing its failure predicate")),
        }
    }

    pub fn integer(&self, ty: TyId) -> Result<(u16, bool), Error> {
        match self.module.program.hir.types.get(ty) {
            Ty::Integer { bits, signed } => Ok((if *bits == 0 { 64 } else { *bits }, *signed)),
            Ty::Char => Ok((32, false)),
            _ => Err(self.error("checked arithmetic requires an integer")),
        }
    }

    pub fn resize(&mut self, source: TyId, target: TyId, value: String) -> Result<String, Error> {
        let source = self.module.scalar_type(source)?;
        let target = self.module.scalar_type(target)?;
        if source == target {
            return Ok(value);
        }
        let bits = |ty: &str| {
            ty.strip_prefix('i')
                .and_then(|bits| bits.parse::<u16>().ok())
        };
        let (Some(from), Some(to)) = (bits(&source), bits(&target)) else {
            return Err(self.error("native integer conversion is not scalar"));
        };
        Ok(self.ir.temp(format!(
            "{} {source} {value} to {target}",
            if from < to { "zext" } else { "trunc" }
        )))
    }
}

fn comparison(op: B, signed: bool, float: bool) -> Option<&'static str> {
    use B::*;
    Some(match (op, signed, float) {
        (Equal, _, false) => "eq",
        (NotEqual, _, false) => "ne",
        (Equal, _, true) => "oeq",
        (NotEqual, _, true) => "une",
        (Less, _, true) => "olt",
        (LessEqual, _, true) => "ole",
        (Greater, _, true) => "ogt",
        (GreaterEqual, _, true) => "oge",
        (Less, true, false) => "slt",
        (LessEqual, true, false) => "sle",
        (Greater, true, false) => "sgt",
        (GreaterEqual, true, false) => "sge",
        (Less, false, false) => "ult",
        (LessEqual, false, false) => "ule",
        (Greater, false, false) => "ugt",
        (GreaterEqual, false, false) => "uge",
        _ => return None,
    })
}

/// LLAM's qualified IR profile does not admit LLVM overflow intrinsics. These
/// small helpers keep defined wrapping arithmetic and explicit overflow tests;
/// optnone prevents InstCombine from recreating an unsupported intrinsic.
fn overflow_definition(name: &str, op: B, ty: &str, signed: bool) -> String {
    let operation = match op {
        B::Add => "add",
        B::Subtract => "sub",
        B::Multiply => "mul",
        _ => unreachable!("overflow definition"),
    };
    let mut out = format!(
        "define internal i32 @{name}({ty} %left, {ty} %right, ptr %out) #1 {{\nentry:\n  %result = {operation} {ty} %left, %right\n  store {ty} %result, ptr %out, align 1\n"
    );
    if op == B::Multiply {
        out.push_str(&multiply_test(ty, signed));
    } else if signed {
        let a = if op == B::Add { "%result" } else { "%right" };
        let _ = writeln!(
            out,
            "  %a = xor {ty} %left, {a}\n  %b = xor {ty} {}, %result\n  %both = and {ty} %a, %b\n  %bad = icmp slt {ty} %both, 0",
            if op == B::Add { "%right" } else { "%left" }
        );
        out.push_str("  %status = zext i1 %bad to i32\n  ret i32 %status\n");
    } else {
        let _ = writeln!(
            out,
            "  %bad = icmp ult {ty} {}, {}\n  %status = zext i1 %bad to i32\n  ret i32 %status",
            if op == B::Add { "%result" } else { "%left" },
            if op == B::Add { "%left" } else { "%right" }
        );
    }
    out.push_str("}\n");
    out
}

fn multiply_test(ty: &str, signed: bool) -> String {
    let mut out = format!(
        "  %zero = icmp eq {ty} %right, 0\n  br i1 %zero, label %safe, label %nonzero\nsafe:\n  ret i32 0\nnonzero:\n"
    );
    if signed {
        let bits = ty[1..].parse::<u32>().expect("integer helper type");
        let minimum = 1u128 << (bits - 1);
        let _ = writeln!(
            out,
            "  %min = icmp eq {ty} %left, -{minimum}\n  %minusone = icmp eq {ty} %right, -1\n  %special = and i1 %min, %minusone\n  br i1 %special, label %overflow, label %divide\noverflow:\n  ret i32 1\ndivide:"
        );
    }
    let _ = writeln!(
        out,
        "  %quotient = {} {ty} %result, %right\n  %bad = icmp ne {ty} %quotient, %left\n  %status = zext i1 %bad to i32\n  ret i32 %status",
        if signed { "sdiv" } else { "udiv" }
    );
    out
}

fn operation(op: B, signed: bool, float: bool) -> Option<&'static str> {
    use B::*;
    Some(match (op, signed, float) {
        (Add, _, true) => "fadd",
        (Subtract, _, true) => "fsub",
        (Multiply, _, true) => "fmul",
        (Divide, _, true) => "fdiv",
        (Remainder, _, true) => "frem",
        (Add, _, false) => "add",
        (Subtract, _, false) => "sub",
        (Multiply, _, false) => "mul",
        (Divide, true, false) => "sdiv",
        (Divide, false, false) => "udiv",
        (Remainder, true, false) => "srem",
        (Remainder, false, false) => "urem",
        (ShiftLeft, _, false) => "shl",
        (ShiftRight, true, false) => "ashr",
        (ShiftRight, false, false) => "lshr",
        (BitAnd | And, _, false) => "and",
        (BitOr | Or, _, false) => "or",
        (BitXor, _, false) => "xor",
        _ => return None,
    })
}
