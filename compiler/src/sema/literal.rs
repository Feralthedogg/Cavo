use crate::{
    diagnostic::{Diagnostic, report},
    hir::Constant,
    source::Span,
    syntax::ast::LiteralKind,
    types::{Region, Ty, TyId, TypeContext},
};

pub(super) fn check(
    text: &str,
    kind: LiteralKind,
    expected: Option<TyId>,
    negative: bool,
    span: Span,
    types: &mut TypeContext,
    diagnostics: &mut Vec<Diagnostic>,
) -> (TyId, Constant) {
    let error = |diagnostics: &mut Vec<Diagnostic>, message| {
        report(
            diagnostics,
            Diagnostic::error("E-LITERAL-001", message, span),
        )
    };
    match kind {
        LiteralKind::Bool(value) => (TyId::BOOL, Constant::Bool(value)),
        LiteralKind::Integer => {
            let Some((magnitude, suffix)) = integer_parts(text) else {
                error(diagnostics, "invalid or oversized integer literal");
                return (
                    TyId::ERROR,
                    Constant::Integer {
                        magnitude: 0,
                        negative,
                    },
                );
            };
            let ty = if suffix.is_empty() {
                expected
                    .filter(|&ty| types.integer(ty))
                    .unwrap_or_else(|| types.builtin("i32").expect("primitive"))
            } else {
                types
                    .builtin(suffix)
                    .filter(|&ty| types.integer(ty))
                    .unwrap_or_else(|| {
                        error(diagnostics, "invalid integer type suffix");
                        TyId::ERROR
                    })
            };
            if let Ty::Integer { signed, bits } = types.get(ty) {
                let bits = if *bits == 0 { 64 } else { *bits };
                let limit = if *signed {
                    if negative {
                        1_u128 << (bits - 1)
                    } else {
                        (1_u128 << (bits - 1)) - 1
                    }
                } else if bits == 128 {
                    u128::MAX
                } else {
                    (1_u128 << bits) - 1
                };
                if magnitude > limit || (negative && !signed) {
                    error(diagnostics, "integer literal is outside its type's range");
                }
            }
            (
                ty,
                Constant::Integer {
                    magnitude,
                    negative,
                },
            )
        }
        LiteralKind::Float => {
            let (number, suffix) = if let Some(number) = text.strip_suffix("f32") {
                (number, Some("f32"))
            } else if let Some(number) = text.strip_suffix("f64") {
                (number, Some("f64"))
            } else {
                (text, None)
            };
            let ty = suffix
                .and_then(|s| types.builtin(s))
                .or_else(|| expected.filter(|&ty| matches!(types.get(ty), Ty::Float { .. })))
                .unwrap_or_else(|| types.builtin("f64").expect("primitive"));
            let number = number.replace('_', "");
            let value = match types.get(ty) {
                Ty::Float { bits: 32 } => number.parse::<f32>().map(f64::from).ok(),
                _ => number.parse::<f64>().ok(),
            };
            let value = match value {
                Some(value) if value.is_finite() => value,
                _ => {
                    error(diagnostics, "invalid or out-of-range float literal");
                    0.0
                }
            };
            (ty, Constant::Float(if negative { -value } else { value }))
        }
        LiteralKind::String => {
            let value = decode_quoted(text).unwrap_or_default();
            let ty = types.intern(Ty::Reference {
                region: Region::Static,
                mutable: false,
                inner: TyId::STR,
            });
            (ty, Constant::String(value))
        }
        LiteralKind::Char => {
            let value = decode_quoted(text).and_then(|s| {
                let mut chars = s.chars();
                let first = chars.next()?;
                chars.next().is_none().then_some(first)
            });
            let value = value.unwrap_or_else(|| {
                error(diagnostics, "invalid character literal");
                '\0'
            });
            (TyId::CHAR, Constant::Char(value))
        }
        LiteralKind::Null => {
            let ty = expected
                .filter(|&ty| matches!(types.get(ty), Ty::Pointer { .. }))
                .unwrap_or_else(|| {
                    error(diagnostics, "null requires a raw pointer type context");
                    TyId::ERROR
                });
            (ty, Constant::Null)
        }
    }
}

pub(super) fn integer_parts(text: &str) -> Option<(u128, &str)> {
    let (prefix, radix) = if text.starts_with("0x") || text.starts_with("0X") {
        (2, 16)
    } else if text.starts_with("0b") || text.starts_with("0B") {
        (2, 2)
    } else if text.starts_with("0o") || text.starts_with("0O") {
        (2, 8)
    } else {
        (0, 10)
    };
    let end = text[prefix..]
        .bytes()
        .position(|b| b != b'_' && !(b as char).is_digit(radix))
        .map_or(text.len(), |n| prefix + n);
    let mut value = 0_u128;
    let mut digits = 0;
    for byte in text[prefix..end].bytes().filter(|&b| b != b'_') {
        value = value
            .checked_mul(radix as u128)?
            .checked_add((byte as char).to_digit(radix)? as u128)?;
        digits += 1;
    }
    (digits > 0).then_some((value, &text[end..]))
}

pub(super) fn decode_quoted(text: &str) -> Option<String> {
    let mut output = String::new();
    let mut chars = text.get(1..text.len().checked_sub(1)?)?.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            output.push(ch);
            continue;
        }
        let ch = match chars.next()? {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '0' => '\0',
            '\\' => '\\',
            '\'' => '\'',
            '"' => '"',
            'x' => char::from_u32(chars.next()?.to_digit(16)? * 16 + chars.next()?.to_digit(16)?)?,
            'u' => {
                if chars.next()? != '{' {
                    return None;
                }
                let mut value = 0_u32;
                loop {
                    let ch = chars.next()?;
                    if ch == '}' {
                        break;
                    }
                    value = value.checked_mul(16)?.checked_add(ch.to_digit(16)?)?;
                }
                char::from_u32(value)?
            }
            _ => return None,
        };
        output.push(ch);
    }
    Some(output)
}
