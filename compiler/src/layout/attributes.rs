use super::{Error, TargetLayout};
use crate::{
    hir, source::SourceMap, symbol::Interner, syntax::token::TokenKind, types::GenericArg,
};

pub(super) struct Instance<'a> {
    pub owner: hir::DefId,
    pub declaration: &'a hir::Definition,
    pub arguments: &'a [GenericArg],
}

#[derive(Clone, Copy)]
pub(super) struct Options {
    pub c: bool,
    pub packed: bool,
    pub alignment: u64,
}

pub(super) fn parse(
    program: &mut hir::Program,
    instance: Instance<'_>,
    target: TargetLayout,
    symbols: &Interner,
    sources: &SourceMap,
) -> Result<Options, Error> {
    let definition = instance.declaration;
    let mut options = Options {
        c: false,
        packed: false,
        alignment: 1,
    };
    let mut aligned = false;
    for attribute in &definition.attributes {
        match symbols.get(attribute.name) {
            "repr" => {
                if options.c || !is_c(attribute, symbols) {
                    return Err(problem(definition, "expected one repr(C) annotation"));
                }
                options.c = true;
            }
            "packed" => {
                if options.packed || !attribute.arguments.is_empty() {
                    return Err(problem(
                        definition,
                        "packed accepts no arguments and may occur once",
                    ));
                }
                options.packed = true;
            }
            "align" => {
                if aligned {
                    return Err(problem(definition, "duplicate alignment annotation"));
                }
                options.alignment =
                    resolved_alignment(attribute, &instance, program, target, sources)?;
                if !options.alignment.is_power_of_two()
                    || options.alignment > target.maximum_alignment
                {
                    return Err(problem(
                        definition,
                        "alignment must be a supported power of two",
                    ));
                }
                aligned = true;
            }
            _ => {}
        }
    }
    if options.packed && aligned {
        return Err(problem(
            definition,
            "packed and explicit alignment cannot be combined",
        ));
    }
    Ok(options)
}

fn resolved_alignment(
    attribute: &hir::Attribute,
    instance: &Instance<'_>,
    program: &mut hir::Program,
    target: TargetLayout,
    sources: &SourceMap,
) -> Result<u64, Error> {
    let Some(constant) = attribute.constant else {
        return alignment(attribute, instance.declaration, program, sources);
    };
    let constant = program
        .types
        .const_substitute(constant, instance.owner, instance.arguments)
        .map_err(|error| problem(instance.declaration, &error.to_string()))?;
    let limits = crate::ctfe::Limits {
        pointer_bits: target.pointer_bits,
        ..crate::ctfe::Limits::default()
    };
    let constant =
        crate::ctfe::evaluate_term(program, constant, limits).map_err(|error| Error {
            ty: instance.declaration.ty,
            span: Some(error.span),
            message: error.message,
        })?;
    program.types.const_usize(constant).ok_or_else(|| {
        problem(
            instance.declaration,
            "alignment constant must have target usize type",
        )
    })
}

fn is_c(attribute: &hir::Attribute, symbols: &Interner) -> bool {
    matches!(attribute.arguments.as_slice(), [token] if matches!(token.kind, TokenKind::Ident(name) if symbols.get(name) == "C"))
}

fn alignment(
    attribute: &hir::Attribute,
    definition: &hir::Definition,
    program: &hir::Program,
    sources: &SourceMap,
) -> Result<u64, Error> {
    let [token] = attribute.arguments.as_slice() else {
        return Err(problem(
            definition,
            "alignment requires one constant integer",
        ));
    };
    if let TokenKind::Ident(name) = token.kind {
        return named_alignment(name, definition, program);
    }
    if token.kind != TokenKind::Integer {
        return Err(problem(
            definition,
            "alignment requires an evaluated integer constant",
        ));
    }
    let source = sources
        .files()
        .get(token.span.file.0 as usize)
        .ok_or_else(|| problem(definition, "alignment has no source text"))?;
    let text = source
        .text()
        .get(token.span.start as usize..token.span.end as usize)
        .ok_or_else(|| problem(definition, "invalid alignment source span"))?;
    let text = text.replace('_', "");
    let text = text.strip_suffix("usize").unwrap_or(&text);
    let (radix, digits) = if let Some(value) = text.strip_prefix("0x") {
        (16, value)
    } else if let Some(value) = text.strip_prefix("0o") {
        (8, value)
    } else if let Some(value) = text.strip_prefix("0b") {
        (2, value)
    } else {
        (10, text)
    };
    u64::from_str_radix(digits, radix).map_err(|_| problem(definition, "invalid alignment integer"))
}

fn named_alignment(
    name: crate::symbol::Symbol,
    definition: &hir::Definition,
    program: &hir::Program,
) -> Result<u64, Error> {
    let constant = program
        .definitions
        .iter()
        .position(|candidate| {
            candidate.name == name
                && candidate.module == definition.module
                && candidate.kind == hir::DefinitionKind::Global
        })
        .map(|index| hir::DefId(index as u32))
        .ok_or_else(|| problem(definition, "alignment name is not a module constant"))?;
    let value = crate::ctfe::evaluate_global(program, constant, crate::ctfe::Limits::default())
        .map_err(|error| problem(definition, &error.message))?;
    value.usize_value().ok_or_else(|| {
        problem(
            definition,
            "alignment constant is not a nonnegative target integer",
        )
    })
}

fn problem(definition: &hir::Definition, message: &str) -> Error {
    Error {
        ty: definition.ty,
        span: Some(definition.span),
        message: message.into(),
    }
}
