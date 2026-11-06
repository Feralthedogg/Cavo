//! LLVM emission from concrete, checked MIR and its elaborated cleanup CFG.
//! Byte-addressed storage uses the layout table; no alias or pointer-validity
//! attributes are inferred merely from a source type.
mod arithmetic;
mod body;
mod cleanup;
mod control;
mod intrinsics;
mod ir;
mod module;
mod place;
mod value;

use crate::{
    hir, layout, mir, mono,
    source::Span,
    symbol::Interner,
    types::{Ty, TyId},
};
use module::Module;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Write},
};

#[derive(Clone, Debug)]
pub struct Error {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Error {}

pub struct Artifact {
    pub llvm_ir: String,
    pub entry: hir::DefId,
}

/// This boundary consumes no optimization certificate. The concrete MIR,
/// cleanup correspondence and contract snapshot are checked before emission.
pub fn emit(
    program: &mut mono::Program,
    symbols: &Interner,
    triple: &str,
) -> Result<Artifact, Error> {
    let span = program
        .hir
        .definitions
        .first()
        .map_or(Span::new(crate::source::FileId(0), 0, 0), |d| d.span);
    let validate = |message: String| Error {
        code: "E-CODEGEN-INPUT",
        span,
        message,
    };
    program
        .hir
        .validate()
        .map_err(|e| validate(e.to_string()))?;
    program
        .mir
        .validate(&mut program.hir)
        .map_err(|e| validate(e.to_string()))?;
    program
        .analysis
        .drops
        .validate(&program.mir, &mut program.hir)
        .map_err(|e| validate(e.to_string()))?;
    program
        .analysis
        .contracts
        .validate_for(&program.mir, &program.hir)
        .map_err(validate)?;
    coverage(program)?;
    let entry = entry(program, symbols, span)?;
    let mut module = Module::new(program, symbols, triple, span)?;
    module.functions()?;
    module.glue()?;
    module.entry(entry)?;
    Ok(Artifact {
        llvm_ir: module.finish()?,
        entry,
    })
}

fn coverage(program: &mono::Program) -> Result<(), Error> {
    for body in &program.mir.functions {
        if body
            .locals
            .iter()
            .any(|local| local.kind == mir::LocalKind::TaskRegistry)
        {
            return Err(Error {code:"E-RUNTIME-SCOPE-DRAIN",span:body.blocks[0].span,
                message:"scoped tasks require a cancellation-immune managed group drain, unavailable in pinned LLAM 3.0.0; the host-only drain cannot release borrowed parent storage".into()});
        }
    }
    for function in &program.analysis.borrows.functions {
        if let Some(gap) = function
            .gaps
            .iter()
            .find(|gap| gap.kind != mir::borrow::GapKind::RawPointer)
        {
            return Err(Error {
                code: "E-CODEGEN-COVERAGE",
                span: gap.span,
                message: format!(
                    "native memory analysis is incomplete: {}",
                    gap.kind.message()
                ),
            });
        }
    }
    for function in &program.analysis.effects.functions {
        if !function.unknown.is_empty() {
            return Err(Error {
                code: "E-CODEGEN-COVERAGE",
                span: program.hir.definitions[function.definition].span,
                message: format!(
                    "native effect analysis is incomplete: {:?}; foreign calls need a pinned trusted summary",
                    function.unknown
                ),
            });
        }
    }
    Ok(())
}

fn entry(program: &mono::Program, symbols: &Interner, span: Span) -> Result<hir::DefId, Error> {
    let mut entries = program.mir.functions.iter().filter(|body| {
        let definition = &program.hir.definitions[body.definition];
        symbols.get(definition.name) == "main"
    });
    let body = entries.next().ok_or_else(|| Error {
        code: "E-ENTRY",
        span,
        message: "an executable requires one `void main()` or `i32 main()` function".into(),
    })?;
    let declaration = &program.hir.definitions[body.definition];
    let valid = matches!(program.hir.types.get(declaration.ty), Ty::Function { parameters, result }
        if parameters.is_empty() && (*result == TyId::VOID || matches!(program.hir.types.get(*result), Ty::Integer { signed:true, bits:32 })));
    if entries.next().is_some() || !valid {
        return Err(Error {
            code: "E-ENTRY",
            span: declaration.span,
            message:
                "the executable entry must be unique, take no arguments and return void or i32"
                    .into(),
        });
    }
    Ok(body.definition)
}

fn problem(span: Span, message: impl Into<String>) -> Error {
    Error {
        code: "E-CODEGEN-STAGE",
        span,
        message: message.into(),
    }
}

fn quote(text: &str) -> String {
    let mut output = String::from("\"");
    for byte in text.bytes() {
        if (32..127).contains(&byte) && !matches!(byte, b'"' | b'\\') {
            output.push(char::from(byte));
        } else {
            let _ = write!(output, "\\{byte:02X}");
        }
    }
    output.push('"');
    output
}
