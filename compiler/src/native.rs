//! External LLVM tools keep the compiler itself free of unsafe LLVM FFI.
//! Managed objects retain LLAM's IR/machine passes and final-image admission.
mod pipeline;
mod scratch;
mod sdk;
mod tools;

use crate::{codegen, mono, source::Span, symbol::Interner};
pub use sdk::prepare as prepare_sdk;
pub use sdk::{LLAM_RELEASE, LLAM_REVISION, LLVM_VERSION};
use std::{
    fmt,
    path::{Path, PathBuf},
};
use tools::Tools;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Runtime {
    Llam,
    None,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputKind {
    Object,
    Executable,
}

#[derive(Clone, Debug)]
pub struct Options {
    pub llvm_bin: Option<PathBuf>,
    pub llam_sdk: Option<PathBuf>,
    pub runtime: Runtime,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            llvm_bin: None,
            llam_sdk: None,
            runtime: Runtime::Llam,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub code: &'static str,
    pub span: Option<Span>,
    pub message: String,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Error {}
impl From<codegen::Error> for Error {
    fn from(error: codegen::Error) -> Self {
        Self {
            code: error.code,
            span: Some(error.span),
            message: error.message,
        }
    }
}

pub struct Build {
    pub target: String,
    pub runtime: Runtime,
}

pub fn llvm_ir(
    program: &mut mono::Program,
    symbols: &Interner,
    options: &Options,
) -> Result<String, Error> {
    let tools = Tools::discover(options)?;
    Ok(codegen::emit(program, symbols, &tools.target)?.llvm_ir)
}

pub fn build(
    program: &mut mono::Program,
    symbols: &Interner,
    options: &Options,
    kind: OutputKind,
    output: &Path,
) -> Result<Build, Error> {
    let tools = Tools::discover(options)?;
    let artifact = codegen::emit(program, symbols, &tools.target)?;
    if options.runtime == Runtime::Llam {
        managed_frames(program, symbols)?;
    }
    let sdk = if options.runtime == Runtime::Llam {
        Some(sdk::Sdk::load(options)?)
    } else {
        None
    };
    pipeline::build(&tools, sdk.as_ref(), artifact, kind, output)?;
    Ok(Build {
        target: tools.target,
        runtime: options.runtime,
    })
}

fn managed_frames(program: &mut mono::Program, symbols: &Interner) -> Result<(), Error> {
    for body in &program.mir.functions {
        let definition = &program.hir.definitions[body.definition];
        if definition
            .attributes
            .iter()
            .any(|attribute| symbols.get(attribute.name) == "nopreempt")
        {
            return Err(Error {code:"E-CODEGEN-NOPREEMPT",span:Some(definition.span),
                message:"managed lowering for bounded @nopreempt native regions is not connected; refusing to emit asynchronously interruptible code for this contract".into()});
        }
    }
    let evidence = crate::tasks::independent_frames(
        &program.mir,
        &mut program.hir,
        symbols,
        &program.analysis.effects.functions,
    )
    .map_err(|message| failure("E-CODEGEN-FRAME", message))?;
    if let Some(body) = program
        .mir
        .functions
        .iter()
        .find(|body| !evidence.established.contains(&body.definition))
    {
        return Err(Error {code:"E-CODEGEN-FRAME",span:Some(program.hir.definitions[body.definition].span),
            message:"cannot establish Send and suspension requirements for the native managed frame; use an owning transfer contract or a thread-bound declaration".into()});
    }
    Ok(())
}

fn failure(code: &'static str, message: impl Into<String>) -> Error {
    Error {
        code,
        span: None,
        message: message.into(),
    }
}
