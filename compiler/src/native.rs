//! External LLVM tools keep the compiler itself free of unsafe LLVM FFI.
//! Managed objects retain LLAM's IR/machine passes and final-image admission.
mod doctor;
mod pipeline;
mod scratch;
mod sdk;
mod tools;
pub use doctor::{Doctor, diagnose};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Optimization {
    O0,
    O2,
}
impl Optimization {
    pub fn profile(self) -> &'static str {
        match self {
            Self::O0 => "debug",
            Self::O2 => "release",
        }
    }
    fn llvm(self) -> &'static str {
        match self {
            Self::O0 => "O0",
            Self::O2 => "O2",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Options {
    pub llvm_bin: Option<PathBuf>,
    pub llam_sdk: Option<PathBuf>,
    pub runtime: Runtime,
    pub optimization: Optimization,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            llvm_bin: None,
            llam_sdk: None,
            runtime: Runtime::Llam,
            optimization: Optimization::O2,
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
    Compiler::new(options)?.llvm_ir(program, symbols)
}

pub fn build(
    program: &mut mono::Program,
    symbols: &Interner,
    options: &Options,
    kind: OutputKind,
    output: &Path,
) -> Result<Build, Error> {
    Compiler::new(options)?.build(program, symbols, kind, output)
}

/// A CLI invocation validates its toolchain once, before choosing a target path.
pub(crate) struct Compiler {
    tools: Tools,
    options: Options,
}
impl Compiler {
    pub fn new(options: &Options) -> Result<Self, Error> {
        Ok(Self {
            tools: Tools::discover(options)?,
            options: options.clone(),
        })
    }
    pub fn target(&self) -> &str {
        &self.tools.target
    }
    pub fn llvm_ir(
        &self,
        program: &mut mono::Program,
        symbols: &Interner,
    ) -> Result<String, Error> {
        Ok(codegen::emit(program, symbols, &self.tools.target)?.llvm_ir)
    }
    pub fn build(
        &self,
        program: &mut mono::Program,
        symbols: &Interner,
        kind: OutputKind,
        output: &Path,
    ) -> Result<Build, Error> {
        let artifact = codegen::emit(program, symbols, &self.tools.target)?;
        if self.options.runtime == Runtime::Llam {
            managed_frames(program, symbols)?;
        }
        let sdk = if self.options.runtime == Runtime::Llam {
            Some(sdk::Sdk::load(&self.options)?)
        } else {
            None
        };
        pipeline::build(
            &self.tools,
            sdk.as_ref(),
            artifact,
            kind,
            output,
            self.options.optimization,
        )?;
        Ok(Build {
            target: self.tools.target.clone(),
            runtime: self.options.runtime,
        })
    }
}

/// Checks a sealed managed image without resealing or modifying it.
pub fn verify_image(image: &Path, options: &Options) -> Result<u64, Error> {
    let tools = Tools::discover(options)?;
    let sdk = sdk::Sdk::load(options)?;
    pipeline::check_image(&tools, &sdk, image)
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
