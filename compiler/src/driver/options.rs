use super::{Emit, Mode};
use crate::external::Digest;
use std::{ffi::OsString, path::PathBuf};

pub(super) struct Options {
    pub native: Native,
    pub modules: Vec<PathBuf>,
    pub manifest: Option<PathBuf>,
    pub locked: bool,
    pub offline: bool,
    pub mode: Mode,
    pub emit: Emit,
    pub paths: Vec<PathBuf>,
    pub summary_paths: Vec<PathBuf>,
    pub trusted: Vec<Digest>,
}

pub(super) struct Native {
    pub backend: crate::native::Options,
    pub output: Option<PathBuf>,
    pub source: Option<PathBuf>,
    pub build: Option<PathBuf>,
    pub probe: bool,
    specified: bool,
    backend_specified: bool,
}
impl Default for Native {
    fn default() -> Self {
        Self {
            backend: crate::native::Options {
                optimization: crate::native::Optimization::O0,
                ..crate::native::Options::default()
            },
            output: None,
            source: None,
            build: None,
            probe: true,
            specified: false,
            backend_specified: false,
        }
    }
}
pub(super) enum Action {
    Help,
    Version,
    Grammar,
    Run(Box<Options>),
}
pub(super) enum Error {
    Usage,
    Message(String),
}
impl Error {
    fn message(text: &str) -> Self {
        Self::Message(text.into())
    }
}

/// Argument interpretation is pure: it neither opens files nor performs a
/// compilation. `--` preserves non-UTF-8 paths and literal command-like names.
pub(super) fn parse(arguments: &[OsString]) -> Result<Action, Error> {
    let mut options = Options {
        native: Native::default(),
        modules: Vec::new(),
        manifest: None,
        locked: false,
        offline: false,
        mode: Mode::Check,
        emit: Emit::None,
        paths: Vec::new(),
        summary_paths: Vec::new(),
        trusted: Vec::new(),
    };
    let mut literal = false;
    let mut arguments = arguments.iter();
    while let Some(argument) = arguments.next() {
        if !literal && let Some(text) = argument.to_str() {
            if options.paths.is_empty()
                && let Some(mode) = command(text)
            {
                options.mode = mode;
                continue;
            }
            if text.starts_with("--emit=") {
                options.emit = emission(text)?;
                continue;
            }
            match text {
                "--" => {
                    literal = true;
                    continue;
                }
                "--help" | "-h" => return Ok(Action::Help),
                "--version" | "-V" => return Ok(Action::Version),
                "--grammar" => return Ok(Action::Grammar),
                text if text.starts_with('-')
                    && value_option(text, &mut options, &mut arguments)? =>
                {
                    continue;
                }
                text if text.starts_with('-') => {
                    return Err(Error::Message(format!("unsupported option {text:?}")));
                }
                _ => {}
            }
        }
        options.paths.push(PathBuf::from(argument));
    }
    validate(options)
}

fn value_option<'a>(
    text: &str,
    options: &mut Options,
    arguments: &mut std::slice::Iter<'a, OsString>,
) -> Result<bool, Error> {
    if native_option(text, &mut options.native, arguments)? {
        return Ok(true);
    }
    match text {
        "--summary" => {
            options.summary_paths.push(PathBuf::from(
                arguments
                    .next()
                    .ok_or_else(|| Error::message("--summary requires a path"))?,
            ));
        }
        "--module" => {
            options.modules.push(PathBuf::from(
                arguments
                    .next()
                    .ok_or_else(|| Error::message("--module requires a capsule path"))?,
            ));
        }
        "--manifest-path" => {
            if options.manifest.is_some() {
                return Err(Error::message("duplicate --manifest-path"));
            }
            options.manifest =
                Some(PathBuf::from(arguments.next().ok_or_else(|| {
                    Error::message("--manifest-path requires Cavo.toml")
                })?));
        }
        "--locked" => {
            options.locked = true;
        }
        "--offline" => {
            options.offline = true;
        }
        "--trust-summary" => {
            options.trusted.push(trusted_digest(arguments.next())?);
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn command(text: &str) -> Option<Mode> {
    Some(match text {
        "check" => Mode::Check,
        "parse" => Mode::Parse,
        "lex" => Mode::Lex,
        "summary-id" => Mode::SummaryId,
        "lock" => Mode::Lock,
        "build" => Mode::Build,
        "run" => Mode::Run,
        "doctor" => Mode::Doctor,
        "clean" => Mode::Clean,
        "sdk" => Mode::Sdk,
        _ => return None,
    })
}

fn emission(text: &str) -> Result<Emit, Error> {
    Ok(match text {
        "--emit=ast" => Emit::Ast,
        "--emit=hir" => Emit::Hir,
        "--emit=mir" => Emit::Mir,
        "--emit=mono" => Emit::Mono,
        "--emit=local" => Emit::Local,
        "--emit=tokens" => Emit::Tokens,
        "--emit=interface" => Emit::Interface,
        "--emit=module" => Emit::Module,
        "--emit=contracts" => Emit::Contracts,
        "--emit=llvm-ir" => Emit::LlvmIr,
        "--emit=obj" => Emit::Object,
        _ => return Err(Error::Message(format!("unsupported option {text:?}"))),
    })
}

fn trusted_digest(argument: Option<&OsString>) -> Result<Digest, Error> {
    argument
        .and_then(|value| value.to_str())
        .and_then(Digest::parse)
        .ok_or_else(|| {
            Error::message(concat!(
                "--trust-summary requires sha256: followed by ",
                "64 lowercase hex digits"
            ))
        })
}

fn validate(mut options: Options) -> Result<Action, Error> {
    if options.mode.tool() {
        validate_tool(&options)?;
        return Ok(Action::Run(Box::new(options)));
    }
    if options.paths.is_empty() && options.manifest.is_none() {
        return Err(Error::Usage);
    }
    if options.manifest.is_some() && !options.paths.is_empty() {
        return Err(Error::message(
            "manifest mode does not accept loose source paths",
        ));
    }
    if options.mode == Mode::Lock {
        validate_lock(&options)?;
        return Ok(Action::Run(Box::new(options)));
    }
    if options.mode != Mode::Check
        && !options.mode.native()
        && (options.manifest.is_some() || !options.modules.is_empty())
    {
        return Err(Error::message("modules and packages require check mode"));
    }
    if options.mode.native() {
        validate_native(&options)?;
        return Ok(Action::Run(Box::new(options)));
    }
    if options.native.specified {
        return Err(Error::message(
            "native options require build, run, doctor or sdk mode",
        ));
    }
    if options.manifest.is_none() && (options.locked || options.offline) {
        return Err(Error::message("--locked/--offline require --manifest-path"));
    }
    if options.mode == Mode::SummaryId {
        if options.paths.len() != 1
            || options.emit != Emit::None
            || !options.summary_paths.is_empty()
            || !options.trusted.is_empty()
        {
            return Err(Error::message(
                "summary-id requires exactly one summary path",
            ));
        }
        return Ok(Action::Run(Box::new(options)));
    }
    if options.emit == Emit::Ast {
        options.mode = Mode::Parse;
    }
    if options.emit == Emit::Tokens {
        options.mode = Mode::Lex;
    }
    validate_emission(&options)?;
    Ok(Action::Run(Box::new(options)))
}

fn validate_lock(options: &Options) -> Result<(), Error> {
    if options.manifest.is_none()
        || options.emit != Emit::None
        || options.locked
        || !options.modules.is_empty()
        || !options.summary_paths.is_empty()
        || !options.trusted.is_empty()
        || options.native.specified
    {
        return Err(Error::message(
            "lock requires only --manifest-path and optional --offline",
        ));
    }
    Ok(())
}

fn validate_emission(options: &Options) -> Result<(), Error> {
    if matches!(options.emit, Emit::LlvmIr | Emit::Object) {
        return Err(Error::message("native emission requires build mode"));
    }
    if options.mode != Mode::Check {
        if options.emit == Emit::Mono {
            return Err(Error::message("monomorphized emission requires check mode"));
        }
        if options.emit == Emit::Hir {
            return Err(Error::message("HIR emission requires check mode"));
        }
        if options.emit == Emit::Mir {
            return Err(Error::message("MIR emission requires check mode"));
        }
        if options.emit == Emit::Local {
            return Err(Error::message(
                "local analysis emission requires check mode",
            ));
        }
        if options.emit == Emit::Interface
            || matches!(options.emit, Emit::Module | Emit::Contracts)
            || !options.summary_paths.is_empty()
            || !options.trusted.is_empty()
        {
            return Err(Error::message(
                "external summaries and interface emission require check mode",
            ));
        }
    }
    Ok(())
}

fn native_option<'a>(
    text: &str,
    options: &mut Native,
    arguments: &mut std::slice::Iter<'a, OsString>,
) -> Result<bool, Error> {
    if backend_option(text, &mut options.backend, arguments)? {
        options.specified = true;
        options.backend_specified = true;
        return Ok(true);
    }
    match text {
        "-o" | "--output" => native_path(&mut options.output, arguments.next(), "--output")?,
        "--llam-source" => native_path(&mut options.source, arguments.next(), "--llam-source")?,
        "--llam-build" => native_path(&mut options.build, arguments.next(), "--llam-build")?,
        "--no-probe" => options.probe = false,
        _ => return Ok(false),
    }
    options.specified = true;
    Ok(true)
}

fn backend_option<'a>(
    text: &str,
    options: &mut crate::native::Options,
    arguments: &mut std::slice::Iter<'a, OsString>,
) -> Result<bool, Error> {
    use crate::native::{Optimization, Runtime};
    match text {
        "--llvm-bin" => native_path(&mut options.llvm_bin, arguments.next(), "--llvm-bin")?,
        "--llam-sdk" => native_path(&mut options.llam_sdk, arguments.next(), "--llam-sdk")?,
        "-O0" => options.optimization = Optimization::O0,
        "-O2" | "--release" => options.optimization = Optimization::O2,
        "--runtime=llam" => options.runtime = Runtime::Llam,
        "--runtime=none" => options.runtime = Runtime::None,
        _ => return Ok(false),
    }
    Ok(true)
}

fn native_path(
    slot: &mut Option<PathBuf>,
    argument: Option<&OsString>,
    name: &str,
) -> Result<(), Error> {
    let path = argument.ok_or_else(|| Error::Message(format!("{name} requires a path")))?;
    if slot.replace(PathBuf::from(path)).is_some() {
        return Err(Error::Message(format!("duplicate {name}")));
    }
    Ok(())
}

fn validate_native(options: &Options) -> Result<(), Error> {
    if options.manifest.is_none() && (options.locked || options.offline) {
        return Err(Error::message("--locked/--offline require --manifest-path"));
    }
    if !matches!(options.emit, Emit::None | Emit::LlvmIr | Emit::Object) {
        return Err(Error::message(
            "build/run support --emit=llvm-ir or --emit=obj; use check for frontend dumps",
        ));
    }
    if options.mode == Mode::Run && options.emit != Emit::None {
        return Err(Error::message(
            "run requires an executable, not an emission mode",
        ));
    }
    if options.native.source.is_some() || options.native.build.is_some() || !options.native.probe {
        return Err(Error::message(
            "SDK preparation paths require sdk; --no-probe requires doctor",
        ));
    }
    Ok(())
}

fn validate_tool(options: &Options) -> Result<(), Error> {
    if !options.paths.is_empty()
        || options.emit != Emit::None
        || !options.modules.is_empty()
        || !options.summary_paths.is_empty()
        || !options.trusted.is_empty()
        || options.locked
        || options.offline
    {
        return Err(Error::message(
            "doctor/clean/sdk do not accept source, emission, module or package-resolution arguments",
        ));
    }
    match options.mode {
        Mode::Doctor
            if options.native.output.is_none()
                && options.native.source.is_none()
                && options.native.build.is_none() =>
        {
            Ok(())
        }
        Mode::Clean if !options.native.specified => Ok(()),
        Mode::Sdk
            if options.manifest.is_none()
                && options.native.source.is_some()
                && options.native.build.is_some()
                && !options.native.backend_specified
                && options.native.probe =>
        {
            Ok(())
        }
        _ => Err(Error::message(
            "sdk requires --llam-source and --llam-build; doctor/clean accept only their relevant options",
        )),
    }
}
