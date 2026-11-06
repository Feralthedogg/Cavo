use super::{Emit, Mode};
use crate::external::Digest;
use std::{ffi::OsString, path::PathBuf};

pub(super) struct Options {
    pub mode: Mode,
    pub emit: Emit,
    pub paths: Vec<PathBuf>,
    pub summary_paths: Vec<PathBuf>,
    pub trusted: Vec<Digest>,
}
pub(super) enum Action {
    Help,
    Version,
    Run(Options),
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
                "--summary" => {
                    options.summary_paths.push(PathBuf::from(
                        arguments
                            .next()
                            .ok_or_else(|| Error::message("--summary requires a path"))?,
                    ));
                    continue;
                }
                "--trust-summary" => {
                    options.trusted.push(trusted_digest(arguments.next())?);
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

fn command(text: &str) -> Option<Mode> {
    Some(match text {
        "check" => Mode::Check,
        "parse" => Mode::Parse,
        "lex" => Mode::Lex,
        "summary-id" => Mode::SummaryId,
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
    if options.paths.is_empty() {
        return Err(Error::Usage);
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
        return Ok(Action::Run(options));
    }
    if options.emit == Emit::Ast {
        options.mode = Mode::Parse;
    }
    if options.emit == Emit::Tokens {
        options.mode = Mode::Lex;
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
            || !options.summary_paths.is_empty()
            || !options.trusted.is_empty()
        {
            return Err(Error::message(
                "external summaries and interface emission require check mode",
            ));
        }
    }
    Ok(Action::Run(options))
}
