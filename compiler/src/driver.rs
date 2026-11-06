use crate::{Compilation, syntax::lexer};
use std::{
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

mod options;

const HELP: &str = r#"Cavo frontend

Usage: cavoite [check|parse|lex] [--emit=ast|hir|mir|mono|local|tokens|interface] FILE...
       cavoite summary-id FILE

check  Check types, local moves, NLL and supported region contracts (default).
parse  Parse the language grammar and dump AST.
lex    Dump tokens with original UTF-8 byte spans.

--summary FILE          Load a versioned external summary without trusting it.
--trust-summary DIGEST  Pin a reviewed document's sha256 identity as an assumption.
--emit=interface        Emit declaration fingerprints; type checking only.
--emit=local            Dump CFG, findings and external assumption dependencies.
--emit=mir              Lower and verify MIR with explicit cleanup paths.
--emit=mono             Instantiate generics; dump concrete MIR, layout and glue.

This foundation does not generate code. General heap/effect/contract and task
analyses are pending; full memory safety is unverified.
"#;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Check,
    Parse,
    Lex,
    SummaryId,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Emit {
    None,
    Ast,
    Hir,
    Mir,
    Mono,
    Local,
    Tokens,
    Interface,
}

pub fn main_entry() -> ExitCode {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    let status = run(
        &arguments,
        &mut io::stdout().lock(),
        &mut io::stderr().lock(),
    );
    ExitCode::from(status)
}

pub fn run(arguments: &[OsString], output: &mut dyn Write, error: &mut dyn Write) -> u8 {
    match run_inner(arguments, output, error) {
        Ok(status) => status,
        Err(problem) if problem.kind() == io::ErrorKind::BrokenPipe => 0,
        Err(problem) => {
            let _ = writeln!(error, "cavoite: {problem}");
            2
        }
    }
}

fn run_inner(
    arguments: &[OsString],
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let options = match options::parse(arguments) {
        Ok(options::Action::Help) => {
            output.write_all(HELP.as_bytes())?;
            return Ok(0);
        }
        Ok(options::Action::Version) => {
            writeln!(output, "cavoite {} (frontend)", env!("CARGO_PKG_VERSION"))?;
            return Ok(0);
        }
        Ok(options::Action::Run(options)) => options,
        Err(options::Error::Usage) => {
            error.write_all(HELP.as_bytes())?;
            return Ok(2);
        }
        Err(options::Error::Message(message)) => {
            writeln!(error, "cavoite: {message}")?;
            return Ok(2);
        }
    };
    let options::Options {
        mode,
        emit,
        paths,
        summary_paths,
        trusted,
    } = options;
    if mode == Mode::SummaryId {
        let text = read_summary(&paths[0])?;
        writeln!(output, "{}", crate::external::Summaries::digest(&text))?;
        return Ok(0);
    }
    let mut compilation = Compilation::default();
    for path in summary_paths {
        let text = read_summary(&path)?;
        compilation.add_external_summary(&path, text);
    }
    for digest in trusted {
        compilation.trust_summary(digest);
    }
    let Some(file_count) = load_sources(&mut compilation, paths, mode, output, error)? else {
        return Ok(2);
    };
    compile_output(&mut compilation, mode, emit, file_count, output, error)
}

fn compile_output(
    compilation: &mut Compilation,
    mode: Mode,
    emit: Emit,
    file_count: usize,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    if emit == Emit::Mono {
        return emit_monomorphized(compilation, output, error);
    }
    let mut mir = None;
    let hir = if mode == Mode::Check {
        if emit == Emit::Interface {
            compilation.check_types()
        } else if emit == Emit::Mir {
            compilation.check_mir().map(|(hir, lowered)| {
                mir = Some(lowered);
                hir
            })
        } else {
            compilation.check()
        }
    } else {
        None
    };
    emit_local(compilation, emit, output)?;
    if emit_diagnostics(compilation, error)? {
        return Ok(1);
    }
    if let Some(mir) = mir {
        let hir = hir.as_ref().expect("MIR emission retains its typed HIR");
        output.write_all(mir.dump(hir, &compilation.symbols).as_bytes())?;
        if let Some(analysis) = &compilation.mir_analysis {
            output.write_all(analysis.dump().as_bytes())?;
        }
        return Ok(0);
    }
    emit_success(
        compilation,
        hir.as_ref(),
        mode,
        emit,
        file_count,
        output,
        error,
    )
}

fn emit_monomorphized(
    compilation: &mut Compilation,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let program = compilation.check_monomorphized();
    if emit_diagnostics(compilation, error)? {
        return Ok(1);
    }
    output.write_all(
        program
            .expect("checked monomorphization")
            .dump(&compilation.symbols)
            .as_bytes(),
    )?;
    Ok(0)
}

fn emit_local(compilation: &Compilation, emit: Emit, output: &mut dyn Write) -> io::Result<()> {
    if emit != Emit::Local {
        return Ok(());
    }
    if let Some(report) = &compilation.local_analysis {
        writeln!(output, "{report:#?}")?;
        symbols(compilation, output)?;
    } else if let Some(analysis) = &compilation.mir_analysis {
        output.write_all(analysis.dump().as_bytes())?;
    }
    Ok(())
}
fn emit_diagnostics(compilation: &Compilation, error: &mut dyn Write) -> io::Result<bool> {
    if compilation.diagnostics.is_empty() {
        return Ok(false);
    }
    for diagnostic in &compilation.diagnostics {
        error.write_all(diagnostic.render(&compilation.sources).as_bytes())?;
    }
    let count = compilation.diagnostics.len();
    let suffix = if count == 1 { "" } else { "s" };
    writeln!(
        error,
        "error: aborting due to {count} previous error{suffix}"
    )?;
    Ok(true)
}
fn emit_success(
    compilation: &Compilation,
    program: Option<&crate::hir::Program>,
    mode: Mode,
    emit: Emit,
    file_count: usize,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    match mode {
        Mode::Check => {
            if emit == Emit::Interface {
                let program = program.expect("typed HIR");
                let Some(interface) = crate::external::interface::interfaces(
                    program,
                    &compilation.symbols,
                    &compilation.sources,
                ) else {
                    writeln!(
                        error,
                        "cavoite: interface fingerprint exceeds its resource limit"
                    )?;
                    return Ok(1);
                };
                output.write_all(crate::external::interface::render(&interface).as_bytes())?;
            } else if emit == Emit::Hir {
                writeln!(
                    output,
                    "{:#?}",
                    program.expect("no diagnostics implies typed HIR")
                )?;
                symbols(compilation, output)?;
            } else if emit != Emit::Local {
                let analysis = if compilation.mir_analysis.is_some() {
                    "MIR ownership, region, cleanup and effect checks applied"
                } else {
                    "whole-program local move/borrow checks applied"
                };
                writeln!(
                    output,
                    "type-checked {file_count} file(s); {analysis}; full ownership/effect/contract verification is pending"
                )?;
            }
        }
        Mode::Parse => {
            writeln!(output, "{:#?}", compilation.ast)?;
            symbols(compilation, output)?;
        }
        Mode::Lex => {}
        Mode::SummaryId => unreachable!("handled before parsing"),
    }
    Ok(0)
}

fn load_sources(
    compilation: &mut Compilation,
    paths: Vec<PathBuf>,
    mode: Mode,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<Option<usize>> {
    let mut count = 0;
    for path in paths {
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(problem) => {
                writeln!(error, "cavoite: {}: {problem}", path.display())?;
                return Ok(None);
            }
        };
        let file = match compilation.sources.add(&path, text) {
            Ok(file) => file,
            Err(problem) => {
                writeln!(error, "cavoite: {}: {problem}", path.display())?;
                return Ok(None);
            }
        };
        count += 1;
        if mode == Mode::Lex {
            let source = compilation.sources.file(file);
            let tokens = lexer::lex(
                source,
                &mut compilation.symbols,
                &mut compilation.diagnostics,
            );
            for token in tokens {
                writeln!(
                    output,
                    "{}:{}..{} {:?} {:?}",
                    path.display(),
                    token.span.start,
                    token.span.end,
                    token.kind,
                    source.slice(token.span)
                )?;
            }
        } else {
            compilation.parse(file);
        }
    }
    Ok(Some(count))
}

fn read_summary(path: &std::path::Path) -> io::Result<String> {
    use std::io::Read;
    let file = std::fs::File::open(path)?;
    let mut text = String::new();
    file.take(262_145).read_to_string(&mut text)?;
    if text.len() > 262_144 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "external summary exceeds 256 KiB",
        ));
    }
    Ok(text)
}

fn symbols(compilation: &Compilation, output: &mut dyn Write) -> io::Result<()> {
    writeln!(output, "symbols:")?;
    for (symbol, text) in compilation.symbols.entries() {
        writeln!(output, "  {}: {text:?}", symbol.0)?;
    }
    Ok(())
}
