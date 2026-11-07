use crate::{Compilation, syntax::lexer};
use std::{
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

mod modules;
mod native;
mod options;
mod outputs;

const HELP: &str = r#"Cavo compiler

Usage: cavoite [check|parse|lex] [--emit=ast|hir|mir|mono|local|tokens|interface|contracts|module] FILE...
       cavoite check --manifest-path Cavo.toml [--locked] [--offline]
       cavoite lock --manifest-path Cavo.toml [--offline]
       cavoite summary-id FILE
       cavoite build|run [--release|-O0|-O2] [--llvm-bin DIR] [--llam-sdk DIR] [-o FILE] FILE...
       cavoite build [--emit=llvm-ir|obj] [--runtime=llam|none] FILE...
       cavoite doctor [--llvm-bin DIR] [--llam-sdk DIR] [--no-probe]
       cavoite sdk --llam-source DIR --llam-build DIR [-o PREFIX]
       cavoite clean [--manifest-path Cavo.toml]

check  Check types, ownership, regions, contracts, effects and scoped tasks (default).
parse  Parse the language grammar and dump AST.
lex    Dump tokens with original UTF-8 byte spans.
build  Emit native code using pinned LLVM 23.1.2 and LLAM 3.0.0.
run    Build and run; propagate the program's exit status.
doctor Check tools, SDK identities and required asynchronous runtime admission.
clean  Remove only unchanged native outputs confirmed by ownership records.

--summary FILE          Load a versioned external summary without trusting it.
--trust-summary DIGEST  Pin a reviewed document's sha256 identity as an assumption.
--emit=interface        Emit declaration fingerprints; type checking only.
--emit=local            Dump CFG, findings and external assumption dependencies.
--emit=mir              Lower and verify MIR with explicit cleanup paths.
--emit=mono             Instantiate generics; dump concrete MIR, layout and glue.
--emit=contracts        Emit versioned evidence, assumptions and retained checks as JSON.
--emit=module           Emit a checked frontend module capsule; no native object code.
--module FILE           Load and independently recheck a module capsule.
--manifest-path FILE    Resolve the package's declared sources and pinned dependencies.
--locked                Require an exact Cavo.lock match.
--offline               Use local sources and already cached pinned Git dependencies.
--grammar               Print the frozen Cavo 0.1 EBNF.

Native outputs use target/cavo/<triple>/<debug|release>/. Temporary IR is removed
unless --emit=llvm-ir is requested. The default runtime policy is async-required;
--runtime=none selects explicit native diagnostics mode. Check/parse/lex need no
LLVM or runtime. Scoped tasks require the unavailable cancellation-immune drain
and are rejected by native emission until that runtime contract is implemented.
"#;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Check,
    Parse,
    Lex,
    SummaryId,
    Lock,
    Build,
    Run,
    Doctor,
    Clean,
    Sdk,
}
impl Mode {
    fn native(self) -> bool {
        matches!(self, Self::Build | Self::Run)
    }
    fn tool(self) -> bool {
        matches!(self, Self::Doctor | Self::Clean | Self::Sdk)
    }
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
    Module,
    Contracts,
    LlvmIr,
    Object,
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
            writeln!(output, "cavoite {}", env!("CARGO_PKG_VERSION"))?;
            return Ok(0);
        }
        Ok(options::Action::Grammar) => {
            output.write_all(crate::syntax::GRAMMAR.as_bytes())?;
            return Ok(0);
        }
        Ok(options::Action::Run(options)) => *options,
        Err(options::Error::Usage) => {
            error.write_all(HELP.as_bytes())?;
            return Ok(2);
        }
        Err(options::Error::Message(message)) => {
            writeln!(error, "cavoite: {message}")?;
            return Ok(2);
        }
    };
    execute(options, output, error)
}

fn execute(
    options: options::Options,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    if options.mode.tool() {
        return native::tool(&options, output, error);
    }
    if options.mode == Mode::SummaryId {
        let text = read_summary(&options.paths[0])?;
        writeln!(output, "{}", crate::external::Summaries::digest(&text))?;
        return Ok(0);
    }
    let package = if let Some(path) = &options.manifest {
        match crate::packages::resolve(path, options.locked, options.offline) {
            Ok(graph) => Some(graph),
            Err(message) => {
                writeln!(error, "cavoite: {message}")?;
                return Ok(1);
            }
        }
    } else {
        None
    };
    if options.mode == Mode::Lock {
        let graph = package.expect("validated lock options");
        return match graph.write_lock() {
            Ok(()) => {
                writeln!(output, "locked {} package(s)", graph.packages.len())?;
                Ok(0)
            }
            Err(message) => {
                writeln!(error, "cavoite: {message}")?;
                Ok(1)
            }
        };
    }
    let mode = options.mode;
    let emit = options.emit;
    let Some((mut compilation, count)) = load_inputs(&options, package.as_ref(), output, error)?
    else {
        return Ok(2);
    };
    if mode.native() {
        return native::compile(&mut compilation, &options, package.as_ref(), output, error);
    }
    compile_output(&mut compilation, mode, emit, count, output, error)
}

fn load_inputs(
    options: &options::Options,
    package: Option<&crate::packages::Graph>,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<Option<(Compilation, usize)>> {
    let mut compilation = Compilation::default();
    if !modules::load(&mut compilation, &options.modules, error)? {
        return Ok(None);
    }
    for path in &options.summary_paths {
        let text = read_summary(path)?;
        compilation.add_external_summary(path, text);
    }
    for &digest in &options.trusted {
        compilation.trust_summary(digest);
    }
    let files = if let Some(package) = package {
        modules::load_package(&mut compilation, package, error)?
    } else {
        load_sources(
            &mut compilation,
            &options.paths,
            options.mode,
            output,
            error,
        )?
    };
    Ok(files.map(|count| (compilation, count)))
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
    if emit == Emit::Module {
        return modules::emit(compilation, output, error);
    }
    let mut mir = None;
    let hir = if mode == Mode::Check {
        if emit == Emit::Interface {
            compilation.check_types()
        } else if matches!(emit, Emit::Mir | Emit::Contracts) {
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
    if emit == Emit::Contracts
        && let Some(analysis) = &compilation.mir_analysis
    {
        output.write_all(analysis.contracts.json(&compilation.sources).as_bytes())?;
    }
    if emit_diagnostics(compilation, error)? {
        return Ok(1);
    }
    if let Some(mir) = mir {
        if emit == Emit::Contracts {
            return Ok(0);
        }
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
                return emit_interface(compilation, program.expect("typed HIR"), output, error);
            } else if emit == Emit::Hir {
                writeln!(
                    output,
                    "{:#?}",
                    program.expect("no diagnostics implies typed HIR")
                )?;
                symbols(compilation, output)?;
            } else if emit != Emit::Local {
                let analysis = if compilation.mir_analysis.is_some() {
                    "MIR ownership, region, cleanup, effect, contract and task checks applied"
                } else {
                    "whole-program local move/borrow checks applied"
                };
                writeln!(
                    output,
                    "type-checked {file_count} file(s); {analysis}; native code and runtime verification is pending"
                )?;
            }
        }
        Mode::Parse => {
            writeln!(output, "{:#?}", compilation.ast)?;
            symbols(compilation, output)?;
        }
        Mode::Lex => {}
        Mode::SummaryId
        | Mode::Lock
        | Mode::Build
        | Mode::Run
        | Mode::Doctor
        | Mode::Clean
        | Mode::Sdk => unreachable!("handled before frontend output"),
    }
    Ok(0)
}

fn emit_interface(
    compilation: &Compilation,
    program: &crate::hir::Program,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let Some(interface) =
        crate::external::interface::interfaces(program, &compilation.symbols, &compilation.sources)
    else {
        writeln!(
            error,
            "cavoite: interface fingerprint exceeds its resource limit"
        )?;
        return Ok(1);
    };
    let Some(copy) = crate::external::interface::copy_permissions(
        program,
        &compilation.symbols,
        &compilation.sources,
    ) else {
        writeln!(
            error,
            "cavoite: Copy interface identities exceed their resource limit"
        )?;
        return Ok(1);
    };
    output.write_all(crate::external::interface::render_with_copy(&interface, &copy).as_bytes())?;
    Ok(0)
}

fn load_sources(
    compilation: &mut Compilation,
    paths: &[PathBuf],
    mode: Mode,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<Option<usize>> {
    let mut count = 0;
    for path in paths {
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(problem) => {
                writeln!(error, "cavoite: {}: {problem}", path.display())?;
                return Ok(None);
            }
        };
        let file = match compilation.sources.add(path, text) {
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
