use super::*;
use crate::{external::digest::sha256, native as backend};
use std::{
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
};

pub(super) fn tool(
    options: &options::Options,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let root = match project_root(options, None) {
        Ok(root) => root,
        Err(message) => return simple_error("E-NATIVE-PROJECT", &message, error),
    };
    match options.mode {
        Mode::Clean => clean(&root, output, error),
        Mode::Sdk => prepare(options, &root, output, error),
        Mode::Doctor => doctor(options, &root, output, error),
        _ => simple_error("E-NATIVE-COMMAND", "invalid native tool command", error),
    }
}

struct Invocation {
    compiler: backend::Compiler,
    store: outputs::Store,
    path: PathBuf,
}

pub(super) fn compile(
    compilation: &mut Compilation,
    options: &options::Options,
    package: Option<&crate::packages::Graph>,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let program = compilation.check_executable();
    if emit_diagnostics(compilation, error)? {
        return Ok(1);
    }
    let Some(mut program) = program else {
        return simple_error("E-NATIVE-INPUT", "no checked executable artifact", error);
    };
    let invocation = match invocation(options, package) {
        Ok(invocation) => invocation,
        Err(problem) => return report(problem, Some(compilation), error),
    };
    if let Err(problem) = emit_artifact(
        &invocation,
        &mut program,
        &compilation.symbols,
        options.emit,
    ) {
        return report(problem, Some(compilation), error);
    }
    if options.mode == Mode::Run {
        // Inherit terminal streams without unbounded buffering. The owning
        // invocation keeps the output lock until the child has exited.
        return match Command::new(&invocation.path).status() {
            Ok(status) => Ok(status_code(status)),
            Err(problem) => simple_error("E-NATIVE-RUN", &problem.to_string(), error),
        };
    }
    writeln!(output, "built {}", invocation.path.display())?;
    Ok(0)
}

fn invocation(
    options: &options::Options,
    package: Option<&crate::packages::Graph>,
) -> Result<Invocation, backend::Error> {
    let root = project_root(options, package)
        .map_err(|message| native_error("E-NATIVE-PROJECT", message))?;
    let compiler = backend::Compiler::new(&settings(options, &root))?;
    let store =
        outputs::Store::open(&root).map_err(|message| native_error("E-NATIVE-OUTPUT", message))?;
    let path = output_path(options, package, &compiler, &store)
        .map_err(|message| native_error("E-NATIVE-OUTPUT", message))?;
    Ok(Invocation {
        compiler,
        store,
        path,
    })
}

fn emit_artifact(
    invocation: &Invocation,
    program: &mut crate::mono::Program,
    symbols: &crate::symbol::Interner,
    emit: Emit,
) -> Result<(), backend::Error> {
    if emit == Emit::LlvmIr {
        let text = invocation.compiler.llvm_ir(program, symbols)?;
        outputs::atomic_text(&invocation.path, &text)
            .map_err(|message| native_error("E-NATIVE-OUTPUT", message))?;
    } else {
        let kind = if emit == Emit::Object {
            backend::OutputKind::Object
        } else {
            backend::OutputKind::Executable
        };
        invocation
            .compiler
            .build(program, symbols, kind, &invocation.path)?;
    }
    invocation
        .store
        .record(&invocation.path)
        .map_err(|message| {
            native_error(
                "E-NATIVE-OWNERSHIP",
                format!(
                    "{} was built but its ownership record failed: {message}",
                    invocation.path.display()
                ),
            )
        })
}

fn native_error(code: &'static str, message: String) -> backend::Error {
    backend::Error {
        code,
        span: None,
        message,
    }
}

fn project_root(
    options: &options::Options,
    package: Option<&crate::packages::Graph>,
) -> Result<PathBuf, String> {
    if let Some(package) = package {
        return package
            .lock_path
            .parent()
            .ok_or("package has no project root")
            .map(Path::to_path_buf)
            .map_err(str::to_owned);
    }
    if let Some(path) = &options.manifest {
        return path
            .canonicalize()
            .map_err(|error| error.to_string())?
            .parent()
            .ok_or("manifest has no project root")
            .map(Path::to_path_buf)
            .map_err(str::to_owned);
    }
    std::env::current_dir().map_err(|error| error.to_string())
}

fn settings(options: &options::Options, root: &Path) -> backend::Options {
    let mut settings = options.native.backend.clone();
    if settings.llam_sdk.is_none() && std::env::var_os("CAVO_LLAM_SDK").is_none() {
        settings.llam_sdk = Some(root.join("target/cavo-native-sdk/llam-3.0.0"));
    }
    settings
}

fn output_path(
    options: &options::Options,
    package: Option<&crate::packages::Graph>,
    compiler: &backend::Compiler,
    store: &outputs::Store,
) -> Result<PathBuf, String> {
    if let Some(path) = &options.native.output {
        return if path.is_absolute() {
            Ok(path.clone())
        } else {
            std::env::current_dir()
                .map(|root| root.join(path))
                .map_err(|error| error.to_string())
        };
    }
    let name = if let Some(package) = package {
        package.packages[package.root].manifest.name.clone()
    } else {
        let name = options.paths[0]
            .file_stem()
            .ok_or("source path has no file name")?;
        name.to_str().map(str::to_owned).unwrap_or_else(|| {
            format!(
                "program-{}",
                &sha256(name.as_encoded_bytes()).to_string()[7..23]
            )
        })
    };
    let extension = match options.emit {
        Emit::LlvmIr => Some("ll"),
        Emit::Object => Some(if cfg!(windows) { "obj" } else { "o" }),
        _ if cfg!(windows) => Some("exe"),
        _ => None,
    };
    store.output(
        compiler.target(),
        options.native.backend.optimization.profile(),
        &name,
        extension,
    )
}

fn prepare(
    options: &options::Options,
    root: &Path,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let destination = options
        .native
        .output
        .clone()
        .unwrap_or_else(|| root.join("target/cavo-native-sdk/llam-3.0.0"));
    match backend::prepare_sdk(
        options.native.source.as_deref().expect("validated source"),
        options.native.build.as_deref().expect("validated build"),
        &destination,
    ) {
        Ok(()) => {
            writeln!(
                output,
                "prepared LLAM {} SDK: {}",
                backend::LLAM_RELEASE,
                destination.display()
            )?;
            Ok(0)
        }
        Err(problem) => report(problem, None, error),
    }
}

fn doctor(
    options: &options::Options,
    root: &Path,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    let settings = settings(options, root);
    let store = if options.native.probe && settings.runtime == backend::Runtime::Llam {
        match outputs::Store::open(root) {
            Ok(store) => Some(store),
            Err(message) => return simple_error("E-NATIVE-OUTPUT", &message, error),
        }
    } else {
        None
    };
    match backend::diagnose(
        &settings,
        store.as_ref().map_or(root, |store| store.root.as_path()),
        options.native.probe,
    ) {
        Ok(report) => {
            print_doctor(&report, settings.runtime, output)?;
            Ok(0)
        }
        Err(problem) => report(problem, None, error),
    }
}

fn print_doctor(
    report: &backend::Doctor,
    runtime: backend::Runtime,
    output: &mut dyn Write,
) -> io::Result<()> {
    writeln!(
        output,
        "cavoite {} / native toolchain",
        env!("CARGO_PKG_VERSION")
    )?;
    writeln!(output, "Rust: {}", report.rust)?;
    writeln!(
        output,
        "LLVM: {} ({})",
        backend::LLVM_VERSION,
        report.llvm_bin.display()
    )?;
    writeln!(
        output,
        "target: {}\nsysroot: {}",
        report.target, report.sysroot
    )?;
    writeln!(
        output,
        "LLAM: {} / {}",
        backend::LLAM_RELEASE,
        backend::LLAM_REVISION
    )?;
    writeln!(output, "public ABI: 2.4\nmanaged compiler ABI: 1.0 / LLPM2")?;
    if let Some(sdk) = &report.sdk {
        writeln!(output, "SDK: {}", sdk.display())?;
    }
    if let Some(producer) = &report.producer {
        writeln!(output, "SDK producer: {producer}")?;
    }
    if let Some(verifier) = &report.verifier {
        writeln!(output, "image verifier: {verifier}")?;
    }
    writeln!(
        output,
        "requested policy: {}",
        if runtime == backend::Runtime::Llam {
            "async-required"
        } else {
            "runtime disabled"
        }
    )?;
    writeln!(output, "effective policy: {}", report.effective_policy)?;
    writeln!(
        output,
        "runtime admission probe: {}",
        if report.probed { "passed" } else { "not run" }
    )
}

fn clean(root: &Path, output: &mut dyn Write, error: &mut dyn Write) -> io::Result<u8> {
    if !root.join("target/cavo").try_exists()? {
        writeln!(output, "removed 0 owned output(s)")?;
        return Ok(0);
    }
    let store = match outputs::Store::open(root) {
        Ok(store) => store,
        Err(message) => return simple_error("E-NATIVE-OUTPUT", &message, error),
    };
    let result = match store.clean() {
        Ok(result) => result,
        Err(message) => return simple_error("E-NATIVE-OUTPUT", &message, error),
    };
    writeln!(output, "removed {} owned output(s)", result.removed)?;
    for (path, message) in &result.preserved {
        writeln!(error, "preserved {}: {message}", path.display())?;
    }
    Ok(u8::from(!result.preserved.is_empty()))
}

fn report(
    problem: backend::Error,
    compilation: Option<&Compilation>,
    error: &mut dyn Write,
) -> io::Result<u8> {
    if let (Some(span), Some(compilation)) = (problem.span, compilation) {
        error.write_all(
            crate::diagnostic::Diagnostic::error(problem.code, problem.message, span)
                .render(&compilation.sources)
                .as_bytes(),
        )?;
    } else {
        writeln!(error, "error[{}]: {}", problem.code, problem.message)?;
    }
    Ok(1)
}
fn simple_error(code: &str, message: &str, error: &mut dyn Write) -> io::Result<u8> {
    writeln!(error, "error[{code}]: {message}")?;
    Ok(1)
}
fn status_code(status: ExitStatus) -> u8 {
    if let Some(code) = status.code() {
        return if code == 0 {
            0
        } else {
            u8::try_from(code)
                .ok()
                .filter(|&code| code != 0)
                .unwrap_or(1)
        };
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        status
            .signal()
            .and_then(|signal| u8::try_from(128 + signal).ok())
            .unwrap_or(1)
    }
    #[cfg(not(unix))]
    {
        1
    }
}
