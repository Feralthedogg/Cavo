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
    let mut diagnostics = Vec::new();
    program.analysis.diagnostics(&mut diagnostics);
    if let Some(diagnostic) = diagnostics.into_iter().next() {
        return Err(Error {
            code: diagnostic.code,
            span: diagnostic.primary,
            message: diagnostic.message,
        });
    }
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
    let internal = program.hir.internal_definitions();
    let mut entries = program.mir.functions.iter().filter(|body| {
        let definition = &program.hir.definitions[body.definition];
        symbols.get(definition.name) == "main" && !internal.contains(&body.definition)
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

#[cfg(test)]
mod native_status_tests {
    use super::*;
    use crate::{Compilation, native};
    use std::{
        path::{Path, PathBuf},
        process::Command,
        sync::atomic::{AtomicU64, Ordering},
    };

    const SOURCE: &str = r#"
@lang(drop) trait Drop { void drop(&mut Self self); }
struct Child<'a> { &'a mut i32 counter; }
impl<'a> Drop for Child<'a> {
    void drop(&mut Self self) { *self.counter += 1; }
}
struct Parent<'a, 'b> { &'a mut i32 observed; Child<'b> child; }
impl<'a, 'b> Drop for Parent<'a, 'b> {
    void drop(&mut Self self) { *self.observed = *self.child.counter; }
}
i32 failure() { return 0; }
i32 inspect(&mut i32 observed, &mut i32 counter) {
    Parent value = Parent { observed: &mut *observed, child: Child { counter: &mut *counter } };
    return failure();
}
i32 main() { return 0; }
"#;

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let root = Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .unwrap()
                .join("target/native-status-tests");
            std::fs::create_dir_all(&root).unwrap();
            assert!(
                !std::fs::symlink_metadata(&root)
                    .unwrap()
                    .file_type()
                    .is_symlink()
            );
            let path = root.join(format!(
                "{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn llvm() -> Option<PathBuf> {
        let explicit = std::env::var_os("CAVO_LLVM_BIN").map(PathBuf::from);
        let required = explicit.is_some() || std::env::var_os("CAVO_NATIVE_REQUIRED").is_some();
        let path = explicit
            .or_else(|| {
                ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"]
                    .into_iter()
                    .map(PathBuf::from)
                    .find(|path| path.join("llc").is_file())
            })
            .filter(|path| {
                Command::new(path.join(if cfg!(windows) { "llc.exe" } else { "llc" }))
                    .arg("--version")
                    .output()
                    .is_ok_and(|output| {
                        output.status.success()
                            && String::from_utf8_lossy(&output.stdout)
                                .split_whitespace()
                                .any(|word| word == native::LLVM_VERSION)
                    })
            });
        assert!(
            path.is_some() || !required,
            "native cleanup tests require LLVM 23.1.2"
        );
        path
    }

    fn program(reason: Option<mir::ExitKind>) -> (Compilation, mono::Program, hir::DefId) {
        let mut compilation = Compilation::default();
        let file = compilation
            .sources
            .add("native-status.cavo", SOURCE.into())
            .unwrap();
        compilation.parse(file);
        let mut program = compilation
            .check_monomorphized()
            .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
        if let Some(reason) = reason {
            inject_status(&mut program, &compilation.symbols, reason);
        }
        program.analysis = mir::analyze(
            &program.mir,
            &mut program.hir,
            &compilation.symbols,
            &[],
            &compilation.sources,
        )
        .unwrap_or_else(|error| panic!("{}: {}", error.code, error.message));
        let mut errors = Vec::new();
        program.analysis.diagnostics(&mut errors);
        assert!(errors.is_empty(), "{errors:#?}");
        let id = program
            .mir
            .functions
            .iter()
            .find(|body| {
                compilation
                    .symbols
                    .get(program.hir.definitions[body.definition].name)
                    == "inspect"
            })
            .unwrap()
            .definition;
        (compilation, program, id)
    }

    fn inject_status(program: &mut mono::Program, symbols: &Interner, reason: mir::ExitKind) {
        // A test-only execution stimulus exercises the ABI's abnormal returns.
        // Revalidate and recompute every report; this never approves source.
        let body = program
            .mir
            .functions
            .iter_mut()
            .find(|body| symbols.get(program.hir.definitions[body.definition].name) == "failure")
            .unwrap();
        for block in &mut body.blocks {
            if matches!(block.terminator, mir::Terminator::Return) {
                block.statements.push(mir::Statement {
                    kind: mir::StatementKind::StorageDead(body.return_local),
                    span: block.span,
                });
                block.terminator = mir::Terminator::Resume(reason);
                block.cleanup = Some(reason);
            }
        }
        program.mir.validate(&mut program.hir).unwrap();
    }

    #[test]
    fn transformed_destructor_cancellation_cannot_reach_codegen() {
        let (compilation, mut program, _) = program(None);
        let body = program
            .mir
            .functions
            .iter_mut()
            .find(|body| {
                compilation
                    .symbols
                    .get(program.hir.definitions[body.definition].name)
                    == "drop"
            })
            .unwrap();
        for block in &mut body.blocks {
            if matches!(block.terminator, mir::Terminator::Return) {
                block.statements.push(mir::Statement {
                    kind: mir::StatementKind::StorageDead(body.return_local),
                    span: block.span,
                });
                block.terminator = mir::Terminator::Resume(mir::ExitKind::Cancel);
                block.cleanup = Some(mir::ExitKind::Cancel);
            }
        }
        program.mir.validate(&mut program.hir).unwrap();
        program.analysis = mir::analyze(
            &program.mir,
            &mut program.hir,
            &compilation.symbols,
            &[],
            &compilation.sources,
        )
        .unwrap_or_else(|error| panic!("{}: {}", error.code, error.message));
        assert!(!program.analysis.effects.violations.is_empty());
        assert!(
            emit(
                &mut program,
                &compilation.symbols,
                "x86_64-unknown-linux-gnu"
            )
            .is_err()
        );
    }

    fn harness(path: &Path, definition: hir::DefId, status: i32) {
        let text = format!(
            r#"
extern int __cavo_f_{}(void *, void *, void *, void *);
_Noreturn void cavo_rt_abort(void) {{ __builtin_trap(); }}
int main(void) {{
    int observed = 0, counter = 5, result = -1;
    void *first = &observed, *second = &counter;
    int status = __cavo_f_{}(0, &result, &first, &second);
    return status == {} && observed == 5 && counter == 6 && result == {} ? 0 : 91;
}}
"#,
            definition.0,
            definition.0,
            status,
            if status == 0 { 0 } else { -1 }
        );
        std::fs::write(path, text).unwrap();
    }

    fn link(llvm: &Path, source: &Path, object: &Path, output: &Path) {
        let mut command =
            Command::new(llvm.join(if cfg!(windows) { "clang.exe" } else { "clang" }));
        command.args(["-std=c11", "-fno-crash-diagnostics"]);
        if cfg!(target_os = "macos") {
            let sdk = Command::new("xcrun")
                .arg("--show-sdk-path")
                .output()
                .unwrap();
            assert!(sdk.status.success());
            command
                .arg("-isysroot")
                .arg(String::from_utf8(sdk.stdout).unwrap().trim());
        }
        let result = command
            .arg(source)
            .arg(object)
            .arg("-o")
            .arg(output)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }

    #[test]
    fn native_normal_panic_cancel_keep_result_storage_and_drop_order() {
        let Some(llvm) = llvm() else {
            return;
        };
        for optimization in [native::Optimization::O0, native::Optimization::O2] {
            for (reason, status) in [
                (None, 0),
                (Some(mir::ExitKind::Panic), 1),
                (Some(mir::ExitKind::Cancel), 2),
            ] {
                let scratch = Scratch::new();
                let (compilation, mut program, definition) = program(reason);
                let object = scratch.0.join("program.o");
                let options = native::Options {
                    llvm_bin: Some(llvm.clone()),
                    runtime: native::Runtime::None,
                    optimization,
                    ..native::Options::default()
                };
                native::build(
                    &mut program,
                    &compilation.symbols,
                    &options,
                    native::OutputKind::Object,
                    &object,
                )
                .unwrap();
                let source = scratch.0.join("harness.c");
                let output = scratch.0.join(if cfg!(windows) {
                    "harness.exe"
                } else {
                    "harness"
                });
                harness(&source, definition, status);
                link(&llvm, &source, &object, &output);
                let result = Command::new(output).output().unwrap();
                assert!(
                    result.status.success(),
                    "{reason:?} at {optimization:?}: {result:?}"
                );
            }
        }
    }
}
