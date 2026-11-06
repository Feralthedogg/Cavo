use cavo_compiler::{
    Compilation,
    native::{self, Options, OutputKind, Runtime},
};
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("target/native-tests");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join(format!(
            "{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn executable(&self) -> PathBuf {
        self.0.join(if cfg!(windows) {
            "program.exe"
        } else {
            "program"
        })
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn llvm() -> Option<PathBuf> {
    let explicit = std::env::var_os("CAVO_LLVM_BIN").map(PathBuf::from);
    let root = explicit.or_else(|| {
        ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"]
            .map(PathBuf::from)
            .into_iter()
            .find(|root| root.join("llc").is_file())
    });
    assert!(
        root.is_some() || std::env::var_os("CAVO_NATIVE_REQUIRED").is_none(),
        "native tests require LLVM 23.1.2"
    );
    root
}

fn parsed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("native.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn run(source: &str, expected: i32) {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation = parsed(source);
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let options = Options {
        runtime: Runtime::None,
        llvm_bin: Some(llvm_bin),
        ..Options::default()
    };
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .unwrap();
    let result = Command::new(fixture.executable()).output().unwrap();
    assert_eq!(
        result.status.code(),
        Some(expected),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn native_integer_calls_branches_and_loops() {
    run(
        "i32 twice(i32 n) { return n * 2; } i32 main() { i32 n = 0; for (i32 i = 0; i < 6; i += 1) { n += twice(i); } return n; }",
        30,
    );
}

#[test]
fn native_nominal_moves_and_explicit_copies_preserve_value_storage() {
    run(
        "struct Data { i32 value; } i32 main() { Data first = Data { value: 3 }; Data second = move first; return second.value + second.value; }",
        6,
    );
    run(
        "@lang(copy) trait Copy {} struct Data { i32 value; } impl Copy for Data {} i32 main() { Data first = Data { value: 3 }; Data second = first; return first.value + second.value; }",
        6,
    );
}

#[test]
fn native_aggregate_and_enum_layouts_preserve_payload_offsets() {
    run(
        "enum Choice { No, Yes(i32) } struct Pair { byte tag; Choice choice; } i32 main() { Pair pair = Pair { tag: 1, choice: Choice::Yes(37) }; return match pair.choice { Choice::Yes(value) => value, Choice::No => 0 }; }",
        37,
    );
}

#[test]
fn native_arrays_slices_and_owned_iteration() {
    run(
        "i32 first(&[i32] values) { return values[1]; } i32 main() { i32[3] values = [2, 7, 4]; i32 n = first(&values); for (auto value in move values) { n += value; } return n; }",
        20,
    );
}

#[test]
fn native_scalar_contract_failure_is_fatal() {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation = parsed(
        "i32 positive(i32 n) requires n > 0 { return n; } i32 main() { return positive(0); }",
    );
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let options = Options {
        runtime: Runtime::None,
        llvm_bin: Some(llvm_bin),
        ..Options::default()
    };
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .unwrap();
    let result = Command::new(fixture.executable()).output().unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("E-RUNTIME-CHECK"));
}

fn managed_sdk() -> Option<PathBuf> {
    use std::sync::OnceLock;
    static SDK: OnceLock<PathBuf> = OnceLock::new();
    if let Some(path) = std::env::var_os("CAVO_LLAM_SDK") {
        return Some(PathBuf::from(path));
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let source = root.parent().unwrap().join("LLAM");
    let build = source.join("build-async-all-os");
    if !build.join("llam_managed_pass.so").is_file() {
        assert!(
            std::env::var_os("CAVO_MANAGED_REQUIRED").is_none(),
            "managed tests require a qualified LLAM SDK"
        );
        return None;
    }
    Some(
        SDK.get_or_init(|| {
            let destination = root.join("target/cavo-native-sdk/llam-3.0.0");
            native::prepare_sdk(&source, &build, &destination).unwrap();
            destination
        })
        .clone(),
    )
}

#[test]
fn qualified_llam_runs_the_generated_entry_without_a_compatibility_fallback() {
    let (Some(llvm_bin), Some(llam_sdk)) = (llvm(), managed_sdk()) else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation =
        parsed("i32 twice(i32 n) { return n + n; } i32 main() { return twice(21); }");
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let options = Options {
        runtime: Runtime::Llam,
        llvm_bin: Some(llvm_bin),
        llam_sdk: Some(llam_sdk),
    };
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .unwrap();
    let result = Command::new(fixture.executable())
        .env("CAVO_RUNTIME_STATS", "1")
        .output()
        .unwrap();
    assert_eq!(
        result.status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        !result.stderr.is_empty(),
        "the real runtime must supply its statistics"
    );
}
