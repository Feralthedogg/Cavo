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
    let required = explicit.is_some() || std::env::var_os("CAVO_NATIVE_REQUIRED").is_some();
    let root = explicit.or_else(|| {
        ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"]
            .map(PathBuf::from)
            .into_iter()
            .find(|root| root.join("llc").is_file())
    });
    let root = root.filter(|root| {
        Command::new(root.join(if cfg!(windows) { "llc.exe" } else { "llc" }))
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
        root.is_some() || !required,
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
    run_at(source, expected, native::Optimization::O2);
}

fn run_at(source: &str, expected: i32, optimization: native::Optimization) {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation = parsed(source);
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let options = Options {
        optimization,
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
fn native_o0_and_o2_preserve_values_and_defined_traps() {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    for optimization in [native::Optimization::O0, native::Optimization::O2] {
        run_at(
            "i32 main() { i32 n = 0; for (i32 i = 0; i < 4; i += 1) { n += i; } return n; }",
            6,
            optimization,
        );
        for source in [
            "i32 add(i32 n) { return n + 1; } i32 main() { return add(2147483647); }",
            "i32 div(i32 n, i32 d) { return n / d; } i32 main() { return div(3, 0); }",
            "i32 shift(i32 n, i32 bits) { return n << bits; } i32 main() { return shift(1, 32); }",
            "i32 get(usize n) { i32[2] data = [1, 2]; return data[n]; } i32 main() { return get(2); }",
        ] {
            let fixture = Fixture::new();
            let mut compilation = parsed(source);
            let mut program = compilation
                .check_executable()
                .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
            let options = Options {
                optimization,
                llvm_bin: Some(llvm_bin.clone()),
                runtime: Runtime::None,
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
            assert!(
                !result.status.success(),
                "accepted trap at {optimization:?}: {source}"
            );
            assert!(String::from_utf8_lossy(&result.stderr).contains("E-RUNTIME-CHECK"));
        }
    }
}

#[test]
fn raw_llvm_ir_does_not_invent_alias_range_or_arithmetic_facts() {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let mut compilation = parsed(
        "i32 add(&mut i32 first, &i32 second) { return *first + *second; } i32 main() { i32 a = 1; i32 b = 2; return add(&mut a, &b); }",
    );
    let mut program = compilation.check_executable().unwrap();
    let ir = native::llvm_ir(
        &mut program,
        &compilation.symbols,
        &Options {
            llvm_bin: Some(llvm_bin),
            ..Options::default()
        },
    )
    .unwrap();
    for unproved in [
        " noalias ",
        "getelementptr inbounds",
        " add nsw ",
        " add nuw ",
        " shl nsw ",
        " shl nuw ",
    ] {
        assert!(
            !ir.contains(unproved),
            "unproved fact in emitted IR: {unproved}"
        );
    }
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
fn native_user_drop_and_owned_iteration_reclaim_each_initialized_element_once() {
    run(
        "@lang(drop) trait Drop { void drop(&mut Self self); } struct Mark<'a> { &'a mut i32 counter; } impl<'a> Drop for Mark<'a> { void drop(&mut Self self) { *self.counter += 1; } } i32 main() { i32 a = 0; i32 b = 0; i32 c = 0; { Mark[3] marks = [Mark { counter: &mut a }, Mark { counter: &mut b }, Mark { counter: &mut c }]; for (auto mark in move marks) { break; } } return a + b + c; }",
        3,
    );
}

#[test]
fn native_heap_intrinsics_preserve_typed_initialization_and_free() {
    run(
        "@lang(copy) trait Copy {} @intrinsic(allocate) ptr<T> allocate<T>(usize count); @intrinsic(ptr_initialize) void initialize<T>(ptr<T> p, T value); @intrinsic(ptr_read) T read<T: Copy>(ptr<T> p); @intrinsic(deallocate) void release<T>(ptr<T> p); i32 main() { contract { auto p = allocate::<i32>(1); initialize(p, 19); i32 value = read(p); release(p); return value; } }",
        19,
    );
}

const TASKS: &str = "@lang(result) enum Outcome<T,E> { Ok(T), Err(E) } @lang(task) struct Work<'scope,T> {} @lang(spawn_error) struct Admission<F> { F capture; } @lang(task_error) enum Fault { Cancelled, Panicked }";

fn scoped_program() -> Compilation {
    parsed(&format!(
        "{TASKS} void child(&i32 value) {{ i32 n = *value; }} void main() {{ i32 value = 1; scope {{ auto receipt = spawn child(&value); }} }}"
    ))
}

#[test]
fn missing_scope_lifetime_barrier_preserves_the_previous_artifact() {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let fixture = Fixture::new();
    std::fs::write(fixture.executable(), b"previous artifact").unwrap();
    let mut compilation = scoped_program();
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let options = Options {
        llvm_bin: Some(llvm_bin),
        ..Options::default()
    };
    let error = native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "E-RUNTIME-SCOPE-DRAIN");
    assert_eq!(
        std::fs::read(fixture.executable()).unwrap(),
        b"previous artifact"
    );
}

#[test]
#[ignore = "0.1 release gate: pinned LLAM 3.0.0 lacks a cancellation-immune managed group barrier"]
fn scoped_borrows_require_runtime_barrier() {
    let options = Options {
        llvm_bin: Some(llvm().expect("required LLVM producer")),
        llam_sdk: Some(managed_sdk().expect("required LLAM SDK")),
        runtime: Runtime::Llam,
        optimization: native::Optimization::O2,
    };
    let fixture = Fixture::new();
    let mut compilation = scoped_program();
    let mut program = compilation
        .check_executable()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .expect("the required scoped lifetime barrier must work before 0.1 release");
    assert!(
        Command::new(fixture.executable())
            .status()
            .unwrap()
            .success()
    );
}

#[test]
fn incompatible_sdk_profile_is_rejected_before_any_output_is_published() {
    let Some(llvm_bin) = llvm() else {
        return;
    };
    let fixture = Fixture::new();
    let sdk = fixture.0.join("bad-sdk");
    std::fs::create_dir(&sdk).unwrap();
    std::fs::write(
        sdk.join("cavo-sdk.json"),
        "{\"schema\":1,\"runtime\":\"2.0.0\",\"revision\":\"wrong\",\"llvm\":\"23.1.2\"}",
    )
    .unwrap();
    let mut compilation = parsed("i32 main() { return 0; }");
    let mut program = compilation.check_executable().unwrap();
    let options = Options {
        llvm_bin: Some(llvm_bin),
        llam_sdk: Some(sdk),
        runtime: Runtime::Llam,
        optimization: native::Optimization::O2,
    };
    let error = native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "E-LLAM-SDK");
    assert!(!fixture.executable().exists());
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
        optimization: native::Optimization::O2,
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

#[test]
fn managed_o0_is_qualified_without_repeating_the_ir_pass() {
    let (Some(llvm_bin), Some(llam_sdk)) = (llvm(), managed_sdk()) else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation = parsed("i32 main() { i32 value = 21; return value + value; }");
    let mut program = compilation.check_executable().unwrap();
    let options = Options {
        llvm_bin: Some(llvm_bin),
        llam_sdk: Some(llam_sdk),
        optimization: native::Optimization::O0,
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
    let before = std::fs::read(fixture.executable()).unwrap();
    assert!(native::verify_image(&fixture.executable(), &options).unwrap() > 0);
    assert_eq!(
        before,
        std::fs::read(fixture.executable()).unwrap(),
        "verification modified the sealed image"
    );
    let result = Command::new(fixture.executable()).output().unwrap();
    assert_eq!(
        result.status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn managed_image_verifier_rejects_missing_or_corrupted_seals() {
    let (Some(llvm_bin), Some(llam_sdk)) = (llvm(), managed_sdk()) else {
        return;
    };
    let fixture = Fixture::new();
    let mut compilation = parsed("i32 main() { return 42; }");
    let mut program = compilation.check_executable().unwrap();
    let mut options = Options {
        llvm_bin: Some(llvm_bin),
        llam_sdk: Some(llam_sdk.clone()),
        ..Options::default()
    };
    options.runtime = Runtime::None;
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .unwrap();
    assert_eq!(
        native::verify_image(&fixture.executable(), &options)
            .unwrap_err()
            .code,
        "E-LLAM-VERIFY"
    );
    options.runtime = Runtime::Llam;
    native::build(
        &mut program,
        &compilation.symbols,
        &options,
        OutputKind::Executable,
        &fixture.executable(),
    )
    .unwrap();
    corrupt_managed_identity(&fixture.executable(), &llam_sdk);
    assert_eq!(
        native::verify_image(&fixture.executable(), &options)
            .unwrap_err()
            .code,
        "E-LLAM-VERIFY"
    );
    resign_fixture(&fixture.executable());
    let result = Command::new(fixture.executable()).output().unwrap();
    assert_eq!(
        result.status.code(),
        Some(125),
        "runtime admitted a stale image identity"
    );
    assert!(String::from_utf8_lossy(&result.stderr).contains("E-RUNTIME-START"));
}

fn resign_fixture(image: &Path) {
    if cfg!(target_os = "macos") {
        let result = Command::new("/usr/bin/codesign")
            .args(["--force", "--sign", "-"])
            .arg(image)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

fn corrupt_managed_identity(image: &Path, sdk: &Path) {
    // Use the pinned LLPM2 parser to locate the seal; never guess an ELF/Mach-O
    // section offset or change the SDK/runtime dependency itself.
    let script = r#"
import importlib.util, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location('llam_verify_fixture', sys.argv[1])
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
path = Path(sys.argv[2])
image = module.read_image(path)
records = module.parse_records(image)
data = bytearray(image.data)
data[records[0].file_offset + 104] ^= 1
path.write_bytes(data)
"#;
    let result = Command::new("python3")
        .args(["-B", "-c", script])
        .arg(sdk.join("libexec/llam/managed_verify.py"))
        .arg(image)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}
