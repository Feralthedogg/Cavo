use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let parent = root().join("target/native-cli-tests");
        fs::create_dir_all(&parent).unwrap();
        let path = parent.join(format!(
            "{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("app.cavo"), "i32 main() { return 42; }\n").unwrap();
        Self(path)
    }
    fn run(&self, arguments: &[&str]) -> Output {
        let mut command = self.command();
        command.args(arguments);
        command.output().unwrap()
    }
    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_cavoite"));
        command.current_dir(&self.0);
        if let Some(llvm) = llvm() {
            command.env("CAVO_LLVM_BIN", llvm);
        }
        if let Some(sdk) = sdk() {
            command.env("CAVO_LLAM_SDK", sdk);
        }
        command
    }
    fn build(&self, arguments: &[&str]) -> PathBuf {
        let result = self.run(arguments);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let output = String::from_utf8(result.stdout).unwrap();
        PathBuf::from(output.trim().strip_prefix("built ").unwrap())
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}
fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
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
                            .any(|word| word == cavo_compiler::native::LLVM_VERSION)
                })
        });
    assert!(
        path.is_some() || !required,
        "native CLI tests require LLVM 23.1.2"
    );
    path
}
fn sdk() -> Option<PathBuf> {
    let path = std::env::var_os("CAVO_LLAM_SDK")
        .map(PathBuf::from)
        .or_else(|| {
            let path = root().join("target/cavo-native-sdk/llam-3.0.0");
            path.join("cavo-sdk.json").is_file().then_some(path)
        });
    assert!(
        path.is_some() || std::env::var_os("CAVO_MANAGED_REQUIRED").is_none(),
        "required LLAM SDK missing"
    );
    path
}

#[test]
fn native_build_run_and_owned_paths_work_at_debug_and_release() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    for release in [false, true] {
        let args = if release {
            vec!["build", "--runtime=none", "--release", "app.cavo"]
        } else {
            vec!["build", "--runtime=none", "app.cavo"]
        };
        let path = fixture.build(&args);
        assert!(path.starts_with(fixture.0.join("target/cavo")));
        let profile = if release { "release" } else { "debug" };
        assert!(
            path.components()
                .any(|component| component.as_os_str() == profile)
        );
        assert_eq!(Command::new(path).status().unwrap().code(), Some(42));
        let args = if release {
            vec!["run", "--runtime=none", "--release", "app.cavo"]
        } else {
            vec!["run", "--runtime=none", "app.cavo"]
        };
        assert_eq!(fixture.run(&args).status.code(), Some(42));
    }
}

#[test]
fn requested_ir_and_objects_are_the_only_retained_codegen_files() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let ir = fixture.build(&["build", "--emit=llvm-ir", "app.cavo"]);
    assert!(fs::read_to_string(ir).unwrap().contains("Cavo checked MIR"));
    let object = fixture.build(&["build", "--runtime=none", "--emit=obj", "app.cavo"]);
    assert!(fs::metadata(object).unwrap().len() > 0);
    let executable = fixture.build(&["build", "--runtime=none", "app.cavo"]);
    for entry in fs::read_dir(executable.parent().unwrap()).unwrap() {
        let path = entry.unwrap().path();
        assert!(
            !path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with(".cavo-native")
        );
        assert_ne!(path.file_name().unwrap(), "optimized.ll");
        assert_ne!(path.file_name().unwrap(), "program.mir");
    }
}

#[test]
fn clean_preserves_modified_unowned_sources_and_sdk_data() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let path = fixture.build(&["build", "--runtime=none", "app.cavo"]);
    let original = fs::read(&path).unwrap();
    let mut changed = original.clone();
    changed.push(0);
    fs::write(&path, changed).unwrap();
    let foreign = path.parent().unwrap().join("user-data.txt");
    fs::write(&foreign, "keep").unwrap();
    let sdk = fixture.0.join("target/cavo-native-sdk");
    fs::create_dir_all(&sdk).unwrap();
    fs::write(sdk.join("keep"), "dependency").unwrap();
    let result = fixture.run(&["clean"]);
    assert_eq!(result.status.code(), Some(1));
    assert!(
        path.exists()
            && foreign.exists()
            && sdk.join("keep").exists()
            && fixture.0.join("app.cavo").exists()
    );
    fs::write(&path, original).unwrap();
    let result = fixture.run(&["clean"]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(!path.exists());
    assert!(foreign.exists() && sdk.join("keep").exists());
}

#[test]
fn clean_rejects_forged_traversal_and_serializes_with_active_operations() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    fixture.build(&["build", "--runtime=none", "app.cavo"]);
    let lock = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(fixture.0.join("target/cavo/.cavo-lock"))
        .unwrap();
    lock.lock().unwrap();
    assert_eq!(fixture.run(&["clean"]).status.code(), Some(1));
    lock.unlock().unwrap();
    let source = fixture.0.join("app.cavo");
    let record = fixture
        .0
        .join("target/cavo/.ownership")
        .join(format!("{}.json", "a".repeat(64)));
    let digest = cavo_compiler::external::digest::sha256(&fs::read(&source).unwrap());
    fs::write(&record, format!("{{\"schema\":1,\"tool\":\"cavoite\",\"path\":\"../../app.cavo\",\"sha256\":\"{digest}\"}}")).unwrap();
    assert_eq!(fixture.run(&["clean"]).status.code(), Some(1));
    assert!(source.exists() && record.exists());
}

#[cfg(unix)]
#[test]
fn clean_does_not_follow_file_or_parent_symlinks() {
    use std::os::unix::fs::symlink;
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let path = fixture.build(&["build", "--runtime=none", "app.cavo"]);
    let saved = fixture.0.join("saved-executable");
    fs::rename(&path, &saved).unwrap();
    symlink(fixture.0.join("app.cavo"), &path).unwrap();
    assert_eq!(fixture.run(&["clean"]).status.code(), Some(1));
    assert!(
        fixture.0.join("app.cavo").exists()
            && fs::symlink_metadata(&path)
                .unwrap()
                .file_type()
                .is_symlink()
    );
    fs::remove_file(&path).unwrap();
    fs::rename(&saved, &path).unwrap();
    let parent = path.parent().unwrap();
    let outside = fixture.0.join("moved-profile");
    fs::rename(parent, &outside).unwrap();
    symlink(&outside, parent).unwrap();
    assert_eq!(fixture.run(&["clean"]).status.code(), Some(1));
    assert!(outside.join(path.file_name().unwrap()).exists());
}

#[test]
fn native_failures_preserve_previous_output_and_have_stage_specific_errors() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let path = fixture.build(&["build", "--runtime=none", "app.cavo"]);
    let before = fs::read(&path).unwrap();
    fs::write(fixture.0.join("app.cavo"), "i32 main() { return true; }").unwrap();
    let result = fixture.run(&["build", "--runtime=none", "app.cavo"]);
    assert_eq!(result.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&result.stderr).contains("E-TYPE-MISMATCH"));
    assert_eq!(before, fs::read(&path).unwrap());
    fs::write(fixture.0.join("app.cavo"), "i32 main() { return 42; }").unwrap();
    let result = fixture.run(&["build", "--llam-sdk", "missing-sdk", "app.cavo"]);
    assert_eq!(result.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&result.stderr).contains("E-LLAM-SDK"));
    assert_eq!(before, fs::read(&path).unwrap());
}

#[test]
fn managed_build_run_and_doctor_report_real_admission() {
    if llvm().is_none() || sdk().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let path = fixture.build(&["build", "app.cavo"]);
    assert_eq!(Command::new(path).status().unwrap().code(), Some(42));
    assert_eq!(fixture.run(&["run", "app.cavo"]).status.code(), Some(42));
    let result = fixture.run(&["doctor"]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let report = String::from_utf8(result.stdout).unwrap();
    for expected in [
        "Rust:",
        "LLVM: 23.1.2",
        "target:",
        "sysroot:",
        "LLAM: 3.0.0",
        "public ABI: 2.4",
        "managed compiler ABI: 1.0",
        "SDK producer: sha256:",
        "image verifier: sha256:",
        "requested policy: async-required",
        "effective policy: async-required",
        "runtime admission probe: passed",
    ] {
        assert!(report.contains(expected), "missing {expected}: {report}");
    }
    assert!(
        !fs::read_dir(fixture.0.join("target/cavo"))
            .unwrap()
            .any(|entry| entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".cavo-native"))
    );
}

#[test]
fn native_option_validation_does_not_silently_enable_other_profiles() {
    let fixture = Fixture::new();
    for arguments in [
        vec!["run", "--emit=obj", "app.cavo"],
        vec!["check", "-O2", "app.cavo"],
        vec!["build", "--offline", "app.cavo"],
        vec!["build", "--runtime=cooperative", "app.cavo"],
        vec!["build", "--lto", "app.cavo"],
        vec!["build", "-fsanitize=address", "app.cavo"],
        vec!["sdk", "--llam-source", ".", "--llam-build", ".", "-O0"],
        vec![
            "sdk",
            "--llam-source",
            ".",
            "--llam-build",
            ".",
            "--no-probe",
        ],
    ] {
        assert_eq!(
            fixture.run(&arguments).status.code(),
            Some(2),
            "{arguments:?}"
        );
    }
    let grammar = fixture.run(&["--grammar"]);
    assert!(grammar.status.success());
    assert!(String::from_utf8_lossy(&grammar.stdout).contains("frozen source grammar"));
}

#[test]
fn dotted_names_and_explicit_outputs_keep_their_requested_identity() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    fs::rename(fixture.0.join("app.cavo"), fixture.0.join("app.test.cavo")).unwrap();
    let ir = fixture.build(&["build", "--emit=llvm-ir", "app.test.cavo"]);
    assert_eq!(ir.file_name().unwrap(), "app.test.ll");
    let explicit = fixture.build(&["build", "--runtime=none", "-o", "chosen", "app.test.cavo"]);
    assert_eq!(explicit, fixture.0.join("chosen"));
    assert_eq!(Command::new(&explicit).status().unwrap().code(), Some(42));
    assert!(fixture.run(&["clean"]).status.success());
    assert!(!ir.exists() && explicit.exists());
}

#[test]
fn package_build_obeys_the_lock_and_places_outputs_beside_the_manifest() {
    if llvm().is_none() {
        return;
    }
    let fixture = Fixture::new();
    fs::create_dir(fixture.0.join("pkg")).unwrap();
    fs::create_dir(fixture.0.join("pkg/src")).unwrap();
    fs::rename(
        fixture.0.join("app.cavo"),
        fixture.0.join("pkg/src/main.cavo"),
    )
    .unwrap();
    fs::write(
        fixture.0.join("pkg/Cavo.toml"),
        "[package]\nname = \"sample\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let result = fixture.run(&["lock", "--manifest-path", "pkg/Cavo.toml", "--offline"]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let path = fixture.build(&[
        "build",
        "--manifest-path",
        "pkg/Cavo.toml",
        "--locked",
        "--offline",
        "--runtime=none",
    ]);
    assert!(path.starts_with(fixture.0.join("pkg/target/cavo")));
    assert_eq!(Command::new(&path).status().unwrap().code(), Some(42));
    fs::write(
        fixture.0.join("pkg/src/main.cavo"),
        "i32 main() { return 7; }",
    )
    .unwrap();
    let result = fixture.run(&[
        "build",
        "--manifest-path",
        "pkg/Cavo.toml",
        "--locked",
        "--runtime=none",
    ]);
    assert_eq!(result.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&result.stderr).contains("Cavo.lock"));
    assert_eq!(Command::new(path).status().unwrap().code(), Some(42));
}

#[test]
fn doctor_does_not_claim_an_unrun_probe_passed() {
    if llvm().is_none() || sdk().is_none() {
        return;
    }
    let fixture = Fixture::new();
    let result = fixture.run(&["doctor", "--no-probe"]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let text = String::from_utf8(result.stdout).unwrap();
    assert!(text.contains("effective policy: not measured (--no-probe)"));
    assert!(text.contains("runtime admission probe: not run"));
    assert!(!fixture.0.join("target").exists());
}
