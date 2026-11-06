use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}
fn sample(name: &str) -> PathBuf {
    root().join("examples/frontend").join(name)
}

#[test]
fn all_four_frontend_stages_integrate_without_a_native_toolchain() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let run = |emit| {
        Command::new(binary)
            .arg(emit)
            .arg(sample("features.cavo"))
            .env("PATH", "")
            .output()
            .unwrap()
    };
    let first = run("--emit=mono");
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let second = run("--emit=mono");
    assert!(second.status.success());
    assert_eq!(first.stdout, second.stdout);
    let dump = String::from_utf8(first.stdout).unwrap();
    for expected in [
        "monomorphized HIR/MIR / no native code generated",
        "instance i",
        "layout ",
        "align=16",
        "user Drop ",
        "dyn_call ",
        "MIR borrow analysis",
        "MIR effects",
        "cancel bb",
    ] {
        assert!(dump.contains(expected), "missing {expected}:\n{dump}");
    }
    let report = run("--emit=local");
    assert!(
        report.status.success(),
        "{}",
        String::from_utf8_lossy(&report.stderr)
    );
    assert!(
        String::from_utf8(report.stdout)
            .unwrap()
            .contains("MIR borrow analysis")
    );
}

#[test]
fn monomorphized_emission_requires_semantic_checking() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let wrong_mode = Command::new(binary)
        .args(["parse", "--emit=mono"])
        .arg(sample("features.cavo"))
        .output()
        .unwrap();
    assert_eq!(wrong_mode.status.code(), Some(2));
    assert!(
        String::from_utf8(wrong_mode.stderr)
            .unwrap()
            .contains("monomorphized emission requires check mode")
    );
}

#[test]
fn mir_dump_is_deterministic_and_needs_no_backend() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let run = || {
        Command::new(binary)
            .arg("--emit=mir")
            .arg(sample("mir.cavo"))
            .env("PATH", "")
            .output()
            .unwrap()
    };
    let first = run();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let second = run();
    assert!(second.status.success());
    assert_eq!(first.stdout, second.stdout);
    let dump = String::from_utf8(first.stdout).unwrap();
    for expected in [
        "cavoite MIR / stage=cleanup-foundation",
        "not an ownership certificate",
        "fn frontend::mir::count",
        "switch ",
        " = call ",
        " -> normal bb",
        ", panic bb",
        ", cancel bb",
        "drop_if_initialized ",
        "explicit drop flags and glue",
        "MIR borrow analysis / local domain",
        "MIR effects / before runtime",
        "storage_dead ",
        "@file0:",
    ] {
        assert!(dump.contains(expected), "missing {expected:?}:\n{dump}");
    }
    assert!(!dump.contains("type-checked"));
    let wrong_mode = Command::new(binary)
        .args(["parse", "--emit=mir"])
        .arg(sample("mir.cavo"))
        .output()
        .unwrap();
    assert_eq!(wrong_mode.status.code(), Some(2));
    assert!(
        String::from_utf8(wrong_mode.stderr)
            .unwrap()
            .contains("MIR emission requires check mode")
    );
}

#[test]
fn external_summary_identity_interface_and_assumptions_work_without_external_programs() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/external.cavo");
    let summary = source.with_extension("cavosum");
    let identity = Command::new(binary)
        .arg("summary-id")
        .arg(&summary)
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        identity.status.success(),
        "{}",
        String::from_utf8_lossy(&identity.stderr)
    );
    let digest = String::from_utf8(identity.stdout).unwrap();
    assert_eq!(
        digest.trim(),
        cavo_compiler::external::Summaries::digest(&std::fs::read_to_string(&summary).unwrap())
            .to_string()
    );
    let interface = Command::new(binary)
        .arg("--emit=interface")
        .arg(&source)
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        interface.status.success(),
        "{}",
        String::from_utf8_lossy(&interface.stderr)
    );
    let interface = String::from_utf8(interface.stdout).unwrap();
    assert!(interface.contains("frontend::external::external_identity"));
    assert!(interface.contains("\"schema\": 1"));
    assert!(!interface.contains("type-checked"));
    let checked = Command::new(binary)
        .arg("--summary")
        .arg(&summary)
        .arg("--trust-summary")
        .arg(digest.trim())
        .arg("--emit=local")
        .arg(&source)
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    let report = String::from_utf8(checked.stdout).unwrap();
    assert!(report.contains("summaries:"));
    assert!(report.contains("Assumed"));
    assert!(report.contains("AssumptionId"));
    assert!(report.contains("verdict: Undetermined"));
}

#[test]
fn cli_requires_explicit_summary_trust_and_reports_english_source_links() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/external.cavo");
    let summary = source.with_extension("cavosum");
    let output = Command::new(binary)
        .arg("--summary")
        .arg(&summary)
        .arg("--emit=local")
        .arg(&source)
        .env("PATH", "")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let diagnostic = String::from_utf8(output.stderr).unwrap();
    assert!(diagnostic.contains("error[E-SUMMARY-UNTRUSTED]"));
    assert!(diagnostic.contains("summary was loaded without granting trust"));
    assert!(diagnostic.contains("::: "));
    assert!(diagnostic.contains("external.cavosum:1:1"));
    for arguments in [
        vec!["--trust-summary", "sha256:bad"],
        vec!["--summary"],
        vec!["parse", "--emit=interface", "file.cavo"],
    ] {
        assert_eq!(
            Command::new(binary)
                .args(arguments)
                .output()
                .unwrap()
                .status
                .code(),
            Some(2)
        );
    }
    let example = Command::new(binary)
        .arg(sample("higher.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        example.status.success(),
        "{}",
        String::from_utf8_lossy(&example.stderr)
    );
}

#[test]
fn check_runs_offline_without_llvm_or_runtime_and_accepts_multiple_modules() {
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("check")
        .arg(sample("main.cavo"))
        .arg(sample("math.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("type-checked 2 file(s)"));
    assert!(text.contains("verification is pending"));
}

#[test]
fn memory_transformers_and_schema_two_stores_are_visible_in_the_cli() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let example = Command::new(binary)
        .arg("--emit=local")
        .arg(sample("memory.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        example.status.success(),
        "{}",
        String::from_utf8_lossy(&example.stderr)
    );
    let dump = String::from_utf8(example.stdout).unwrap();
    assert!(dump.contains("MemorySummary"));
    assert!(dump.contains("MemoryWrite"));
    assert!(dump.contains("normal_return: true"));
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/memory.cavo");
    let summary = source.with_extension("cavosum");
    let digest =
        cavo_compiler::external::Summaries::digest(&std::fs::read_to_string(&summary).unwrap());
    let checked = Command::new(binary)
        .arg("--emit=local")
        .arg("--summary")
        .arg(&summary)
        .arg("--trust-summary")
        .arg(digest.to_string())
        .arg(&source)
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    let dump = String::from_utf8(checked.stdout).unwrap();
    assert!(dump.contains("schema: 2"));
    assert!(dump.contains("ReferenceStore"));
    assert!(dump.contains("Assumed"));
}

#[test]
fn cavoite_emits_resolved_hir_and_unproven_stage() {
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("--emit=hir")
        .arg(sample("math.cavo"))
        .arg(sample("main.cavo"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("stage: Types"));
    assert!(text.contains("CoerceArrayToSlice"));
    assert!(text.contains("identity"));
    assert!(text.contains("TypeAlias"));
}

#[test]
fn parser_accepts_future_runtime_syntax_without_claiming_to_check_it() {
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("parse")
        .arg(sample("syntax.cavo"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("Contract")
    );
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("check")
        .arg(sample("syntax.cavo"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("E-FRONTEND-STAGE")
    );
}

#[test]
fn semantic_failures_have_exit_code_one_and_source_location() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/wrong-type.cavo");
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("check")
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("E-TYPE-MISMATCH"));
    assert!(error.contains("wrong-type.cavo:2:12"), "{error}");
    assert!(error.contains("error[E-TYPE-MISMATCH]: mismatched types\n"));
    assert!(error.contains("^^^^ expected `i32`, found `bool`"));
    assert!(error.ends_with("error: aborting due to 1 previous error\n"));
    assert!(!error.contains('\u{1b}'));
}

#[test]
fn cli_handles_spaces_io_failures_and_unsupported_backend_options() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/with spaces.cavo");
    assert!(
        Command::new(env!("CARGO_BIN_EXE_cavoite"))
            .arg(path)
            .output()
            .unwrap()
            .status
            .success()
    );
    assert_eq!(
        Command::new(env!("CARGO_BIN_EXE_cavoite"))
            .arg("--emit=llvm-ir")
            .output()
            .unwrap()
            .status
            .code(),
        Some(2)
    );
    assert_eq!(
        Command::new(env!("CARGO_BIN_EXE_cavoite"))
            .arg("missing-input.cavo")
            .output()
            .unwrap()
            .status
            .code(),
        Some(2)
    );
}

#[test]
fn token_dump_keeps_raw_source_and_original_spans() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/with spaces.cavo");
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("lex")
        .arg(path)
        .output()
        .unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains(":0..3 Ident("));
    assert!(text.contains("\"i32\""));
}

#[test]
fn executable_identity_help_version_and_errors_use_cavoite() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let help = Command::new(binary).arg("--help").output().unwrap();
    assert!(help.status.success());
    let help = String::from_utf8(help.stdout).unwrap();
    assert!(help.contains("Usage: cavoite "));
    assert!(!help.contains("Usage: cavo ") && !help.contains("cavoc "));

    let version = Command::new(binary).arg("--version").output().unwrap();
    assert!(version.status.success());
    assert!(
        String::from_utf8(version.stdout)
            .unwrap()
            .starts_with("cavoite ")
    );

    let failure = Command::new(binary).arg("--unknown").output().unwrap();
    assert_eq!(failure.status.code(), Some(2));
    assert!(
        String::from_utf8(failure.stderr)
            .unwrap()
            .starts_with("cavoite: ")
    );
}

#[test]
fn local_dump_exposes_cfg_and_incomplete_coverage_without_a_backend() {
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("--emit=local")
        .arg(sample("local.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("verdict: Undetermined"));
    assert!(text.contains("not_analyzed:"));
    assert!(text.contains("LocalCheck"));
    assert!(text.contains("BorrowExclusive"));
    assert_eq!(
        Command::new(env!("CARGO_BIN_EXE_cavoite"))
            .arg("parse")
            .arg("--emit=local")
            .arg(sample("local.cavo"))
            .output()
            .unwrap()
            .status
            .code(),
        Some(2)
    );
}

#[test]
fn failed_local_checks_still_emit_the_rejected_source_backed_report() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/moved-reference.cavo");
    let output = Command::new(env!("CARGO_BIN_EXE_cavoite"))
        .arg("--emit=local")
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("verdict: Rejected"));
    assert!(text.contains("NotEstablished"));
    assert!(text.contains("EventId"));
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("E-MOVE-USE")
    );
}

#[test]
fn field_loans_expose_place_paths_and_english_conflict_labels() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let success = Command::new(binary)
        .arg("--emit=local")
        .arg(sample("fields.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        success.status.success(),
        "{}",
        String::from_utf8_lossy(&success.stderr)
    );
    let dump = String::from_utf8(success.stdout).unwrap();
    assert!(dump.contains("places:"));
    assert!(dump.contains("FieldProjection"));
    assert!(dump.contains("verdict: Undetermined"));

    let failure = Command::new(binary)
        .arg("--emit=local")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/field-borrow.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert_eq!(failure.status.code(), Some(1));
    let error = String::from_utf8(failure.stderr).unwrap();
    assert!(error.contains("error[E-BORROW-CONFLICT]"), "{error}");
    assert!(error.contains("field-borrow.cavo:8:5"), "{error}");
    assert!(error.contains("conflicting borrow starts here"), "{error}");
    assert!(
        error.contains("this place overlaps a borrow that is still active"),
        "{error}"
    );
    assert!(
        String::from_utf8(failure.stdout)
            .unwrap()
            .contains("verdict: Rejected")
    );
}

#[test]
fn partial_moves_and_nll_run_without_a_backend_and_reject_future_borrow_uses() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let good = Command::new(binary)
        .arg("--emit=local")
        .arg(sample("ownership.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        good.status.success(),
        "{}",
        String::from_utf8_lossy(&good.stderr)
    );
    let dump = String::from_utf8(good.stdout).unwrap();
    assert!(dump.contains("NllReport"));
    assert!(dump.contains("block_entry:"));
    assert!(dump.contains("verdict: Undetermined"));

    let bad = Command::new(binary)
        .arg("check")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/nll-borrow.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert_eq!(bad.status.code(), Some(1));
    let error = String::from_utf8(bad.stderr).unwrap();
    assert!(error.contains("error[E-BORROW-CONFLICT]"), "{error}");
    assert!(error.contains("nll-borrow.cavo:4:5"), "{error}");
    assert!(error.contains("conflicting borrow starts here"), "{error}");
    assert!(error.contains("including possible cleanup use"), "{error}");
}

#[test]
fn function_regions_and_reborrows_have_source_backed_reports_and_english_errors() {
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let good = Command::new(binary)
        .arg("--emit=local")
        .arg(sample("regions.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert!(
        good.status.success(),
        "{}",
        String::from_utf8_lossy(&good.stderr)
    );
    let dump = String::from_utf8(good.stdout).unwrap();
    assert!(dump.contains("RegionContract"));
    assert!(dump.contains("body_checked: true"));
    assert!(dump.contains("Reborrow"));
    assert!(dump.contains("verdict: Undetermined"));
    let bad = Command::new(binary)
        .arg("--emit=local")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/region-return.cavo"))
        .env("PATH", "")
        .output()
        .unwrap();
    assert_eq!(bad.status.code(), Some(1));
    let error = String::from_utf8(bad.stderr).unwrap();
    assert!(error.contains("error[E-REGION-RETURN]"), "{error}");
    assert!(error.contains("region-return.cavo:2:5"), "{error}");
    assert!(
        error.contains("return region is declared by this signature"),
        "{error}"
    );
    assert!(
        String::from_utf8(bad.stdout)
            .unwrap()
            .contains("body_checked: false")
    );
}
