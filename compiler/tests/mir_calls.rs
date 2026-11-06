use cavo_compiler::{Compilation, external, hir, mir};
use mir::borrow::{FindingKind, GapKind, Verdict};

fn parsed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("mir-calls.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn analyze(source: &str) -> mir::borrow::Report {
    let mut compilation = parsed(source);
    let mut hir = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let core = mir::lower(&mut hir).unwrap();
    mir::borrow::analyze(&core, &mut hir).unwrap()
}

fn established(report: &mir::borrow::Report) {
    assert!(
        report
            .functions
            .iter()
            .all(|function| function.verdict == Verdict::Established),
        "{report:#?}"
    );
}

#[test]
fn incomplete_generic_shapes_retain_known_local_origins() {
    for source in [
        "T identity<T>(T value) { return move value; } trait Marker {} &'a i32 bad<'a>(&'a i32 input) { i32 local = 1; return identity(&local); }",
        "struct Hold<T> { T value; } Hold<T> wrap<T>(T value) { return Hold { value: move value }; } trait Marker {} &'a i32 bad<'a>(&'a i32 input) { i32 local = 1; auto held = wrap(&local); return held.value; }",
    ] {
        let mut compilation = parsed(source);
        assert!(
            compilation.check().is_none(),
            "unsafe generic escape accepted: {source}"
        );
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E-MIR-BORROW"),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn direct_reference_returns_are_checked_from_mir_in_both_declaration_orders() {
    let identity = "&'a i32 identity<'a>(&'a i32 value) { return value; }";
    let caller = "i32 f() { i32 value = 7; &i32 view = identity(&value); return *view; }";
    for source in [
        format!("{identity} {caller}"),
        format!("{caller} {identity}"),
    ] {
        established(&analyze(&source));
    }
}

#[test]
fn source_signature_regions_reject_an_unrelated_return_origin() {
    let report = analyze("&'a i32 wrong<'a,'b>(&'a i32 left, &'b i32 right) { return right; }");
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.kind == FindingKind::RegionMismatch)
    );
}

#[test]
fn static_inputs_and_mutable_nested_regions_are_checked_independently_of_bodies() {
    let report = analyze(
        "void require_static(&'static i32 value) {} void f() { i32 value = 1; require_static(&value); }",
    );
    assert_eq!(
        report.functions[1].verdict,
        Verdict::Rejected,
        "{report:#?}"
    );
    established(&analyze(
        "&'a &'a i32 shrink<'a,'b>(&'a &'b i32 value) { return value; }",
    ));
    let report =
        analyze("&'a mut &'a i32 wrong<'a,'b>(&'a mut &'b i32 value) { return move value; }");
    assert_eq!(
        report.functions[0].verdict,
        Verdict::Rejected,
        "{report:#?}"
    );
}

#[test]
fn known_function_values_returned_by_factories_keep_their_call_summary() {
    let source = "type RefFn = for<'a> fn(&'a i32) -> &'a i32; &'a i32 identity<'a>(&'a i32 value) { return value; } RefFn factory() { return identity; } i32 f() { i32 value = 3; RefFn function = factory(); return *function(&value); }";
    established(&analyze(source));
}

#[test]
fn reference_stores_replace_origins_in_callers() {
    let source = "void put<'a>(&mut &'a i32 slot, &'a i32 next) { *slot = next; } i32 f() { i32 old = 1; i32 fresh = 2; &i32 slot = &old; put(&mut slot, &fresh); old = 3; return *slot; }";
    established(&analyze(source));
    let report = analyze(&source.replace("old = 3", "fresh = 3"));
    assert_eq!(
        report.functions[1].verdict,
        Verdict::Rejected,
        "{report:#?}"
    );
}

#[test]
fn nested_reads_and_swaps_use_one_entry_snapshot() {
    let source = "void swap<'a>(&mut &'a i32 left, &mut &'a i32 right) { &'a i32 saved = *left; *left = *right; *right = saved; } i32 f() { i32 a = 1; i32 b = 2; &i32 left = &a; &i32 right = &b; swap(&mut left, &mut right); return *left + *right; }";
    established(&analyze(source));
    let report = analyze(&source.replace("return *left + *right", "a = 5; return *right"));
    assert_eq!(
        report.functions[1].verdict,
        Verdict::Rejected,
        "{report:#?}"
    );
}

#[test]
fn recursive_components_reach_a_reference_summary_fixed_point() {
    let report = analyze(
        "&'a i32 walk<'a>(&'a i32 value, bool done) { if (done) { return value; } return walk(value, true); } i32 f() { i32 x = 1; return *walk(&x, false); }",
    );
    established(&report);
    assert!(
        report
            .summaries
            .iter()
            .all(|summary| summary.normal.is_some())
    );
}

#[test]
fn returned_reborrows_freeze_the_parent_until_the_childs_last_use() {
    let base = "&mut i32 child(&mut i32 value) { return &mut *value; } void f() { i32 x = 1; &mut i32 parent = &mut x; &mut i32 view = child(parent); *view = 2; *parent = 3; }";
    established(&analyze(base));
    let report = analyze(&base.replace("*view = 2; *parent = 3;", "*parent = 3; *view = 2;"));
    assert_eq!(
        report.functions[1].verdict,
        Verdict::Rejected,
        "{report:#?}"
    );
}

fn trusted(source: &str, returns: &str, stores: Option<&str>) -> (Compilation, hir::Program) {
    let mut compilation = parsed(source);
    let hir = compilation.check_types().unwrap();
    let declaration =
        external::interface::interfaces(&hir, &compilation.symbols, &compilation.sources)
            .unwrap()
            .remove(0);
    let (schema, writes, stores) = stores.map_or((1, "[]", String::new()), |stores| {
        (2, "[0]", format!(",\"stores\":{stores}"))
    });
    let document = format!(
        r#"{{"schema":{schema},"id":"mir","version":"1","artifact":"sha256:{}","functions":[{{"name":"{}","abi":"{}","signature":"{}","effects":{{"no_retain":true,"no_free":true,"no_callback":true,"no_unwind":true,"no_suspend":true,"no_block":true,"no_allocate":true,"preserves_validity":true,"reads":[0],"writes":{writes}{stores}}},"returns":[{returns}]}}]}}"#,
        "a".repeat(64),
        declaration.name,
        declaration.abi,
        declaration.signature
    );
    let digest = compilation
        .add_external_summary("mir.cavosum", document)
        .unwrap();
    compilation.trust_summary(digest);
    let hir = compilation
        .check()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, hir)
}

#[test]
fn trusted_external_returns_keep_assumptions_through_source_wrappers() {
    let (compilation, mut hir) = trusted(
        "extern \"C\" { &'a i32 native<'a>(&'a i32 x); } &'a i32 wrap<'a>(&'a i32 x) { return native(x); } i32 f() { i32 x = 3; return *wrap(&x); }",
        "\"0\"",
        None,
    );
    let core = mir::lower(&mut hir).unwrap();
    let external = &compilation.local_analysis.as_ref().unwrap().summaries;
    let report = mir::borrow::analyze_with_summaries(&core, &mut hir, external).unwrap();
    assert!(report.functions.iter().all(|function| function.verdict == Verdict::Assumed && function.assumptions.len() == 1), "{report:#?}");
}

#[test]
fn normal_only_external_stores_do_not_claim_cancel_postconditions() {
    let (compilation, mut hir) = trusted(
        "extern \"C\" { void native<'a>(&mut &'a i32 slot, &'a i32 next); } i32 f() { i32 old = 1; i32 fresh = 2; &i32 slot = &old; native(&mut slot, &fresh); old = 3; return *slot; }",
        "",
        Some(r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#),
    );
    let core = mir::lower(&mut hir).unwrap();
    let external = &compilation.local_analysis.as_ref().unwrap().summaries;
    let report = mir::borrow::analyze_with_summaries(&core, &mut hir, external).unwrap();
    assert_eq!(report.functions[0].verdict, Verdict::Unknown);
    assert!(
        report.functions[0]
            .gaps
            .iter()
            .any(|gap| gap.kind == GapKind::CallReferenceEffects)
    );
    assert_eq!(report.functions[0].assumptions.len(), 1);
}
