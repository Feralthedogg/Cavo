use cavo_compiler::{
    Compilation,
    external::{Digest, SummaryStatus, digest::sha256, interface},
    hir,
    local::{Assessment, Evidence},
};

fn parsed(source: &str) -> Compilation {
    let mut c = Compilation::default();
    let file = c.sources.add("external.cavo", source.into()).unwrap();
    c.parse(file);
    c
}
fn document(c: &mut Compilation, returns: &str, effects: &str) -> String {
    let p = c
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", c.diagnostics));
    let f = interface::interfaces(&p, &c.symbols, &c.sources)
        .unwrap()
        .remove(0);
    format!(
        r#"{{"schema":1,"id":"sample","version":"1.0.0","artifact":"sha256:{}","functions":[{{"name":"{}","abi":"{}","signature":"{}","effects":{{{effects}}},"returns":[{returns}]}}]}}"#,
        "a".repeat(64),
        f.name,
        f.abi,
        f.signature
    )
}
const PURE: &str = r#""no_retain":true,"no_free":true,"no_callback":true,"no_unwind":true,"no_suspend":true,"no_block":true,"no_allocate":true,"preserves_validity":true,"reads":[0],"writes":[]"#;
fn loaded(source: &str, returns: &str, effects: &str, trust: bool) -> Compilation {
    let mut c = parsed(source);
    let doc = document(&mut c, returns, effects);
    let id = c.add_external_summary("sample.cavosum", doc).unwrap();
    if trust {
        c.trust_summary(id);
    }
    c
}
fn checked(mut c: Compilation) -> (Compilation, hir::Program) {
    let p = c.check();
    assert!(c.diagnostics.is_empty(), "{:#?}", c.diagnostics);
    let p = p.unwrap();
    c.local_analysis.as_ref().unwrap().validate(&p).unwrap();
    (c, p)
}

fn memory_loaded(source: &str, returns: &str, stores: &str, trust: bool) -> Compilation {
    let mut c = parsed(source);
    let effects = PURE.replace("\"writes\":[]", "\"writes\":[0]");
    let doc = document(&mut c, returns, &format!("{effects},\"stores\":{stores}")).replacen(
        "\"schema\":1",
        "\"schema\":2",
        1,
    );
    let id = c.add_external_summary("memory.cavosum", doc).unwrap();
    if trust {
        c.trust_summary(id);
    }
    c
}

#[test]
fn trusted_schema_two_stores_update_caller_origins_and_preserve_assumptions() {
    let source = "extern \"C\" { void replace<'a>(&mut &'a i32 slot,&'a i32 value); } i32 f() { i32 old=1; i32 fresh=2; auto slot=&old; replace(&mut slot,&fresh); old=3; return *slot; }";
    let (c, _) = checked(memory_loaded(
        source,
        "",
        r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#,
        true,
    ));
    let r = c.local_analysis.unwrap();
    assert_eq!(r.summaries[0].schema, 2);
    assert_eq!(r.summaries[0].status, SummaryStatus::Assumed);
    assert_eq!(r.functions[0].assumptions.len(), 1);
    let mut c = memory_loaded(
        &source.replace("old=3;", "fresh=3;"),
        "",
        r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| {
        d.code == "E-BORROW-CONFLICT"
            && d.notes
                .iter()
                .any(|n| n.contains("assumed external contract"))
    }));
}

#[test]
fn schema_two_returns_and_stores_share_an_entry_snapshot() {
    let source = "extern \"C\" { &'a i32 swap<'a>(&mut &'a i32 slot,&'a i32 value); } i32 f() { i32 old=1; i32 fresh=2; auto slot=&old; auto previous=swap(&mut slot,&fresh); return *slot+*previous; }";
    checked(memory_loaded(
        source,
        r#""0.*""#,
        r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#,
        true,
    ));
    let mut c = memory_loaded(
        &source.replace("return *slot+*previous;", "old=3; return *previous;"),
        r#""0.*""#,
        r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-BORROW-CONFLICT"));
}

#[test]
fn unknown_invalid_or_untrusted_store_effects_are_not_approved() {
    let source = "extern \"C\" { void replace<'a>(&mut &'a i32 slot,&'a i32 value); }";
    for stores in [
        "null",
        r#"[{"target":"0.*","sources":["20"],"when":"always"}]"#,
        r#"[{"target":"0.*","sources":["0"],"when":"always"}]"#,
        r#"[{"target":"0","sources":["1"],"when":"always"}]"#,
    ] {
        let mut c = memory_loaded(source, "", stores, true);
        assert!(c.check().is_none());
        assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-EFFECT"));
    }
    let mut c = memory_loaded(
        &format!(
            "{source} void f<'a>(&mut &'a i32 slot,&'a i32 value) {{ replace(move slot,value); }}"
        ),
        "",
        r#"[{"target":"0.*","sources":["1"],"when":"always"}]"#,
        false,
    );
    assert!(c.check().is_none());
    assert!(
        c.diagnostics
            .iter()
            .any(|d| d.code == "E-SUMMARY-UNTRUSTED")
    );
}

#[test]
fn maybe_external_stores_keep_the_original_origin() {
    let source = "extern \"C\" { void replace<'a>(&mut &'a i32 slot,&'a i32 value); } i32 f() { i32 old=1; i32 fresh=2; auto slot=&old; replace(&mut slot,&fresh); old=3; return *slot; }";
    let mut c = memory_loaded(
        source,
        "",
        r#"[{"target":"0.*","sources":["1"],"when":"maybe"}]"#,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-BORROW-CONFLICT"));
}

#[test]
fn legacy_schema_does_not_silently_accept_new_store_semantics() {
    let mut c = parsed("extern \"C\" { void replace<'a>(&mut &'a i32 slot,&'a i32 value); }");
    let doc = document(&mut c, "", &format!("{PURE},\"stores\":[]"));
    assert!(c.add_external_summary("legacy.cavosum", doc).is_none());
    assert!(c.diagnostics[0].message.contains("unknown member `stores`"));
}

#[test]
fn external_store_contracts_cannot_copy_a_nested_mutable_reference() {
    let source =
        "extern \"C\" { void replace<'a>(&mut &'a mut i32 target,&mut &'a mut i32 source); }";
    let mut c = memory_loaded(
        source,
        "",
        r#"[{"target":"0.*","sources":["1.*"],"when":"always"}]"#,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-EFFECT"));
}

#[test]
fn sha256_matches_standard_vectors_and_exact_byte_identity() {
    for (text, expected) in [
        (
            "",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            "abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
    ] {
        let digest = sha256(text.as_bytes());
        assert_eq!(digest.to_string(), format!("sha256:{expected}"));
        assert_eq!(Digest::parse(&digest.to_string()), Some(digest));
    }
    assert_ne!(sha256(b"abc"), sha256(b"abc\n"));
    assert!(Digest::parse(&format!("sha256:{}", "A".repeat(64))).is_none());
}

#[test]
fn loading_a_summary_does_not_grant_trust() {
    let mut c = loaded(
        "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); } i32 f() { i32 x=1; return *identity(&x); }",
        r#""0""#,
        PURE,
        false,
    );
    assert!(c.check().is_none());
    assert!(
        c.diagnostics
            .iter()
            .any(|d| d.code == "E-SUMMARY-UNTRUSTED")
    );
    assert_eq!(
        c.local_analysis.as_ref().unwrap().summaries[0].status,
        SummaryStatus::Untrusted
    );
}

#[test]
fn trusted_reference_summaries_preserve_origins_and_transitive_assumptions() {
    let (c, _) = checked(loaded(
        "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); } &'a i32 wrapper<'a>(&'a i32 x) { return identity(x); } i32 f() { i32 x=1; return *wrapper(&x); }",
        r#""0""#,
        PURE,
        true,
    ));
    let r = c.local_analysis.unwrap();
    assert_eq!(r.summaries[0].status, SummaryStatus::Assumed);
    for f in r.functions {
        assert_eq!(f.assumptions.len(), 1);
        assert!(
            f.findings
                .iter()
                .all(|d| d.assessment != Assessment::Established)
        );
        assert!(
            f.findings
                .iter()
                .any(|d| d.assessment == Assessment::Assumed)
        );
    }
    assert!(r.regions.iter().all(|r| !r.assumptions.is_empty()));
}

#[test]
fn violations_keep_external_assumptions_in_evidence_and_diagnostics() {
    let mut c = loaded(
        "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); } i32 f() { &i32 view; { i32 x=1; view=identity(&x); } return *view; }",
        r#""0""#,
        PURE,
        true,
    );
    assert!(c.check().is_none());
    let d = c
        .diagnostics
        .iter()
        .find(|d| d.code == "E-BORROW-LIFETIME")
        .unwrap();
    assert!(
        d.notes
            .iter()
            .any(|n| n.contains("assumed external contract"))
    );
    let r = c.local_analysis.as_ref().unwrap();
    assert!(
        r.functions[0]
            .findings
            .iter()
            .any(|f| f.assessment == Assessment::NotEstablished && !f.assumptions.is_empty())
    );
}

#[test]
fn nested_external_return_paths_resolve_the_inner_reference() {
    checked(loaded(
        "extern \"C\" { &'b i32 inner<'a,'b>(&'a &'b i32 x); } i32 f() { i32 x=1; auto r=&x; auto result=inner(&r); return *result; }",
        r#""0.*""#,
        PURE,
        true,
    ));
    let mut c = loaded(
        "extern \"C\" { &'static i32 inner<'a,'b>(&'a &'b i32 x); }",
        r#""0.*""#,
        PURE,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-EFFECT"));
}

#[test]
fn unknown_or_unmodeled_effects_cannot_be_assumed_safe() {
    for effects in [
        PURE.replace("\"no_free\":true", "\"no_free\":null"),
        PURE.replace("\"no_callback\":true", "\"no_callback\":false"),
        PURE.replace("\"reads\":[0]", "\"reads\":null"),
    ] {
        let mut c = loaded(
            "extern \"C\" { i32 read(&i32 x); } i32 f() { i32 x=1; return read(&x); }",
            "",
            &effects,
            true,
        );
        assert!(c.check().is_none());
        assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-EFFECT"));
        assert_eq!(
            c.local_analysis.as_ref().unwrap().summaries[0].status,
            SummaryStatus::Unsupported
        );
    }
    let mut c = loaded("extern \"C\" { i32 read(ptr<i32> x); }", "", PURE, true);
    assert!(c.check().is_none());
}

#[test]
fn scalar_mutations_require_exclusive_input_and_preserved_validity() {
    let effects = PURE.replace("\"writes\":[]", "\"writes\":[0]");
    checked(loaded(
        "extern \"C\" { void update(&mut i32 x); } i32 f() { i32 x=1; update(&mut x); return x; }",
        "",
        &effects,
        true,
    ));
    let mut c = loaded("extern \"C\" { void update(&i32 x); }", "", &effects, true);
    assert!(c.check().is_none());
    let mut c = loaded(
        "extern \"C\" { void update(&mut &i32 x); }",
        "",
        &effects,
        true,
    );
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-EFFECT"));
}

#[test]
fn stale_or_changed_documents_do_not_inherit_trust() {
    let source = "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); } i32 f() { i32 x=1; return *identity(&x); }";
    let mut c = parsed(source);
    let doc = document(&mut c, r#""0""#, PURE);
    let old = sha256(doc.as_bytes());
    let changed = format!("{doc}\n");
    c.add_external_summary("changed.cavosum", changed).unwrap();
    c.trust_summary(old);
    assert!(c.check().is_none());
    assert!(
        c.diagnostics
            .iter()
            .any(|d| d.code == "E-SUMMARY-UNTRUSTED")
    );
}

#[test]
fn abi_signature_duplicates_and_body_overrides_are_rejected() {
    let mut declaration = parsed("i32 read(&i32 x);");
    let doc = document(&mut declaration, "", PURE);
    let mut body = parsed("i32 read(&i32 x) { return *x; }");
    let id = body.add_external_summary("override.cavosum", doc).unwrap();
    body.trust_summary(id);
    assert!(body.check().is_none());
    assert!(body.diagnostics.iter().any(|d| d.code == "E-SUMMARY-BIND"));
    for change in ["abi", "signature", "duplicate"] {
        let mut c = parsed("extern \"C\" { i32 read(&i32 x); }");
        let doc = document(&mut c, "", PURE);
        let changed = match change {
            "abi" => doc.replace("\"abi\":\"C\"", "\"abi\":\"cavo\""),
            "signature" => doc.replacen("\"signature\":\"sha256:", "\"signature\":\"sha256:0", 1),
            _ => doc.clone(),
        };
        let digest = c.add_external_summary("bad.cavosum", changed);
        if change == "duplicate" {
            c.add_external_summary("duplicate.cavosum", doc);
        }
        if let Some(id) = digest {
            c.trust_summary(id);
        }
        assert!(c.check().is_none());
        assert!(
            c.diagnostics
                .iter()
                .any(|d| matches!(d.code, "E-SUMMARY-BIND" | "E-SUMMARY-SCHEMA"))
        );
    }
}

#[test]
fn summaries_cannot_skip_declared_contracts_or_self_authorize() {
    let mut c = loaded(
        "extern \"C\" { i32 read(&i32 x) requires false; }",
        "",
        PURE,
        true,
    );
    assert!(c.check().is_none());
    let d = c
        .diagnostics
        .iter()
        .find(|d| d.code == "E-SUMMARY-EFFECT")
        .unwrap();
    assert!(d.notes.iter().any(|n| n.contains("requires/ensures")));
    let mut c = parsed("extern \"C\" { i32 read(&i32 x); }");
    let doc = document(&mut c, "", PURE);
    let invalid = doc.replacen("{", "{\"trusted\":true,", 1);
    assert!(
        c.add_external_summary("self-trust.cavosum", invalid)
            .is_none()
    );
    assert!(
        c.diagnostics[0]
            .message
            .contains("unknown member `trusted`")
    );
}

#[test]
fn callback_values_keep_their_targets_external_dependencies_at_the_caller() {
    let (c, _) = checked(loaded(
        "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); } &'a i32 wrapper<'a>(&'a i32 x) { return identity(x); } i32 run(for<'a> fn(&'a i32) -> &'a i32 cb) { i32 x=1; return *cb(&x); } i32 entry() { return run(wrapper); }",
        r#""0""#,
        PURE,
        true,
    ));
    assert_eq!(
        c.local_analysis
            .unwrap()
            .functions
            .last()
            .unwrap()
            .assumptions
            .len(),
        1
    );
}

#[test]
fn assumption_closure_limits_never_leave_established_local_findings() {
    let declarations = (0..129)
        .map(|i| format!("void external{i}();"))
        .collect::<String>();
    let calls = (0..129)
        .map(|i| format!("external{i}();"))
        .collect::<String>();
    let mut c = parsed(&format!(
        "extern \"C\" {{ {declarations} }} void f() {{ {calls} }}"
    ));
    let p = c.check_types().unwrap();
    let interfaces = interface::interfaces(&p, &c.symbols, &c.sources).unwrap();
    let effects = PURE.replace("\"reads\":[0]", "\"reads\":[]");
    for (batch, entries) in interfaces.chunks(65).enumerate() {
        let entries=entries.iter().map(|f|format!(r#"{{"name":"{}","abi":"{}","signature":"{}","effects":{{{effects}}},"returns":[]}}"#,f.name,f.abi,f.signature)).collect::<Vec<_>>().join(",");
        let doc = format!(
            r#"{{"schema":1,"id":"batch{batch}","version":"1","artifact":"sha256:{}","functions":[{entries}]}}"#,
            "0".repeat(64)
        );
        let id = c
            .add_external_summary(format!("batch{batch}.cavosum"), doc)
            .unwrap();
        c.trust_summary(id);
    }
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-SUMMARY-LIMIT"));
    let r = c.local_analysis.as_ref().unwrap();
    assert!(r.functions.is_empty());
    assert!(r.regions.iter().all(|c| !c.body_checked));
    r.validate(&p).unwrap();
}

#[test]
fn schema_rejects_duplicates_self_trust_invalid_unicode_and_resource_exhaustion() {
    for text in [
        r#"{"schema":1,"schema":1}"#.into(),
        r#"{"trusted":true}"#.into(),
        r#"{"x":"\uD800"}"#.into(),
        r#"{"x":"\uDC00"}"#.into(),
        r#"{"x":01}"#.into(),
        r#"{"x":18446744073709551616}"#.into(),
        format!("{}0{}", "[".repeat(40), "]".repeat(40)),
        " ".repeat(262_145),
    ] {
        let mut c = Compilation::default();
        assert!(c.add_external_summary("invalid.cavosum", text).is_none());
        assert_eq!(c.diagnostics[0].code, "E-SUMMARY-SCHEMA");
    }
}

#[test]
fn fingerprints_are_independent_of_arena_ids_and_lifetime_spelling() {
    fn id(source: &str) -> Digest {
        let mut c = parsed(source);
        let p = c
            .check_types()
            .unwrap_or_else(|| panic!("{source}\n{:#?}", c.diagnostics));
        interface::interfaces(&p, &c.symbols, &c.sources)
            .unwrap()
            .remove(0)
            .signature
    }
    let source = "extern \"C\" { &'a i32 identity<'a>(&'a i32 x); }";
    assert_eq!(
        id(source),
        id(&format!("struct Unrelated {{ bool value; }} {source}"))
    );
    assert_eq!(id(source), id(&source.replace("'a", "'renamed")));
    assert_ne!(id(source), id(&source.replace("i32", "i64")));
    assert_ne!(
        id(source),
        id(source
            .strip_prefix("extern \"C\" { ")
            .unwrap()
            .strip_suffix(" }")
            .unwrap())
    );
    assert_ne!(
        id("struct R { i32 x; } extern \"C\" { void read(&R r); }"),
        id("struct R { i64 x; } extern \"C\" { void read(&R r); }")
    );
}

#[test]
fn report_support_ids_cannot_reference_an_untrusted_or_missing_summary() {
    let (mut c, p) = checked(loaded(
        "extern \"C\" { i32 read(&i32 x); } i32 f() { i32 x=1; return read(&x); }",
        "",
        PURE,
        true,
    ));
    let r = c.local_analysis.as_mut().unwrap();
    let check = r.functions[0]
        .evidence
        .iter_mut()
        .find(|e| matches!(e, Evidence::LocalCheck { .. }))
        .unwrap();
    if let Evidence::LocalCheck { assumptions, .. } = check {
        assumptions[0].0 = 999;
    }
    assert!(r.validate(&p).is_err());
}
