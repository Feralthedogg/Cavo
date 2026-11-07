use cavo_compiler::{
    Compilation,
    diagnostic::Diagnostic,
    source::{SourceMap, Span},
    symbol::Symbol,
    syntax::token::{Keyword, TokenKind},
};

fn span(file: cavo_compiler::source::FileId, source: &str, needle: &str) -> Span {
    let start = source.find(needle).unwrap() as u32;
    Span::new(file, start, start + needle.len() as u32)
}

#[test]
fn english_diagnostic_has_rust_like_gutters_labels_note_and_help() {
    let mut sources = SourceMap::default();
    let source = "i32 main() {\n    return true;\n}\n";
    let file = sources.add("main.cavo", source.into()).unwrap();
    let diagnostic = Diagnostic::error(
        "E-TYPE-MISMATCH",
        "mismatched types",
        span(file, source, "true"),
    )
    .primary_label("expected `i32`, found `bool`")
    .note("the return type is checked before code generation")
    .help("choose a value of the required type\nor review the function's return type");
    assert_eq!(
        diagnostic.render(&sources),
        concat!(
            "error[E-TYPE-MISMATCH]: mismatched types\n",
            " --> main.cavo:2:12\n",
            "  |\n",
            "2 |     return true;\n",
            "  |            ^^^^ expected `i32`, found `bool`\n",
            "  |\n",
            "  = note: the return type is checked before code generation\n",
            "  = help: choose a value of the required type\n",
            "          or review the function's return type\n\n",
        )
    );
}

#[test]
fn related_labels_share_source_lines_without_repeating_the_file_header() {
    let mut sources = SourceMap::default();
    let source = "i32 value;\nreturn value;\n";
    let file = sources.add("main.cavo", source.into()).unwrap();
    let last = source.rfind("value").unwrap() as u32;
    let diagnostic = Diagnostic::error(
        "E-INIT-READ",
        "binding is not initialized",
        Span::new(file, last, last + 5),
    )
    .primary_label("used here")
    .label(span(file, source, "value"), "declared here");
    assert_eq!(
        diagnostic.render(&sources),
        concat!(
            "error[E-INIT-READ]: binding is not initialized\n",
            " --> main.cavo:2:8\n",
            "  |\n",
            "1 | i32 value;\n",
            "  |     ----- declared here\n",
            "2 | return value;\n",
            "  |        ^^^^^ used here\n",
            "\n",
        )
    );
}

#[test]
fn cross_file_labels_follow_the_primary_file_and_show_their_source() {
    let mut sources = SourceMap::default();
    let definitions = "struct Point {}\n";
    let first = sources.add("definitions.cavo", definitions.into()).unwrap();
    let source = "Point point;\n";
    let second = sources.add("main.cavo", source.into()).unwrap();
    let output = Diagnostic::error(
        "E-TEST",
        "cannot use this type",
        span(second, source, "Point"),
    )
    .label(span(first, definitions, "Point"), "type declared here")
    .render(&sources);
    assert!(
        output.find("--> main.cavo:1:1").unwrap()
            < output.find("::: definitions.cavo:1:8").unwrap()
    );
    assert!(output.contains("1 | struct Point {}\n  |        ----- type declared here"));
    assert_eq!(output.matches("definitions.cavo").count(), 1);
}

#[test]
fn overlapping_same_line_labels_keep_their_roles_without_repeating_source() {
    let mut sources = SourceMap::default();
    let source = "left + right";
    let file = sources.add("main.cavo", source.into()).unwrap();
    let output = Diagnostic::error(
        "E-TEST",
        "conflicting operands",
        span(file, source, "right"),
    )
    .primary_label("right operand")
    .label(span(file, source, "left"), "left operand")
    .label(Span::new(file, 0, source.len() as u32), "whole expression")
    .render(&sources);
    assert_eq!(output.matches("1 | left + right").count(), 1);
    assert!(output.contains("^^^^^ right operand"));
    assert!(output.contains("---- left operand"));
    assert!(output.contains("------------ whole expression"));
}

#[test]
fn multiline_spans_are_bounded_and_half_open_at_a_newline() {
    let mut sources = SourceMap::default();
    let source = "start\n".to_owned() + &"middle\n".repeat(20) + "finish\n";
    let file = sources.add("main.cavo", source.clone()).unwrap();
    let output = Diagnostic::error(
        "E-TEST",
        "large span",
        Span::new(file, 0, source.len() as u32),
    )
    .primary_label("ends here")
    .render(&sources);
    assert!(output.contains("1 | start"));
    assert!(output.contains("22 | finish"));
    assert!(output.lines().any(|line| line.trim() == "..."));
    assert!(!output.contains("| ..."));
    assert!(!output.contains("middle"));
    assert!(output.lines().count() < 12);
    let output =
        Diagnostic::error("E-TEST", "first line only", Span::new(file, 0, 6)).render(&sources);
    assert!(output.contains("1 | start"));
    assert!(!output.contains("middle"));
}

#[test]
fn eof_empty_input_and_crlf_keep_a_visible_insertion_marker() {
    for source in ["", "abc", "abc\r\n"] {
        let mut sources = SourceMap::default();
        let file = sources.add("main.cavo", source.into()).unwrap();
        let end = source.len() as u32;
        let output = Diagnostic::error(
            "E-TEST",
            "expected an expression",
            Span::new(file, end, end),
        )
        .render(&sources);
        assert_eq!(output.matches('^').count(), 1);
        assert!(!output.contains('\r'));
    }
}

#[test]
fn tab_expansion_utf8_and_control_escaping_keep_scalar_offsets() {
    let mut sources = SourceMap::default();
    let source = "\treturn é;\r\n";
    let file = sources.add("main.cavo", source.into()).unwrap();
    let output =
        Diagnostic::error("E-TEST", "marked scalar", span(file, source, "é")).render(&sources);
    assert!(output.contains("main.cavo:1:9"));
    assert!(output.contains("1 |     return é;"));
    assert!(output.contains(&format!("  | {}^\n", " ".repeat(11))));
    assert!(!output.contains('\t') && !output.contains('\r'));
    let source = "\u{1b}x";
    let file = sources.add("control.cavo", source.into()).unwrap();
    let output =
        Diagnostic::error("E-TEST", "marked scalar", span(file, source, "x")).render(&sources);
    assert!(output.contains("1 | \\u{1b}x"));
    assert!(output.contains(&format!("  | {}^", " ".repeat("\\u{1b}".len()))));
    assert!(!output.contains('\u{1b}'));
}

#[test]
fn parser_uses_source_tokens_and_marks_the_missing_semicolon_insertion() {
    let source = "i32 main() {\n    return 1\n}\n";
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("main.cavo", source.into()).unwrap();
    compilation.parse(file);
    let diagnostic = compilation
        .diagnostics
        .iter()
        .find(|d| d.code == "E-PARSE-001")
        .unwrap();
    let point = source.find("1\n").unwrap() as u32 + 1;
    assert_eq!(diagnostic.primary, Span::new(file, point, point));
    let output = diagnostic.render(&compilation.sources);
    assert!(output.contains("expected `;`, found `}`"));
    assert!(output.contains("= help: add `;` to finish this statement"));
    assert!(!output.contains("Semicolon") && !output.contains("RightBrace"));
    assert_eq!(TokenKind::Eof.to_string(), "end of file");
    assert_eq!(TokenKind::Ident(Symbol(99)).to_string(), "an identifier");
    assert_eq!(
        TokenKind::Keyword(Keyword::Contract).to_string(),
        "`contract`"
    );
}

fn parse_diagnostic_source(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("diagnostic.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    compilation
}

#[test]
fn mir_move_diagnostic_names_the_source_use_and_original_move() {
    let source = include_str!("fixtures/diagnostic-move.cavo");
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check_mir().is_none());
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-MOVE-USE", "{diagnostic:#?}");
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "packet.value"
    );
    assert!(
        !diagnostic.message.contains("function #"),
        "{diagnostic:#?}"
    );
    assert!(!diagnostic.message.contains("bb"), "{diagnostic:#?}");
    let moved = source.find("move packet").unwrap() as u32 + 5;
    assert!(
        diagnostic
            .labels
            .iter()
            .any(|label| label.span.start == moved && label.message.contains("moved here")),
        "{diagnostic:#?}"
    );
    assert!(!diagnostic.helps.is_empty(), "{diagnostic:#?}");
}

#[test]
fn contract_diagnostic_marks_the_call_and_uses_the_source_function_name() {
    let source = include_str!("fixtures/diagnostic-contract.cavo");
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check_mir().is_none());
    let diagnostic = compilation
        .diagnostics
        .iter()
        .find(|d| d.code == "E-CONTRACT-003")
        .unwrap();
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "read_word(p)"
    );
    assert_eq!(
        diagnostic.message,
        "cannot establish the required contract for `read_word`"
    );
    assert!(
        diagnostic
            .notes
            .iter()
            .any(|note| note.starts_with("allocation lifetime: not established"))
    );
    assert!(
        !diagnostic
            .labels
            .iter()
            .any(|label| label.message.contains("no live descendant")),
        "{diagnostic:#?}"
    );
}

#[test]
fn lifetime_diagnostic_does_not_claim_that_ended_storage_was_uninitialized() {
    let source = include_str!("fixtures/diagnostic-lifetime.cavo");
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-BORROW-LIFETIME"),
        "{:#?}",
        compilation.diagnostics
    );
    assert!(
        !compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-INIT-READ"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn an_independent_uninitialized_binding_is_still_reported_after_a_lifetime_error() {
    let source = include_str!("fixtures/diagnostic-lifetime.cavo")
        .replace("return *view;", "i32 missing;\n    return *view + missing;");
    let mut compilation = parse_diagnostic_source(&source);
    assert!(compilation.check().is_none());
    let initialization: Vec<_> = compilation
        .diagnostics
        .iter()
        .filter(|d| d.code == "E-INIT-READ")
        .collect();
    assert_eq!(initialization.len(), 1, "{:#?}", compilation.diagnostics);
    let diagnostic = initialization[0];
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "missing"
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-BORROW-LIFETIME")
    );
}

#[test]
fn conditional_partial_moves_keep_their_own_source_witness() {
    let source = "trait Marker {} struct Packet { i32 value; } struct Pair { Packet left; Packet right; } i32 inspect(Pair pair, bool take) { if (take) { auto owner = move pair.left; } return pair.left.value; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check_mir().is_none());
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-MOVE-USE", "{diagnostic:#?}");
    let moved = source.find("move pair.left").unwrap() as u32 + 5;
    assert!(
        diagnostic
            .labels
            .iter()
            .any(|label| label.span.start == moved)
    );
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "pair.left.value"
    );
}

#[test]
fn moving_a_sibling_or_reinitializing_a_field_does_not_invent_a_move_cause() {
    let prefix =
        "trait Marker {} struct Packet { i32 value; } struct Pair { Packet left; Packet right; }";
    for body in [
        "Pair pair; pair.left = Packet { value: 1 }; auto owner = move pair.left; return pair.right.value;",
        "Pair pair; pair.left = Packet { value: 1 }; auto owner = move pair.left; pair.left = Packet { value: 2 }; return pair.right.value;",
    ] {
        let source = format!("{prefix} i32 inspect() {{ {body} }}");
        let mut compilation = parse_diagnostic_source(&source);
        assert!(compilation.check_mir().is_none());
        let diagnostic = &compilation.diagnostics[0];
        assert_eq!(diagnostic.code, "E-INIT-READ", "{diagnostic:#?}");
        assert!(
            !diagnostic
                .labels
                .iter()
                .any(|label| label.message.contains("moved")),
            "{diagnostic:#?}"
        );
    }
    let source = format!(
        "{prefix} i32 inspect(Pair pair) {{ auto owner = move pair.left; pair.left = Packet {{ value: 2 }}; return pair.left.value + pair.right.value; }}"
    );
    let mut compilation = parse_diagnostic_source(&source);
    assert!(
        compilation.check_mir().is_some(),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn loop_move_and_dereferencing_a_moved_reference_are_source_errors() {
    for source in [
        "trait Marker {} struct Packet { i32 value; } void take(Packet packet) {} void inspect(Packet packet, bool repeat) { while (repeat) { take(move packet); } }",
        "trait Marker {} i32 inspect(&mut i32 view) { auto owner = move view; return *view; }",
    ] {
        let mut compilation = parse_diagnostic_source(source);
        assert!(compilation.check_mir().is_none());
        let diagnostic = &compilation.diagnostics[0];
        assert_eq!(diagnostic.code, "E-MOVE-USE", "{diagnostic:#?}");
        assert!(!diagnostic.labels.is_empty(), "{diagnostic:#?}");
        assert!(!diagnostic.helps.is_empty(), "{diagnostic:#?}");
    }
}

fn assert_move_certainty(source: &str, expected: &str, label: &str) {
    for prefix in ["", "trait ForceMir {}"] {
        let mut compilation = parse_diagnostic_source(&format!("{prefix} {source}"));
        assert!(compilation.check_mir().is_none());
        let diagnostic = compilation
            .diagnostics
            .iter()
            .find(|d| d.code == "E-MOVE-USE")
            .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
        assert_eq!(diagnostic.message, expected, "{diagnostic:#?}");
        assert_eq!(diagnostic.primary_label.as_deref(), Some(label));
        assert!(
            diagnostic
                .labels
                .iter()
                .any(|label| label.message == "ownership moved here")
        );
        assert!(!diagnostic.helps.is_empty());
    }
}

#[test]
fn move_certainty_distinguishes_unconditional_and_conditional_transfers() {
    let prefix = "struct Packet { i32 value; } void consume(Packet packet) {}";
    assert_move_certainty(
        &format!(
            "{prefix} i32 inspect(Packet packet) {{ consume(move packet); return packet.value; }}"
        ),
        "value was moved before this use",
        "this place has already been moved",
    );
    assert_move_certainty(
        &format!(
            "{prefix} i32 inspect(Packet packet, bool take) {{ if (take) {{ consume(move packet); }} return packet.value; }}"
        ),
        "value may have been moved before this use",
        "this place is not available on every incoming path",
    );
}

#[test]
fn move_certainty_is_definite_when_each_branch_moves_the_value() {
    assert_move_certainty(
        "struct Packet { i32 value; } void consume(Packet packet) {} i32 inspect(Packet packet, bool take) { if (take) { consume(move packet); } else { consume(move packet); } return packet.value; }",
        "value was moved before this use",
        "this place has already been moved",
    );
}

#[test]
fn move_certainty_waits_for_longer_incoming_paths() {
    for body in [
        "if (take) { consume(move packet); } else { if (other) { i32 extra = 1; } }",
        "if (take) { if (other) { i32 extra = 1; } } else { consume(move packet); }",
    ] {
        assert_move_certainty(
            &format!(
                "struct Packet {{ i32 value; }} void consume(Packet packet) {{}} i32 inspect(Packet packet, bool take, bool other) {{ {body} return packet.value; }}"
            ),
            "value may have been moved before this use",
            "this place is not available on every incoming path",
        );
    }
}

#[test]
fn move_certainty_does_not_promote_a_mixed_moved_and_uninitialized_join() {
    assert_move_certainty(
        "struct Packet { i32 value; } void consume(Packet packet) {} i32 inspect(bool take) { Packet packet; if (take) { packet = Packet { value: 1 }; consume(move packet); } return packet.value; }",
        "value may have been moved before this use",
        "this place is not available on every incoming path",
    );
}

#[test]
fn move_certainty_keeps_a_definite_partial_move_of_a_whole_aggregate() {
    assert_move_certainty(
        "struct Packet { i32 value; } struct Pair { Packet left; Packet right; } void consume(Pair pair) {} void inspect(Pair pair) { auto owner = move pair.left; consume(move pair); }",
        "value was moved before this use",
        "this place has already been moved",
    );
}

#[test]
fn return_escape_reports_the_return_without_its_cleanup_cascade() {
    use cavo_compiler::local::{Assessment, Predicate, Verdict};
    for source in [
        "&i32 escape() { i32 value = 1; return &value; }",
        "&i32 escape() { i32 value = 1; auto parent = &mut value; return &*parent; }",
    ] {
        let mut compilation = parse_diagnostic_source(source);
        assert!(compilation.check().is_none());
        let codes: Vec<_> = compilation.diagnostics.iter().map(|d| d.code).collect();
        assert_eq!(codes, ["E-BORROW-RETURN"]);
        let report = compilation.local_analysis.as_ref().unwrap();
        assert_eq!(report.verdict, Verdict::Rejected);
        let failed: Vec<_> = report
            .functions
            .iter()
            .flat_map(|f| &f.findings)
            .filter(|f| f.assessment == Assessment::NotEstablished)
            .collect();
        assert!(
            failed
                .iter()
                .any(|f| f.predicate == Predicate::ReturnDoesNotBorrowLocalStorage)
        );
        assert!(
            failed
                .iter()
                .any(|f| matches!(f.predicate, Predicate::StorageMayEnd(_)))
        );
    }
}

#[test]
fn return_escape_keeps_an_independent_ended_owner() {
    let source = "&i32 escape() { &i32 view; { i32 short = 1; view = &short; } i32 used = *view; i32 value = 2; return &value; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    let codes: Vec<_> = compilation.diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(
        codes
            .iter()
            .filter(|&&code| code == "E-BORROW-RETURN")
            .count(),
        1
    );
    assert_eq!(
        codes
            .iter()
            .filter(|&&code| code == "E-BORROW-LIFETIME")
            .count(),
        1
    );
    assert!(
        !codes.contains(&"E-INIT-READ"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn return_escape_keeps_an_independent_initialization_error() {
    let source = "&i32 escape(bool choose) { i32 missing; if (choose) { missing = 1; } i32 read = missing; i32 value = 2; return &value; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    let codes: Vec<_> = compilation.diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(
        codes
            .iter()
            .filter(|&&code| code == "E-BORROW-RETURN")
            .count(),
        1
    );
    assert_eq!(
        codes.iter().filter(|&&code| code == "E-INIT-READ").count(),
        1
    );
    assert!(!codes.contains(&"E-BORROW-LIFETIME"));
}

#[test]
fn render_unknown_name_explains_the_primary_without_a_trailing_gutter() {
    let mut compilation = parse_diagnostic_source("void inspect() { missing(); }");
    assert!(compilation.check().is_none());
    let diagnostic = compilation
        .diagnostics
        .iter()
        .find(|d| d.code == "E-NAME-UNKNOWN")
        .unwrap();
    assert_eq!(
        diagnostic.primary_label.as_deref(),
        Some("'missing' is not defined in this scope")
    );
    assert!(diagnostic.notes.is_empty() && diagnostic.helps.is_empty());
    let rendered = diagnostic.render(&compilation.sources);
    assert!(rendered.contains("^^^^^^^ 'missing' is not defined in this scope"));
    assert_eq!(
        rendered.lines().filter(|line| line.trim() == "|").count(),
        1
    );
    assert!(
        rendered
            .lines()
            .rfind(|line| !line.is_empty())
            .unwrap()
            .contains('^')
    );
}

#[test]
fn render_help_alone_keeps_its_message_separator() {
    let mut sources = SourceMap::default();
    let file = sources.add("main.cavo", "value".into()).unwrap();
    let rendered = Diagnostic::error("E-TEST", "rejected", Span::new(file, 0, 5))
        .help("initialize this value")
        .render(&sources);
    assert!(rendered.contains("^^^^^\n  |\n  = help: initialize this value\n"));
}

#[test]
fn render_contract_coverage_uses_readable_lowercase_labels() {
    use cavo_compiler::contracts::{Assessment, Component, Obligation, Report};
    let mut sources = SourceMap::default();
    let file = sources.add("main.cavo", "read_word(p)".into()).unwrap();
    let unknown = || Assessment::Unknown("no matching evidence".into());
    let unavailable = || Assessment::NotAnalyzed("analysis unavailable".into());
    for (states, expected) in [
        (vec![unknown()], "complete"),
        (vec![unknown(), unavailable()], "partial"),
        (vec![unavailable()], "unavailable"),
    ] {
        let mut report = Report::default();
        report.obligations.push(Obligation {
            key: cavo_compiler::external::digest::sha256(b"coverage presentation"),
            span: Span::new(file, 0, 12),
            operation: "read_word".into(),
            components: states
                .into_iter()
                .map(|assessment| Component {
                    name: "allocation lifetime".into(),
                    assessment,
                })
                .collect(),
        });
        let mut diagnostics = Vec::new();
        report.diagnostics(&mut diagnostics);
        assert_eq!(diagnostics.len(), 1);
        let rendered = diagnostics[0].render(&sources);
        assert!(
            rendered.contains(&format!("= note: analysis coverage: {expected}\n")),
            "{rendered}"
        );
    }
}

#[test]
fn contract_operation_preserves_the_written_qualified_callee() {
    let mut compilation = Compilation::default();
    for (path, source) in [
        (
            "ptr.cavo",
            "module ptr; @intrinsic(ptr_read) pub i32 read(ptr<const i32> address);",
        ),
        (
            "app.cavo",
            "module app; import ptr; i32 inspect(ptr<const i32> p) { contract { return ptr::read(p); } }",
        ),
    ] {
        let file = compilation.sources.add(path, source.into()).unwrap();
        compilation.parse(file);
    }
    assert!(compilation.check_mir().is_none());
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-CONTRACT-003", "{diagnostic:#?}");
    assert_eq!(
        diagnostic.message,
        "cannot establish the required contract for `ptr::read`"
    );
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "ptr::read(p)"
    );
}

#[test]
fn violated_contract_keeps_the_actual_invalidation_cause() {
    let source = r#"
@intrinsic(ptr_read) i32 load(ptr<i32> address);
@intrinsic(allocate) ptr<i32> allocate(usize count);
@intrinsic(deallocate) void release(ptr<i32> address);
i32 inspect() {
    contract {
        auto p = allocate(1);
        release(p);
        return load(p);
    }
}

"#;
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check_mir().is_none());
    let diagnostic = compilation
        .diagnostics
        .iter()
        .find(|d| d.code == "E-CONTRACT-004")
        .unwrap();
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "load(p)"
    );
    assert!(
        diagnostic.labels.iter().any(|label| compilation
            .sources
            .file(label.span.file)
            .slice(label.span)
            == "release(p)"),
        "{diagnostic:#?}"
    );
}

#[test]
fn locals_ending_at_the_same_brace_keep_separate_lifetime_causes() {
    let source = "i32 inspect() { &i32 first; &i32 second; { i32 left = 1; i32 right = 2; first = &left; second = &right; } return *first + *second; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        2,
        "{:#?}",
        compilation.diagnostics
    );
    for (borrow, used, unrelated) in [
        ("&left", "*first", "*second"),
        ("&right", "*second", "*first"),
    ] {
        let diagnostic = compilation
            .diagnostics
            .iter()
            .find(|d| {
                d.labels.iter().any(|label| {
                    compilation.sources.file(label.span.file).slice(label.span) == borrow
                })
            })
            .unwrap();
        assert_eq!(diagnostic.code, "E-BORROW-LIFETIME");
        let labels: Vec<_> = diagnostic
            .labels
            .iter()
            .map(|label| compilation.sources.file(label.span.file).slice(label.span))
            .collect();
        assert!(labels.contains(&used), "{diagnostic:#?}");
        assert!(!labels.contains(&unrelated), "{diagnostic:#?}");
    }
}

#[test]
fn contract_titles_do_not_copy_comments_or_control_characters_from_the_callee() {
    let source = include_str!("fixtures/diagnostic-contract.cavo")
        .replace("read_word(p)", "(/* \u{1b}[31m\n */ read_word)(p)");
    let mut compilation = parse_diagnostic_source(&source);
    assert!(compilation.check_mir().is_none());
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-CONTRACT-003", "{diagnostic:#?}");
    assert_eq!(
        diagnostic.message,
        "cannot establish the required contract for `read_word`"
    );
    assert!(!diagnostic.render(&compilation.sources).contains('\u{1b}'));
}
