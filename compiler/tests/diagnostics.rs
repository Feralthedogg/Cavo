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
    assert_eq!(
        diagnostic.primary_label.as_deref(),
        Some("the evidence required for this operation is not established")
    );
    let rendered = diagnostic.render(&compilation.sources);
    assert!(
        rendered
            .contains("^^^^^^^^^^^^ the evidence required for this operation is not established")
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
        assert_eq!(
            compilation.diagnostics[0].primary_label.as_deref(),
            Some("this reference would outlive `value`")
        );
        let rendered = compilation.diagnostics[0].render(&compilation.sources);
        assert!(
            rendered
                .lines()
                .any(|line| line.contains("^ this reference would outlive `value`"))
        );
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

fn assert_initialized_reads(compilation: &Compilation, name: &str) {
    use cavo_compiler::local::{Assessment, Predicate, Verdict};
    let report = compilation.local_analysis.as_ref().unwrap();
    assert_eq!(report.verdict, Verdict::Rejected);
    let reads: Vec<_> = report
        .functions
        .iter()
        .flat_map(|f| &f.findings)
        .filter(|f| {
            matches!(f.predicate, Predicate::StorageAvailable(_))
                && compilation.sources.file(f.span.file).slice(f.span) == name
        })
        .collect();
    assert!(!reads.is_empty(), "no availability checks for {name}");
    assert!(
        reads
            .iter()
            .all(|f| f.assessment == Assessment::Established),
        "{reads:#?}"
    );
}

#[test]
fn local_model_keeps_initialization_when_poison_joins_a_loop_backedge() {
    let source = "i32 next_iter(i32 n) { i32 y; i32 total = 0; i32 i = 0; while (i < n) { if (i > 0) { total += y; } y = i; i += 1; } return total; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_initialized_reads(&compilation, "total");
    assert_eq!(
        compilation.diagnostics.len(),
        1,
        "{:#?}",
        compilation.diagnostics
    );
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-INIT-READ");
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "y"
    );
}

#[test]
fn local_model_joins_poisoned_and_clean_values_without_losing_initialization() {
    let source = "i32 inspect(bool choose) { i32 y; i32 total = 0; if (choose) { total = y; } return total; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_initialized_reads(&compilation, "total");
    assert!(
        compilation
            .local_analysis
            .as_ref()
            .unwrap()
            .functions
            .iter()
            .flat_map(|f| &f.findings)
            .any(
                |f| matches!(f.predicate, cavo_compiler::local::Predicate::Available(_))
                    && compilation.sources.file(f.span.file).slice(f.span) == "total"
                    && f.assessment == cavo_compiler::local::Assessment::NotEstablished
            ),
        "initialized storage must not approve a poisoned value"
    );
    let return_check = compilation
        .local_analysis
        .as_ref()
        .unwrap()
        .functions
        .iter()
        .flat_map(|f| &f.findings)
        .find(|f| f.predicate == cavo_compiler::local::Predicate::ReturnDoesNotBorrowLocalStorage)
        .unwrap();
    assert_eq!(
        return_check.assessment,
        cavo_compiler::local::Assessment::NotEstablished,
        "poisoned data must remain invalid despite initialized storage"
    );
    assert_eq!(compilation.diagnostics.len(), 1);
}

#[test]
fn local_model_a_real_overwrite_restores_value_health() {
    let source = "i32 inspect(bool choose) { i32 y; i32 total = 0; if (choose) { total = y; } total = 5; return total; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_initialized_reads(&compilation, "total");
    let return_check = compilation
        .local_analysis
        .as_ref()
        .unwrap()
        .functions
        .iter()
        .flat_map(|f| &f.findings)
        .find(|f| f.predicate == cavo_compiler::local::Predicate::ReturnDoesNotBorrowLocalStorage)
        .unwrap();
    assert_eq!(
        return_check.assessment,
        cavo_compiler::local::Assessment::Established
    );
    assert_eq!(compilation.diagnostics.len(), 1);
}

#[test]
fn local_model_poison_does_not_hide_a_truly_uninitialized_path() {
    let source =
        "i32 inspect(bool choose) { i32 y; i32 total; if (choose) { total = y; } return total; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    let missing: Vec<_> = compilation
        .diagnostics
        .iter()
        .filter(|d| d.code == "E-INIT-READ")
        .map(|d| compilation.sources.file(d.primary.file).slice(d.primary))
        .collect();
    assert!(
        missing.contains(&"y") && missing.contains(&"total"),
        "{missing:?}"
    );
}

#[test]
fn local_model_poison_does_not_hide_a_moved_path() {
    let source = "struct Lease { i32 id; } i32 inspect(bool choose) { Lease value = Lease { id: 1 }; Lease missing; if (choose) { auto owner = move value; } else { value = move missing; } return value.id; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-INIT-READ")
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-MOVE-USE")
    );
}

#[test]
fn local_model_a_failed_borrow_does_not_register_a_new_loan() {
    let source =
        "void inspect(&mut i32 v) { &mut i32 a = &mut *v; &mut i32 b = &mut *v; *a = 1; *b = 2; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        1,
        "{:#?}",
        compilation.diagnostics
    );
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-BORROW-CONFLICT");
    assert_eq!(
        compilation
            .sources
            .file(diagnostic.primary.file)
            .slice(diagnostic.primary),
        "&mut *v"
    );
    assert_eq!(
        diagnostic.primary.start,
        source.rfind("&mut *v").unwrap() as u32
    );
}

#[test]
fn local_model_a_clean_loan_alternative_survives_a_poisoned_branch() {
    let source = "struct Pair { i32 left; i32 right; } void inspect(bool choose, &mut Pair p) { auto a = &mut p.left; &mut i32 r; if (choose) { r = &mut p.left; } else { r = &mut p.right; } *a = 1; p.right = 2; *r = 3; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    let conflicts: Vec<_> = compilation
        .diagnostics
        .iter()
        .filter(|d| d.code == "E-BORROW-CONFLICT")
        .collect();
    assert_eq!(conflicts.len(), 2, "{:#?}", compilation.diagnostics);
    assert!(
        conflicts
            .iter()
            .any(|d| d.primary.start == source.find("p.right = 2").unwrap() as u32),
        "the valid right-field loan must remain live on its branch"
    );
    assert!(
        !conflicts
            .iter()
            .any(|d| compilation.sources.file(d.primary.file).slice(d.primary) == "*a")
    );
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
fn return_owner_names_the_storage_behind_aliases_and_reborrows() {
    for source in [
        "&i32 escape() { i32 x = 1; auto a = &x; auto b = a; return b; }",
        "&i32 escape() { i32 x = 1; auto a = &mut x; return &*a; }",
        "&'a i32 id<'a>(&'a i32 value) { return value; } &i32 escape() { i32 x = 1; return id(&x); }",
        "&i32 escape() { i32 x = 1; auto a = &x; { i32 x = 2; } return a; }",
    ] {
        let mut compilation = parse_diagnostic_source(source);
        assert!(compilation.check().is_none());
        assert_eq!(
            compilation.diagnostics.len(),
            1,
            "{:#?}",
            compilation.diagnostics
        );
        let diagnostic = &compilation.diagnostics[0];
        assert_eq!(diagnostic.code, "E-BORROW-RETURN");
        assert_eq!(
            diagnostic.primary_label.as_deref(),
            Some("this reference would outlive `x`")
        );
        let storage = diagnostic
            .labels
            .iter()
            .find(|label| label.message == "local storage is declared here")
            .unwrap();
        assert_eq!(storage.span.start, source.find("x = 1").unwrap() as u32);
    }
}

#[test]
fn return_owner_keeps_both_distinct_branch_causes_with_the_same_code() {
    let source = "&i32 escape(bool c) { i32 x = 1; i32 y = 2; auto r = &x; if (c) { r = &y; } auto s = r; return s; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    let labels: Vec<_> = compilation
        .diagnostics
        .iter()
        .map(|d| {
            assert_eq!(d.code, "E-BORROW-RETURN", "{d:#?}");
            d.primary_label.as_deref().unwrap()
        })
        .collect();
    assert_eq!(
        labels,
        [
            "this reference would outlive `x`",
            "this reference would outlive `y`"
        ]
    );
    let failed_ends = compilation
        .local_analysis
        .as_ref()
        .unwrap()
        .functions
        .iter()
        .flat_map(|f| &f.findings)
        .filter(|f| {
            matches!(
                f.predicate,
                cavo_compiler::local::Predicate::StorageMayEnd(_)
            ) && f.assessment == cavo_compiler::local::Assessment::NotEstablished
        })
        .count();
    assert!(
        failed_ends >= 2,
        "both failed storage obligations must survive presentation grouping"
    );
}

#[test]
fn return_owner_deduplicates_borrows_of_the_same_storage() {
    let source =
        "&i32 escape(bool c) { i32 x = 1; &i32 r; if (c) { r = &x; } else { r = &x; } return r; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        1,
        "{:#?}",
        compilation.diagnostics
    );
    assert_eq!(
        compilation.diagnostics[0].primary_label.as_deref(),
        Some("this reference would outlive `x`")
    );
}

#[test]
fn return_owner_input_region_failure_has_one_complete_explanation() {
    let source = "&'a i32 first<'a, 'b>(&'a i32 value, &'b i32 other) { return other; }";
    let mut compilation = parse_diagnostic_source(source);
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        1,
        "{:#?}",
        compilation.diagnostics
    );
    let diagnostic = &compilation.diagnostics[0];
    assert_eq!(diagnostic.code, "E-REGION-RETURN");
    assert!(
        diagnostic
            .primary_label
            .as_deref()
            .unwrap()
            .contains("actual origin")
    );
    assert!(
        diagnostic
            .labels
            .iter()
            .any(|label| label.message == "return region is declared by this signature")
    );
    assert!(
        compilation
            .local_analysis
            .as_ref()
            .unwrap()
            .functions
            .iter()
            .flat_map(|f| &f.findings)
            .any(
                |f| f.predicate == cavo_compiler::local::Predicate::ReturnRegion
                    && f.assessment == cavo_compiler::local::Assessment::NotEstablished
            )
    );
}

fn recovery_codes(source: &str) -> Vec<&'static str> {
    let mut compilation = parse_diagnostic_source(source);
    assert!(
        compilation.check().is_none(),
        "an error type must not approve this program"
    );
    compilation.diagnostics.iter().map(|d| d.code).collect()
}

#[test]
fn recovery_error_receivers_do_not_invent_fields_or_methods() {
    for source in [
        "void inspect(Missing value) { auto a = value.bottom; a.load().next; value.clone(); }",
        "struct Holder { Missing data; } void inspect(&Holder holder) { holder.data.bottom.load().next; }",
        "type Broken = Missing; void inspect(Broken value) { value.load(); Broken::make(); }",
        "void inspect(& &Missing value) { value.bottom.load(); }",
    ] {
        assert_eq!(recovery_codes(source), ["E-NAME-UNKNOWN"], "{source}");
    }
}

#[test]
fn recovery_invalid_calls_still_check_independent_arguments() {
    let codes = recovery_codes(
        "void inspect() { Missing::make(first_missing); Missing::again(second_missing); }",
    );
    assert_eq!(
        codes,
        ["E-NAME-UNKNOWN", "E-NAME-UNKNOWN", "E-NAME-UNKNOWN"]
    );
    let codes = recovery_codes(
        "struct Holder { Missing data; } void inspect(Holder holder) { holder.data.load(another_missing); }",
    );
    assert_eq!(codes, ["E-NAME-UNKNOWN", "E-NAME-UNKNOWN"]);
}

#[test]
fn recovery_unknown_construction_still_checks_initializer_expressions() {
    let codes =
        recovery_codes("void inspect() { auto value = Missing { field: independent_missing }; }");
    assert_eq!(codes, ["E-NAME-UNKNOWN", "E-NAME-UNKNOWN"]);
}

#[test]
fn recovery_known_nominal_shapes_keep_independent_member_errors() {
    let source = "struct Holder<T> { T value; i32 ready; } void inspect(Holder<Missing> holder) { holder.value.load(); holder.typo; holder.missing_method(); }";
    let codes = recovery_codes(source);
    assert_eq!(
        codes,
        ["E-NAME-UNKNOWN", "E-TYPE-FIELD", "E-METHOD-SELECTION"]
    );
}

#[test]
fn recovery_unknown_match_subject_keeps_bindings_and_independent_arm_errors() {
    let source = "i32 inspect(Missing value) { auto result = value.load()?; return match result { Some(item) => item.load(independent_missing), None => other_missing }; }";
    let codes = recovery_codes(source);
    assert_eq!(
        codes,
        ["E-NAME-UNKNOWN", "E-NAME-UNKNOWN", "E-NAME-UNKNOWN"]
    );
}

#[test]
fn recovery_a_real_try_error_survives_an_unrelated_missing_type() {
    let codes = recovery_codes("void other(Missing value) {} i32 inspect() { return 1?; }");
    assert_eq!(codes, ["E-NAME-UNKNOWN", "E-TRY-RESULT"]);
}

#[test]
fn recovery_missing_roots_are_bounded_and_module_scoped() {
    let mut compilation = Compilation::default();
    let uses = (0..12)
        .map(|i| format!("void f{i}(Missing value) {{}} "))
        .collect::<String>();
    for (path, source) in [
        (
            "left.cavo",
            format!("module left; {uses} void calls() {{ Missing::make(); Missing::again(); }}"),
        ),
        (
            "right.cavo",
            "module right; void inspect(Missing value) {}".into(),
        ),
    ] {
        let file = compilation.sources.add(path, source).unwrap();
        compilation.parse(file);
    }
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        2,
        "{:#?}",
        compilation.diagnostics
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .all(|d| d.code == "E-NAME-UNKNOWN" && d.labels.len() <= 4)
    );
    assert_eq!(compilation.diagnostics[0].labels.len(), 4);
    assert_ne!(
        compilation.diagnostics[0].primary.file,
        compilation.diagnostics[1].primary.file
    );
}

#[test]
fn recovery_missing_members_of_a_known_module_are_distinct_roots() {
    let mut compilation = Compilation::default();
    for (path, source) in [
        ("known.cavo", "module known; pub i32 exists() { return 1; }"),
        (
            "app.cavo",
            "module app; import known; void inspect() { known::first_missing(); known::second_missing(); }",
        ),
    ] {
        let file = compilation.sources.add(path, source.into()).unwrap();
        compilation.parse(file);
    }
    assert!(compilation.check().is_none());
    assert_eq!(
        compilation.diagnostics.len(),
        2,
        "{:#?}",
        compilation.diagnostics
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .all(|d| d.code == "E-NAME-UNKNOWN")
    );
    assert!(compilation.diagnostics[0].message.contains("first_missing"));
    assert!(
        compilation.diagnostics[1]
            .message
            .contains("second_missing")
    );
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
