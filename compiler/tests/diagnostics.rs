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
            "  |\n\n",
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
    assert!(output.contains("| ..."));
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
