#[path = "support/pattern_machine.rs"]
mod pattern_machine;

use cavo_compiler::{Compilation, hir, mir};
use pattern_machine::{Machine, Value, checked, definition};

const RESULT: &str = "@lang(result) enum Outcome<T, E> { Ok(T), Err(E) }";

fn failed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("result.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    assert!(
        compilation.check_mir().is_none(),
        "unexpectedly accepted {source}"
    );
    compilation
}

#[test]
fn question_mark_returns_only_the_error_variant_and_continues_on_success() {
    let source = format!(
        "{RESULT} Outcome<i32, i32> f(Outcome<i32, i32> value) {{ i32 number = value?; return Outcome::Ok(number + 1); }}"
    );
    let (compilation, hir, mir) = checked(&source);
    let ok = definition(&compilation, &hir, "Ok");
    let err = definition(&compilation, &hir, "Err");
    for (variant, input, output) in [(ok, 4, 5), (err, 9, 9)] {
        let value = Value::Variant(variant, vec![Some(Value::Integer(input))]);
        let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("value", value)]);
        assert_eq!(
            machine.run(),
            Value::Variant(variant, vec![Some(Value::Integer(output))])
        );
    }
}

#[test]
fn question_mark_transfers_non_copy_success_values_without_duplicate_drop() {
    let source = format!(
        "{RESULT} Outcome<T, i32> f<T>(Outcome<T, i32> value) {{ T payload = (move value)?; return Outcome::Ok(move payload); }}"
    );
    let (compilation, hir, mir) = checked(&source);
    let ok = definition(&compilation, &hir, "Ok");
    let value = Value::Variant(ok, vec![Some(Value::Owned("payload"))]);
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("value", value)]);
    assert_eq!(
        machine.run(),
        Value::Variant(ok, vec![Some(Value::Owned("payload"))])
    );
    assert!(!machine.events.iter().any(|event| event == "drop:payload"));
}

#[test]
fn question_mark_runs_registered_cleanup_before_error_return() {
    let source = format!(
        "{RESULT} void mark(i32 n) {{}} Outcome<i32, i32> f(Outcome<i32, i32> value) {{ defer {{ mark(1); }} i32 number = value?; return Outcome::Ok(number); }}"
    );
    let (compilation, hir, mir) = checked(&source);
    let err = definition(&compilation, &hir, "Err");
    let value = Value::Variant(err, vec![Some(Value::Integer(5))]);
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("value", value)]);
    assert_eq!(
        machine.run(),
        Value::Variant(err, vec![Some(Value::Integer(5))])
    );
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| *event == "call:mark")
            .count(),
        1
    );
}

#[test]
fn differing_error_types_require_a_real_from_implementation() {
    let source = format!(
        "{RESULT} struct Failure {{ i32 code; }} Outcome<i32, Failure> f(Outcome<i32, i32> value) {{ i32 number = value?; return Outcome::Ok(number); }}"
    );
    let compilation = failed(&source);
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-TRY-FROM"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn error_conversion_selects_the_declared_from_implementation() {
    let source = format!(
        "{RESULT} @lang(from) trait Convert<T> {{ Self from(T value); }} struct Failure {{ i32 code; }} impl Convert<i32> for Failure {{ Failure from(i32 value) {{ return Failure {{ code: value }}; }} }} Outcome<i32, Failure> f(Outcome<i32, i32> value) {{ i32 number = value?; return Outcome::Ok(number); }}"
    );
    let (compilation, hir, mir) = checked(&source);
    let err = definition(&compilation, &hir, "Err");
    let converted = Value::Fields(vec![Some(Value::Integer(12))]);
    let input = Value::Variant(err, vec![Some(Value::Integer(12))]);
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("value", input)]);
    machine.stub("from", converted.clone());
    assert_eq!(machine.run(), Value::Variant(err, vec![Some(converted)]));
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| *event == "call:from")
            .count(),
        1
    );
}

#[test]
fn similarly_named_enums_do_not_become_result_language_items() {
    let compilation = failed(
        "enum Result<T, E> { Ok(T), Err(E) } Result<i32, i32> f(Result<i32, i32> value) { i32 x = value?; return Result::Ok(x); }",
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-TRY-RESULT")
    );
}

#[test]
fn result_language_items_reject_bad_shapes_and_duplicate_providers() {
    for source in [
        "@lang(result) enum Bad<T, E> { Ok(T), Err(T) }",
        "@lang(result) enum One<T, E> { Ok(T), Err(E) } @lang(result) enum Two<T, E> { Ok(T), Err(E) }",
    ] {
        let compilation = failed(source);
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.starts_with("E-LANG-"))
        );
    }
}

#[test]
fn propagation_is_an_explicit_typed_match_with_an_early_return_arm() {
    let (compilation, hir, mir) = checked(&format!(
        "{RESULT} Outcome<i32, i32> f(Outcome<i32, i32> value) {{ return Outcome::Ok(value?); }}"
    ));
    assert!(
        hir.functions[0]
            .expressions
            .iter()
            .any(|expression| matches!(expression.kind, hir::ExprKind::Match { .. }))
    );
    let function = &mir.functions[0];
    assert!(
        function
            .blocks
            .iter()
            .any(|block| matches!(block.terminator, mir::Terminator::Return))
    );
    assert!(compilation.mir_analysis.is_some());
}
