#[path = "support/pattern_machine.rs"]
pub mod machine;
use machine::{Machine, Outcome, Value, checked};

#[test]
fn const_runtime_contracts_use_entry_state_and_prepared_result() {
    let (compilation, hir, mir) = checked(
        "const usize increment(usize n) requires n < 10 ensures result == old(n) + 1 { n += 1; return n; }",
    );
    let mut path = Machine::new(
        &compilation,
        &hir,
        &mir,
        "increment",
        vec![("n", Value::Integer(3))],
    );
    assert_eq!(path.run(), Value::Integer(4));
}

#[test]
fn failed_runtime_requires_and_ensures_abort_instead_of_becoming_compile_errors() {
    for source in [
        "const usize f(usize n) requires n != 0 { return n; }",
        "const usize f(usize n) ensures result != 0 { return n; }",
    ] {
        let (compilation, hir, mir) = checked(source);
        let mut path = Machine::new(
            &compilation,
            &hir,
            &mir,
            "f",
            vec![("n", Value::Integer(0))],
        );
        assert_eq!(path.run_outcome(), Outcome::Abort);
    }
}

#[test]
fn unreachable_old_arithmetic_is_not_eagerly_evaluated_at_entry() {
    let (compilation, hir, mir) =
        checked("const usize f(usize n) ensures true || old(1usize / 0usize) == 0 { return n; }");
    let mut path = Machine::new(
        &compilation,
        &hir,
        &mir,
        "f",
        vec![("n", Value::Integer(7))],
    );
    assert_eq!(path.run(), Value::Integer(7));
}
