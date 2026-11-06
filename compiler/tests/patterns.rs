#[path = "support/pattern_machine.rs"]
mod pattern_machine;

use cavo_compiler::{Compilation, mir};
use pattern_machine::{Machine, Value, checked, definition};

fn rejected(source: &str, code: &str) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("bad-pattern.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == code),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn boolean_and_scalar_patterns_select_only_the_matching_arm() {
    let (compilation, hir, mir) = checked(
        "i32 flag(bool value) { return match value { true => 11, false => 22 }; } i32 number(i32 value) { return match value { 0 => 30, 7 => 40, _ => 50 }; }",
    );
    for (input, expected) in [(true, 11), (false, 22)] {
        let mut machine = Machine::new(
            &compilation,
            &hir,
            &mir,
            "flag",
            vec![("value", Value::Bool(input))],
        );
        assert_eq!(machine.run(), Value::Integer(expected));
    }
    for (input, expected) in [(0, 30), (7, 40), (8, 50)] {
        let mut machine = Machine::new(
            &compilation,
            &hir,
            &mir,
            "number",
            vec![("value", Value::Integer(input))],
        );
        assert_eq!(machine.run(), Value::Integer(expected));
    }
}

#[test]
fn nested_positional_patterns_cover_the_actual_payload_product() {
    let (compilation, hir, mir) = checked(
        "enum Inner { Flag(bool), Empty } enum Outer { Wrap(Inner), Other } i32 f(Outer value) { return match value { Outer::Wrap(Inner::Flag(true)) => 1, Outer::Wrap(Inner::Flag(false)) => 2, Outer::Wrap(Inner::Empty) => 3, Outer::Other => 4 }; }",
    );
    let wrap = definition(&compilation, &hir, "Wrap");
    let flag = definition(&compilation, &hir, "Flag");
    let empty = definition(&compilation, &hir, "Empty");
    let other = definition(&compilation, &hir, "Other");
    let cases = [
        (
            Value::Variant(
                wrap,
                vec![Some(Value::Variant(flag, vec![Some(Value::Bool(true))]))],
            ),
            1,
        ),
        (
            Value::Variant(
                wrap,
                vec![Some(Value::Variant(flag, vec![Some(Value::Bool(false))]))],
            ),
            2,
        ),
        (
            Value::Variant(wrap, vec![Some(Value::Variant(empty, vec![]))]),
            3,
        ),
        (Value::Variant(other, vec![]), 4),
    ];
    for (value, expected) in cases {
        let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("value", value)]);
        assert_eq!(machine.run(), Value::Integer(expected));
    }
}

#[test]
fn a_false_guard_does_not_move_the_candidate_payload() {
    let (compilation, hir, mir) = checked(
        "enum Packet<T> { Item(T), Empty } bool refuse<T>(&T value) { return false; } T f<T>(Packet<T> packet, T fallback) { return match (move packet) { Packet::Item(payload) if refuse(&payload) => move payload, Packet::Item(payload) => move payload, Packet::Empty => move fallback }; }",
    );
    let item = definition(&compilation, &hir, "Item");
    let input = Value::Variant(item, vec![Some(Value::Owned("payload"))]);
    let mut machine = Machine::new(
        &compilation,
        &hir,
        &mir,
        "f",
        vec![("packet", input), ("fallback", Value::Owned("fallback"))],
    );
    machine.stub("refuse", Value::Bool(false));
    assert_eq!(machine.run(), Value::Owned("payload"));
    let guard = machine
        .events
        .iter()
        .position(|event| event == "call:refuse")
        .unwrap();
    let moved = machine
        .events
        .iter()
        .position(|event| event == "move-leaf:payload")
        .unwrap();
    assert!(guard < moved, "{:#?}", machine.events);
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| event.as_str() == "drop:fallback")
            .count(),
        1
    );
    assert!(!machine.events.iter().any(|event| event == "drop:payload"));
}

#[test]
fn borrowed_patterns_produce_references_to_the_original_payload() {
    let (compilation, hir, mir) = checked(
        "enum Choice { Value(i32), Empty } i32 f() { Choice choice = Choice::Value(17); return match &choice { Choice::Value(value) => *value, Choice::Empty => 0 }; }",
    );
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![]);
    assert_eq!(machine.run(), Value::Integer(17));
}

#[test]
fn block_arms_return_through_the_enclosing_cleanup() {
    let (compilation, hir, mir) = checked(
        "void mark() {} i32 f(bool value) { defer { mark(); } match value { true => { return 7; }, false => { return 9; } }; }",
    );
    for (value, expected) in [(true, 7), (false, 9)] {
        let mut machine = Machine::new(
            &compilation,
            &hir,
            &mir,
            "f",
            vec![("value", Value::Bool(value))],
        );
        assert_eq!(machine.run(), Value::Integer(expected));
        assert_eq!(
            machine
                .events
                .iter()
                .filter(|event| event.as_str() == "call:mark")
                .count(),
            1
        );
    }
}

#[test]
fn guarded_rows_do_not_establish_exhaustiveness() {
    rejected(
        "i32 f(bool value) { return match value { true if value => 1, false => 0 }; }",
        "E-MATCH-EXHAUSTIVE",
    );
    rejected(
        "enum Inner { Flag(bool), Empty } enum Outer { Wrap(Inner), Other } i32 f(Outer value) { return match value { Outer::Wrap(Inner::Flag(true)) => 1, Outer::Wrap(Inner::Empty) => 2, Outer::Other => 3 }; }",
        "E-MATCH-EXHAUSTIVE",
    );
}

#[test]
fn guards_cannot_consume_uncommitted_non_copy_bindings() {
    rejected(
        "enum Packet<T> { Item(T), Empty } bool consume<T>(T value) { return true; } T f<T>(Packet<T> packet, T fallback) { return match (move packet) { Packet::Item(payload) if consume(move payload) => move fallback, _ => move fallback }; }",
        "E-MATCH-GUARD-MOVE",
    );
}

#[test]
fn owned_non_copy_subjects_require_explicit_transfer() {
    rejected(
        "enum Packet<T> { Item(T), Empty } void f<T>(Packet<T> packet) { match packet { Packet::Item(payload) => {}, Packet::Empty => {} }; }",
        "E-MATCH-MOVE",
    );
}

#[test]
fn patterns_reject_wrong_variant_arity_and_wrong_enum_identity() {
    rejected(
        "enum Choice { Value(i32), Empty } i32 f(Choice choice) { return match choice { Choice::Value(a, b) => a, Choice::Empty => 0 }; }",
        "E-MATCH-ARITY",
    );
    rejected(
        "enum A { One } enum B { Two } i32 f(A value) { return match value { B::Two => 1, _ => 2 }; }",
        "E-MATCH-VARIANT",
    );
}

#[test]
fn verifier_rejects_payload_access_after_removing_the_tag_test() {
    let (_, mut hir, mut mir) = checked(
        "enum Choice { Value(i32), Empty } i32 f(Choice value) { return match value { Choice::Value(payload) => payload, Choice::Empty => 0 }; }",
    );
    let body = &mut mir.functions[0];
    let block = body
        .blocks
        .iter_mut()
        .find(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::IsVariant { .. },
                        ..
                    }
                )
            })
        })
        .expect("tag test");
    let mir::Terminator::Switch { yes, .. } = block.terminator else {
        panic!("tag test switch");
    };
    block.statements.retain(|statement| {
        !matches!(
            statement.kind,
            mir::StatementKind::Assign {
                value: mir::Rvalue::IsVariant { .. },
                ..
            }
        )
    });
    block.terminator = mir::Terminator::Goto(yes);
    assert!(mir.validate(&mut hir).is_err());
}
