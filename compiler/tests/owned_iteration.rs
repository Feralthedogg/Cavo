#[path = "support/pattern_machine.rs"]
mod pattern_machine;

use cavo_compiler::{Compilation, mir};
use pattern_machine::{Machine, Outcome, Value, checked};

fn array() -> Value {
    Value::Fields(vec![
        Some(Value::Owned("first")),
        Some(Value::Owned("second")),
        Some(Value::Owned("third")),
    ])
}

fn drops(machine: &Machine<'_>) -> Vec<String> {
    machine
        .events
        .iter()
        .filter_map(|event| event.strip_prefix("drop:").map(str::to_owned))
        .collect()
}

#[test]
fn breaking_drops_the_current_element_before_the_remaining_tail() {
    let (compilation, hir, mir) =
        checked("void f<T>(T[3] values) { for (auto item in move values) { break; } }");
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("values", array())]);
    assert_eq!(machine.run(), Value::Unit);
    assert_eq!(drops(&machine), ["first", "second", "third"]);
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| event.starts_with("next-leaf:"))
            .count(),
        1
    );
}

#[test]
fn continue_consumes_each_element_once_without_skipping_or_restarting() {
    let (compilation, hir, mir) =
        checked("void f<T>(T[3] values) { for (auto item in move values) { continue; } }");
    let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("values", array())]);
    assert_eq!(machine.run(), Value::Unit);
    assert_eq!(drops(&machine), ["first", "second", "third"]);
    let next: Vec<_> = machine
        .events
        .iter()
        .filter(|event| event.starts_with("next-leaf:"))
        .map(String::as_str)
        .collect();
    assert_eq!(
        next,
        ["next-leaf:first", "next-leaf:second", "next-leaf:third"]
    );
}

#[test]
fn returning_an_element_preserves_it_and_cleans_only_the_remaining_owners() {
    let (compilation, hir, mir) = checked(
        "T f<T>(T[3] values, T fallback) { for (auto item in move values) { return move item; } return move fallback; }",
    );
    let mut machine = Machine::new(
        &compilation,
        &hir,
        &mir,
        "f",
        vec![("values", array()), ("fallback", Value::Owned("fallback"))],
    );
    assert_eq!(machine.run(), Value::Owned("first"));
    assert_eq!(drops(&machine), ["second", "third", "fallback"]);
}

#[test]
fn panic_and_cancellation_clean_the_active_binding_and_iterator_tail() {
    let (compilation, hir, mir) = checked(
        "void work() {} void f<T>(T[3] values) { for (auto item in move values) { work(); } }",
    );
    for reason in [mir::ExitKind::Panic, mir::ExitKind::Cancel] {
        let mut machine = Machine::new(&compilation, &hir, &mir, "f", vec![("values", array())]);
        machine.failure = Some(("work", reason));
        assert_eq!(machine.run_outcome(), Outcome::Resume(reason));
        assert_eq!(drops(&machine), ["first", "second", "third"]);
    }
}

#[test]
fn empty_owned_arrays_never_initialize_an_iteration_binding() {
    let (compilation, hir, mir) = checked(
        "void work() {} void f<T>(T[0] values) { for (auto item in move values) { work(); } }",
    );
    let mut machine = Machine::new(
        &compilation,
        &hir,
        &mir,
        "f",
        vec![("values", Value::Fields(vec![]))],
    );
    machine.stub("work", Value::Unit);
    assert_eq!(machine.run(), Value::Unit);
    assert!(machine.events.is_empty());
}

#[test]
fn non_copy_arrays_cannot_be_copied_or_moved_out_of_a_borrowed_place() {
    for source in [
        "void f<T>(T[3] values) { for (auto item in values) {} }",
        "void f<T>(&T[3] values) { for (auto item in move *values) {} }",
    ] {
        let mut compilation = Compilation::default();
        let file = compilation
            .sources
            .add("borrowed-iterator.cavo", source.into())
            .unwrap();
        compilation.parse(file);
        assert!(compilation.check_mir().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.starts_with("E-MOVE")),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn exhausted_edge_cannot_read_the_uninitialized_iteration_result() {
    let (_, mut hir, mut mir) = checked(
        "T f<T>(T[3] values, T fallback) { for (auto item in move values) {} return move fallback; }",
    );
    let body = &mut mir.functions[0];
    let (destination, none) = body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            mir::Terminator::IteratorNext {
                destination, none, ..
            } => Some((destination.clone(), *none)),
            _ => None,
        })
        .expect("owned iterator");
    let target = &mut body.blocks[none.0 as usize];
    target.statements.insert(
        0,
        mir::Statement {
            kind: mir::StatementKind::Assign {
                destination: mir::Place::local(body.return_local),
                value: mir::Rvalue::Use(mir::Operand::Move(destination)),
            },
            span: target.span,
        },
    );
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn iterator_metadata_does_not_materialize_one_flag_per_array_element() {
    let (compilation, hir, mir) =
        checked("void f<T>(T[1000000] values) { for (auto item in move values) { break; } }");
    let body = &mir.functions[0];
    assert_eq!(
        body.locals
            .iter()
            .filter(|local| local.kind == mir::LocalKind::ArrayIterator)
            .count(),
        1
    );
    assert!(body.locals.len() < 64);
    assert!(body.blocks.len() < 256);
    let drops = &compilation.mir_analysis.as_ref().unwrap().drops;
    assert!(drops.functions[0].flags.len() < 64);
    assert!(hir.functions[0].locals.len() < 64);
}
