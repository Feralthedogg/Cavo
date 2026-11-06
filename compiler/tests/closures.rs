use cavo_compiler::{Compilation, hir, types::Ty};

fn parse(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("closures.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = parse(source);
    let result = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (hir, _) = result.expect("checked closure MIR");
    (compilation, hir)
}

#[test]
fn move_capture_of_copy_data_remains_a_reusable_shared_callable() {
    let (_, hir) = checked(
        "i32 f(i32 input) { auto callback = [move input](i32 offset) -> i32 { return input + offset; }; i32 first = callback(1); return first + callback(2); }",
    );
    assert_eq!(hir.closures.len(), 1);
    assert_eq!(hir.closures[0].kind, hir::ClosureKind::Fn);
    assert_eq!(
        hir.closures[0]
            .adapters
            .iter()
            .map(|(kind, _)| *kind)
            .collect::<Vec<_>>(),
        [hir::ClosureKind::FnMut, hir::ClosureKind::FnOnce]
    );
    let closure = &hir.closures[0];
    let Ty::Function { parameters, .. } = hir.types.get(hir.definitions[closure.function].ty)
    else {
        panic!("closure entry signature");
    };
    assert!(matches!(
        hir.types.get(parameters[0]),
        Ty::Reference { mutable: false, .. }
    ));
}

#[test]
fn mutable_captures_are_callable_repeatedly_and_release_after_last_use() {
    let (_, hir) = checked(
        "i32 f() { i32 value = 0; auto update = [&mut value]() { value += 1; }; update(); update(); return value; }",
    );
    assert_eq!(hir.closures[0].kind, hir::ClosureKind::FnMut);
}

#[test]
fn owned_non_copy_capture_requires_an_explicit_consuming_call() {
    let (_, hir) = checked(
        "T f<T>(T value) { auto take = [move value]() -> T { return move value; }; return (move take)(); }",
    );
    assert_eq!(hir.closures[0].kind, hir::ClosureKind::FnOnce);
    let mut implicit = parse(
        "T f<T>(T value) { auto take = [move value]() -> T { return move value; }; return take(); }",
    );
    assert!(implicit.check_mir().is_none());
    assert!(
        implicit
            .diagnostics
            .iter()
            .any(|error| error.code == "E-CLOSURE-MOVE")
    );
}

#[test]
fn consuming_a_closure_twice_and_using_a_moved_capture_are_rejected() {
    for source in [
        "void f<T>(T value) { auto take = [move value]() -> T { return move value; }; T one = (move take)(); T two = (move take)(); }",
        "T f<T>(T value) { auto take = [move value]() -> T { return move value; }; return move value; }",
    ] {
        let mut compilation = parse(source);
        assert!(compilation.check_mir().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|error| error.code.starts_with("E-MOVE")),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn captures_are_explicit_unique_and_respect_binding_mutability() {
    for source in [
        "i32 f(i32 value) { auto callback = []() -> i32 { return value; }; return callback(); }",
        "void f(i32 value) { auto callback = [&value, move value]() {}; }",
        "void f() { const i32 value = 1; auto callback = [&mut value]() {}; }",
    ] {
        let mut compilation = parse(source);
        assert!(compilation.check_mir().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|error| error.code == "E-CLOSURE-CAPTURE"),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn fn_mut_requires_mutable_environment_access() {
    let mut compilation = parse(
        "i32 f(i32 value) { const auto callback = [move value]() -> i32 { value += 1; return value; }; return callback(); }",
    );
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|error| error.code == "E-CLOSURE-MUTABLE")
    );
    checked(
        "i32 f(i32 value) { auto callback = [move value]() -> i32 { value += 1; return value; }; auto reference = &mut callback; return (*reference)(); }",
    );
}

#[test]
fn fresh_closures_have_a_scoped_owned_environment() {
    checked(
        "i32 f(i32 value) { return ([move value](i32 offset) -> i32 { return value + offset; })(3); }",
    );
    checked("T f<T>(T value) { return ([move value]() -> T { return move value; })(); }");
}

#[test]
fn inferred_returns_and_nested_closures_keep_their_own_capture_scopes() {
    let (_, hir) = checked(
        "i32 f(i32 value) { auto outer = [move value]() { auto inner = [move value]() { return value; }; return inner(); }; return outer(); }",
    );
    assert_eq!(hir.closures.len(), 2);
    assert!(
        hir.closures
            .iter()
            .all(|closure| closure.kind == hir::ClosureKind::Fn)
    );
}

#[test]
fn closures_remap_const_and_type_parameters_to_their_generated_owners() {
    checked(
        "usize count<const usize N>() { auto callback = []() { return N; }; return callback(); } usize f() { return count::<3>(); }",
    );
    checked(
        "T take<T, const usize N>(T value) { auto callback = [move value]() -> T { return move value; }; return (move callback)(); } i32 f() { return take::<i32, 2>(7); }",
    );
}

#[test]
fn generated_closure_functions_keep_the_owners_copy_bound() {
    let (_, hir) = checked(
        "@lang(copy) trait Plain {} T repeat<T: Plain>(T value) { auto callback = [move value]() -> T { return move value; }; T first = callback(); return callback(); } i32 f() { return repeat(7); }",
    );
    assert_eq!(hir.closures[0].kind, hir::ClosureKind::Fn);
    for definition in std::iter::once(hir.closures[0].function).chain(
        hir.closures[0]
            .adapters
            .iter()
            .map(|(_, definition)| *definition),
    ) {
        assert_eq!(hir.definitions[definition].bounds.len(), 1);
    }
}

#[test]
fn an_uncaptured_local_cannot_expose_a_shadowed_const_parameter() {
    let mut compilation = parse(
        "usize f<const usize N>() { usize N = 2; auto callback = []() { return N; }; return callback(); }",
    );
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|error| error.code == "E-CLOSURE-CAPTURE")
    );
}

#[test]
fn captured_borrows_cannot_escape_or_hide_a_live_loan() {
    for source in [
        "&i32 bad() { i32 value = 1; auto callback = [&value]() -> &i32 { return &value; }; return callback(); }",
        "i32 bad() { i32 value = 1; auto callback = [&value]() -> i32 { return value; }; value = 2; return callback(); }",
        "void bad() { i32 value = 1; &mut i32 reference = &mut value; auto callback = [&reference]() { *reference = 2; }; callback(); }",
    ] {
        let mut compilation = parse(source);
        assert!(
            compilation.check_mir().is_none(),
            "unsafe closure accepted: {source}"
        );
    }
}

#[test]
fn returned_references_keep_the_original_capture_owner() {
    checked(
        "&i32 f(&i32 input) { auto callback = [move input]() -> &i32 { return input; }; return callback(); }",
    );
    let mut compilation =
        parse("void f(i32 input) { auto callback = [move input]() -> &i32 { return &input; }; }");
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|error| error.code == "E-CLOSURE-ESCAPE")
    );
}

#[test]
fn stronger_closures_satisfy_consuming_callable_bounds_through_real_adapters() {
    for closure in [
        "[move value](i32 extra) -> i32 { return value + extra; }",
        "[move value](i32 extra) -> i32 { value += extra; return value; }",
    ] {
        checked(&format!(
            "@lang(fn_once) trait Consume<A, R> {{ R call(Self self, A value); }} i32 apply<F: Consume<i32, i32>>(F callback) {{ return (move callback)(2); }} i32 f(i32 value) {{ auto callback = {closure}; return apply(move callback); }}"
        ));
    }
}
