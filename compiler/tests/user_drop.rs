use cavo_compiler::{Compilation, hir};

fn compilation(body: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let source = format!("@lang(drop) trait Drop {{ void drop(&mut Self self); }} {body}");
    let file = compilation.sources.add("drop.cavo", source).unwrap();
    compilation.parse(file);
    compilation
}

#[test]
fn user_destructors_are_registered_by_role_and_have_real_bodies() {
    let mut compilation = compilation(
        "struct Owned { i32 value; } impl Drop for Owned { void drop(&mut Self self) { self.value = 0; } }
         void use() { Owned value = Owned { value: 3 }; }",
    );
    let (mut program, _) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let owned = program.records[0].definition;
    let ty = program.definitions[owned.0 as usize].ty;
    let selected = hir::traits::select_drop(&program, ty).unwrap().unwrap();
    hir::traits::check_bounds(&mut program, selected.definition, &selected.type_arguments).unwrap();
    assert!(
        program
            .functions
            .iter()
            .any(|function| function.definition == selected.definition)
    );
}

#[test]
fn a_destructor_cannot_be_called_manually_or_hidden_in_a_function_pointer() {
    for expression in [
        "value.drop();",
        "Owned::drop(&mut value);",
        "fn(&mut Owned)->void function = Owned::drop; function(&mut value);",
    ] {
        let mut compilation = compilation(&format!(
            "struct Owned {{}} impl Drop for Owned {{ void drop(&mut Self self) {{}} }} void f() {{ Owned value = Owned {{}}; {expression} }}",
        ));
        assert!(compilation.check_types().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E-DROP-EXPLICIT"),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn partial_moves_from_drop_owners_are_rejected() {
    let mut compilation = compilation(
        "struct Pair<T> { T first; T second; } impl<T> Drop for Pair<T> { void drop(&mut Self self) {} }
         T take<T>(Pair<T> value) { return move value.first; }",
    );
    assert!(compilation.check().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-MOVE-DROP"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn destructor_effects_are_checked_instead_of_assumed_from_the_role() {
    for body in ["while (true) {}", "self.drop();"] {
        let mut compilation = compilation(&format!(
            "struct Owned {{}} impl Drop for Owned {{ void drop(&mut Self self) {{ {body} }} }}",
        ));
        assert!(compilation.check_types().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "E-DROP-EFFECT" | "E-DROP-EXPLICIT")),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn drop_cannot_specialize_only_some_generic_instances() {
    let mut invalid = compilation(
        "struct Owned<T> { T value; } impl Drop for Owned<i32> { void drop(&mut Self self) {} }",
    );
    assert!(invalid.check_types().is_none());
    assert!(
        invalid
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-DROP-SPECIALIZATION")
    );
    let mut valid = compilation(
        "@lang(copy) trait Copy {} struct Owned<T: Copy> { T value; } impl<T: Copy> Drop for Owned<T> { void drop(&mut Self self) {} }",
    );
    assert!(valid.check_types().is_some(), "{:#?}", valid.diagnostics);
}
