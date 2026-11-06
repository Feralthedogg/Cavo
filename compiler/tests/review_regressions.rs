use cavo_compiler::{Compilation, hir};

#[test]
fn infinite_record_enum_and_instantiated_generic_values_are_rejected() {
    for source in [
        "enum E { Nil, Cons(E) }",
        "struct W<T> { T v; } struct A { W<A> a; }",
        "enum E<T> { None, Some(T) } struct A { E<A> a; }",
        "struct W<T> { W<W<T>> next; }",
        "struct A { B value; } enum B { Value(A) }",
    ] {
        let (c, p) = check(source);
        assert!(p.is_none());
        assert!(
            c.diagnostics.iter().any(|d| d.code == "E-TYPE-RECURSIVE"),
            "{source}\n{:#?}",
            c.diagnostics
        );
    }
    passes(
        "struct Link { ptr<Link> next; } enum E { Nil, Cons(ptr<E>) } struct W<T> { T v; } struct Finite { W<W<i32>> value; }",
    );
    passes("struct Phantom<T> {} struct Finite { Phantom<Finite> value; }");
}

#[test]
fn many_functions_and_reversed_call_chains_have_the_same_verdict() {
    let empty = (0..8000)
        .map(|i| format!("void independent_{i}() {{}}\n"))
        .collect::<String>();
    passes(&empty);
    let chain: Vec<_> = (0..2500)
        .map(|i| {
            if i == 2499 {
                format!("i32 chain_{i}() {{ return 1; }}\n")
            } else {
                format!("i32 chain_{i}() {{ return chain_{}(); }}\n", i + 1)
            }
        })
        .collect();
    passes(&chain.concat());
    passes(&chain.into_iter().rev().collect::<String>());
}
fn check(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut c = Compilation::default();
    let file = c.sources.add("review.cavo", source.into()).unwrap();
    c.parse(file);
    let p = c.check();
    (c, p)
}
fn passes(source: &str) {
    let (c, p) = check(source);
    assert!(p.is_some(), "{:#?}", c.diagnostics);
    assert!(c.diagnostics.is_empty(), "{:#?}", c.diagnostics);
}

#[test]
fn a_mutable_reference_callback_is_assignable_to_its_own_alias_type() {
    passes("type F = fn(&mut i32) -> void; F id(F g) { return g; }");
    passes(
        "type F = fn(&mut i32) -> void; void update(&mut i32 x) { *x=1; } F id(F g) { return g; } i32 f() { F callback=id(update); i32 x=0; callback(&mut x); return x; }",
    );
}

#[test]
fn compact_references_parse_without_changing_logical_and() {
    passes("i32 get(&&i32 value) { return **value; } bool both(bool a,bool b) { return a&&b; }");
    let mut c = Compilation::default();
    let file = c
        .sources
        .add(
            "borrow.cavo",
            "void f() { i32 x=1; auto nested=&&x; }".into(),
        )
        .unwrap();
    c.parse(file);
    assert!(c.diagnostics.is_empty(), "{:#?}", c.diagnostics);
}

#[test]
fn flat_operator_and_else_if_chains_do_not_consume_syntax_nesting() {
    passes(&format!("i32 f(i32 x) {{ return x{}; }}", "+1".repeat(128)));
    let chain = (0..124).map(|_| "else if (x) {}").collect::<String>();
    passes(&format!("void f(bool x) {{ if(x) {{}} {chain} }}"));
}

#[test]
fn callable_type_errors_show_the_lifetimes_that_differ() {
    let (c, p) =
        check("void f<'a,'b>(fn(&'a i32) -> void first) { fn(&'b i32) -> void second=first; }");
    assert!(p.is_none());
    let label = c
        .diagnostics
        .iter()
        .find(|d| d.code == "E-TYPE-MISMATCH")
        .unwrap()
        .primary_label
        .as_ref()
        .unwrap();
    assert!(label.contains("'a") && label.contains("'b"), "{label}");
}
