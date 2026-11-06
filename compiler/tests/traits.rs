use cavo_compiler::{Compilation, hir};

fn parse(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("traits.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn typed(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = parse(source);
    let program = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, program)
}

#[test]
fn associated_functions_use_type_paths_and_infer_nominal_arguments() {
    let mut compilation = parse(
        "struct Wrap<T> { T value; } impl<T> Wrap<T> { Self make(T value) { return Self { value: move value }; } }
         Wrap<i32> f() { return Wrap::make(9); }",
    );
    let program = compilation.check_monomorphized();
    assert!(program.is_some(), "{:#?}", compilation.diagnostics);
    assert!(program.unwrap().instances.len() >= 2);
}

#[test]
fn inherent_and_trait_methods_resolve_to_real_function_bodies() {
    let (_, program) = typed(
        "struct Counter { i32 value; } trait Read { i32 read(&Self self); }
         impl Counter { void increment(&mut Self self) { self.value += 1; } }
         impl Read for Counter { i32 read(&Self self) { return self.value; } }
         i32 f() { Counter value = Counter { value: 4 }; value.increment(); return value.read(); }",
    );
    assert_eq!(program.traits.len(), 1);
    assert_eq!(program.implementations.len(), 2);
    assert!(
        program
            .implementations
            .iter()
            .flat_map(|implementation| &implementation.methods)
            .all(|method| program
                .functions
                .iter()
                .any(|body| body.definition == method.implementation))
    );
}

#[test]
fn generic_bound_calls_preserve_the_declared_trait_witness() {
    let (_, program) = typed(
        "trait Read { i32 read(&Self self); }
         struct Cell { i32 value; }
         impl Read for Cell { i32 read(&Self self) { return self.value; } }
         i32 read<T: Read>(&T value) { return value.read(); }
         i32 f() { Cell value = Cell { value: 6 }; return read(&value); }",
    );
    assert!(
        program
            .definitions
            .iter()
            .any(|definition| !definition.bounds.is_empty())
    );
    let declaration = program.traits[0].methods[0].definition;
    assert!(program.functions.iter().flat_map(|function| &function.expressions)
        .any(|expression| matches!(expression.kind, hir::ExprKind::Definition(definition) if definition == declaration)));
}

#[test]
fn missing_wrong_and_overlapping_implementations_are_rejected() {
    for source in [
        "trait Read { i32 read(&Self self); } struct Cell {} impl Read for Cell {}",
        "trait Read { i32 read(&Self self); } struct Cell {} impl Read for Cell { bool read(&Self self) { return true; } }",
        "trait Read { i32 read(&Self self); } struct Cell {} impl Read for Cell { i32 read(&Self self) { return 1; } } impl Read for Cell { i32 read(&Self self) { return 2; } }",
        "trait Read { i32 read(&Self self); } i32 f<T: Read>(&T value) { return value.read(); } i32 g() { i32 x = 1; return f(&x); }",
    ] {
        let mut compilation = parse(source);
        assert!(compilation.check_types().is_none(), "accepted {source}");
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.starts_with("E-IMPL")
                    || diagnostic.code.starts_with("E-TRAIT")),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn copy_bounds_derive_from_structure_and_never_override_a_destructor() {
    let (_, program) = typed(
        "@lang(copy) trait Copy {} T duplicate<T: Copy>(T value) { return value; }
         i32 f() { return duplicate(7); }",
    );
    assert_eq!(
        program.traits[0].language_item,
        Some(hir::traits::LanguageItem::Copy)
    );
    let mut compilation = parse(
        "@lang(copy) trait Copy {} @lang(drop) trait Drop { void drop(&mut Self self); }
         struct Owned {} impl Drop for Owned { void drop(&mut Self self) {} }
         impl Copy for Owned {}",
    );
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-COPY-IMPL")
    );
}

#[test]
fn callable_traits_select_real_closure_helpers() {
    let (_, program) = typed(
        "@lang(fn) trait Call<A, R> { R call(&Self self, A argument); }
         i32 apply<F: Call<i32, i32>>(F function) { return function(3); }
         i32 f() { auto closure = [](i32 value) -> i32 { return value + 1; }; return apply(closure); }",
    );
    assert_eq!(program.closures.len(), 1);
    assert!(
        program
            .definitions
            .iter()
            .any(|definition| !definition.bounds.is_empty())
    );
}

#[test]
fn explicit_language_roles_reject_wrong_shapes_and_duplicates() {
    for source in [
        "@lang(drop) trait Wrong { i32 drop(&Self self); }",
        "@lang(drop) trait A { void drop(&mut Self self); } @lang(drop) trait B { void drop(&mut Self self); }",
        "@lang(from) trait Wrong<T> { bool from(T value); }",
        "@lang(copy) trait Wrong { void grant(&Self self); }",
    ] {
        let mut compilation = parse(source);
        assert!(compilation.check_types().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E-LANG-ITEM"),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn cyclic_supertraits_do_not_become_evidence() {
    let mut compilation = parse("trait A: B {} trait B: A {}");
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-TRAIT-CYCLE")
    );
}

#[test]
fn default_methods_have_bodies_and_supertrait_obligations_are_checked() {
    let (_, program) = typed(
        "trait Base { i32 base(&Self self); }
         trait Derived: Base { i32 twice(&Self self) { return self.base() + self.base(); } }
         struct Value { i32 number; }
         impl Base for Value { i32 base(&Self self) { return self.number; } }
         impl Derived for Value {}
         i32 use<T: Derived>(&T value) { return value.base(); }
         i32 f() { Value value = Value { number: 4 }; return value.twice() + use(&value); }",
    );
    assert!(
        program
            .traits
            .iter()
            .flat_map(|trait_| &trait_.methods)
            .any(|method| method.has_default)
    );
    let mut invalid =
        parse("trait Base {} trait Derived: Base {} struct Value {} impl Derived for Value {}");
    assert!(invalid.check_types().is_none());
    assert!(
        invalid
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-TRAIT-SUPER")
    );
}

#[test]
fn generic_fnonce_calls_keep_the_explicit_move_boundary() {
    let (_, _) = typed(
        "@lang(fn_once) trait Once<A,R> { R call(move Self self, A argument); }
         i32 invoke<F: Once<i32,i32>>(F function) { return (move function)(3); }",
    );
    let mut invalid = parse(
        "@lang(fn_once) trait Once<A,R> { R call(move Self self, A argument); }
         i32 invoke<F: Once<i32,i32>>(F function) { return function(3); }",
    );
    assert!(invalid.check_types().is_none());
    assert!(
        invalid
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-MOVE-EXPLICIT")
    );
}

#[test]
fn coherence_distinguishes_trait_arguments_and_detects_two_sided_intersections() {
    let (_, program) = typed(
        "trait Convert<T> { T convert(&Self self); } struct Value {}
         impl Convert<i32> for Value { i32 convert(&Self self) { return 1; } }
         impl Convert<u32> for Value { u32 convert(&Self self) { return 1; } }",
    );
    assert_eq!(program.implementations.len(), 2);
    let mut invalid = parse(
        "trait Mark {} struct Pair<A,B> { A first; B second; }
         impl<T> Mark for Pair<T,i32> {} impl<U> Mark for Pair<u32,U> {}",
    );
    assert!(invalid.check_types().is_none());
    assert!(
        invalid
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-IMPL-OVERLAP")
    );
}
