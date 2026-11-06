use cavo_compiler::{Compilation, hir};

const CORE: &str = "@lang(copy) trait Copy {}";
fn check(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("copy.cavo", format!("{CORE}\n{source}"))
        .unwrap();
    compilation.parse(file);
    compilation.check();
    compilation
}
fn accepted(source: &str) {
    let compilation = check(source);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
}
fn rejected(source: &str, code: &str) -> Compilation {
    let compilation = check(source);
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "{:#?}",
        compilation.diagnostics
    );
    compilation
}

#[test]
fn nominal_values_need_explicit_copy_permission() {
    let body = "struct Token { u64 id; } void take(Token t) {} void f() { Token token = Token { id: 1 }; take(token); take(token); }";
    rejected(body, "E-MOVE-EXPLICIT");
    accepted(&format!("impl Copy for Token {{}} {body}"));
    rejected(
        "struct Lease { ptr<u32> address; } void f(ptr<u32> p) { Lease first = Lease { address: p }; Lease second = first; }",
        "E-MOVE-EXPLICIT",
    );
}

#[test]
fn copy_qualification_checks_fields_instead_of_selecting_its_own_impl() {
    let compilation = rejected(
        "struct Unique<'a> { &'a mut i32 value; } impl<'a> Copy for Unique<'a> {}",
        "E-COPY-IMPL",
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .filter(|d| d.code == "E-COPY-IMPL")
            .any(|d| !d.labels.is_empty())
    );
    rejected(
        "@lang(drop) trait Drop { void drop(&mut Self self); } struct Owner {} impl Drop for Owner { void drop(&mut Self self) {} } impl Copy for Owner {}",
        "E-COPY-IMPL",
    );
    let compilation = rejected(
        "@lang(drop) trait Drop { void drop(&mut Self self); } struct Owner {} impl Drop for Owner { void drop(&mut Self self) {} } struct Outer { Owner inner; } impl Copy for Outer {}",
        "E-COPY-IMPL",
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .filter(|d| d.code == "E-COPY-IMPL")
            .any(|d| !d.labels.is_empty())
    );
}

#[test]
fn conditional_copy_bounds_use_the_normal_trait_obligation_engine() {
    accepted(
        "struct Buffer {} struct Pair<T> { T first; T second; } impl<T: Copy> Copy for Pair<T> {} Pair<i32> duplicate(Pair<i32> value) { auto other = value; return other; } Pair<Buffer> transfer(Pair<Buffer> value) { return move value; }",
    );
    rejected(
        "struct Pair<T> { T first; T second; } impl<T> Copy for Pair<T> {}",
        "E-COPY-IMPL",
    );
    rejected(
        "struct Buffer {} struct Pair<T> { T first; T second; } impl<T: Copy> Copy for Pair<T> {} Pair<Buffer> duplicate(Pair<Buffer> value) { return value; }",
        "E-MOVE-EXPLICIT",
    );
}

#[test]
fn copy_bounds_can_depend_on_structural_send_without_query_recursion() {
    accepted(
        "@lang(send) trait Send {} struct Pair<T> { T value; } impl<T: Copy + Send> Copy for Pair<T> {} Pair<i32> f(Pair<i32> value) { auto second = value; return second; }",
    );
}

#[test]
fn repetition_requires_copy_even_for_destructor_free_nominals() {
    rejected(
        "struct Point { i32 x; } void f() { Point point = Point { x: 1 }; Point[4] points = [point; 4]; }",
        "E-COPY-REPEAT",
    );
    accepted(
        "struct Point { i32 x; } impl Copy for Point {} void f() { Point point = Point { x: 1 }; Point[4] points = [point; 4]; }",
    );
}

#[test]
fn discriminant_and_copy_payload_matches_do_not_consume_the_subject() {
    accepted(
        "enum Tag { First, Second } i32 f() { Tag tag = Tag::First; i32 a = match tag { Tag::First => 1, Tag::Second => 2 }; i32 b = match tag { Tag::First => 3, Tag::Second => 4 }; return a + b; }",
    );
    accepted(
        "enum Envelope { Some(i32), None } i32 f() { Envelope value = Envelope::Some(4); i32 a = match value { Envelope::Some(n) => n, Envelope::None => 0 }; i32 b = match value { Envelope::Some(n) => n, Envelope::None => 0 }; return a + b; }",
    );
}

#[test]
fn consuming_a_noncopy_payload_requires_explicit_move() {
    let prelude = "struct Owner {} enum Outcome { Ready(Owner), Empty }";
    rejected(
        &format!(
            "{prelude} void f(Outcome value) {{ match value {{ Outcome::Ready(owner) => {{}}, Outcome::Empty => {{}} }}; }}"
        ),
        "E-MATCH-MOVE",
    );
    accepted(&format!(
        "{prelude} void f(Outcome value) {{ match (move value) {{ Outcome::Ready(owner) => {{}}, Outcome::Empty => {{}} }}; }}"
    ));
}

#[test]
fn checking_a_copy_trait_and_copy_permission_agree() {
    let mut compilation = Compilation::default();
    let file=compilation.sources.add("copy.cavo",format!("{CORE} struct Yes {{ i32 value; }} impl Copy for Yes {{}} struct No {{ i32 value; }}")).unwrap();
    compilation.parse(file);
    let mut program = compilation.check_types().unwrap();
    let copy = program
        .traits
        .iter()
        .find(|item| item.language_item == Some(hir::traits::LanguageItem::Copy))
        .unwrap()
        .definition;
    for (name, expected) in [("Yes", true), ("No", false)] {
        let ty = program
            .definitions
            .iter()
            .find(|d| compilation.symbols.get(d.name) == name)
            .unwrap()
            .ty;
        assert_eq!(hir::traits::is_copy(&mut program, ty), expected);
        assert_eq!(
            hir::traits::require_trait(
                &mut program,
                ty,
                &hir::traits::TraitRef {
                    definition: copy,
                    arguments: vec![]
                }
            )
            .is_ok(),
            expected
        );
    }
}

#[test]
fn move_help_suggests_copy_only_for_an_eligible_local_type() {
    let compilation = rejected(
        "struct Token { u64 id; } Token f(Token value) { return value; }",
        "E-MOVE-EXPLICIT",
    );
    assert!(compilation.diagnostics.iter().any(|d| {
        d.helps
            .iter()
            .any(|help| help.contains("impl Copy for Token {}"))
    }));
    let compilation = rejected(
        "struct Unique<'a> { &'a mut i32 value; } Unique<'a> f<'a>(Unique<'a> value) { return value; }",
        "E-MOVE-EXPLICIT",
    );
    assert!(!compilation.diagnostics.iter().any(|d| {
        d.helps
            .iter()
            .any(|help| help.contains("explicit `Copy` impl"))
    }));
}

#[test]
fn union_storage_checks_its_fields_without_granting_copy_to_the_union() {
    accepted(
        "union Bits { u32 number; bool bit; } bool f() { contract { Bits first = Bits { number: 7 }; first.bit = true; return first.bit; } }",
    );
    rejected(
        "union Bits { u32 number; bool bit; } void f() { contract { Bits first = Bits { number: 7 }; Bits second = first; } }",
        "E-MOVE-EXPLICIT",
    );
    accepted(
        "union Bits { u32 number; bool bit; } impl Copy for Bits {} void f() { contract { Bits first = Bits { number: 7 }; Bits second = first; } }",
    );
}

#[test]
fn copy_impls_and_their_bounds_are_explicit_interface_identities() {
    use cavo_compiler::external::interface;
    fn identity(
        implementation: &str,
        parameter: &str,
    ) -> (cavo_compiler::external::Digest, String) {
        let mut compilation = Compilation::default();
        let text = format!(
            "{CORE} struct Pair<{parameter}> {{ {parameter} value; }} {implementation} void api(Pair<i32> value);"
        );
        let file = compilation.sources.add("api.cavo", text).unwrap();
        compilation.parse(file);
        let program = compilation
            .check_types()
            .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
        let functions =
            interface::interfaces(&program, &compilation.symbols, &compilation.sources).unwrap();
        let permissions =
            interface::copy_permissions(&program, &compilation.symbols, &compilation.sources)
                .unwrap();
        (
            functions[0].signature,
            interface::render_with_copy(&functions, &permissions),
        )
    }
    let (none, _) = identity("", "T");
    let (copy, report) = identity("impl<T: Copy> Copy for Pair<T> {}", "T");
    assert_ne!(none, copy);
    assert!(report.contains("copy_permissions") && report.contains("explicit_impls"));
    assert_eq!(copy, identity("impl<U: Copy> Copy for Pair<U> {}", "U").0);
}

#[test]
fn opaque_task_handles_cannot_gain_copy_even_when_their_record_is_empty() {
    rejected(
        "@lang(task) struct Work<'scope, T> {} impl<'scope, T> Copy for Work<'scope, T> {}",
        "E-COPY-IMPL",
    );
}
