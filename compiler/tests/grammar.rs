use cavo_compiler::{Compilation, syntax};
use std::collections::BTreeSet;

fn parsed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("grammar.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) {
    let mut compilation = parsed(source);
    assert!(
        compilation.check_mir().is_some(),
        "{source}\n{:#?}",
        compilation.diagnostics
    );
}

const CELL: &str = r#"
struct Cell<T> { T value; }
impl<T> Cell<T> {
    Self new(T value) { return Self { value: move value }; }
    U choose<U>(T first, U second) { return move second; }
}
"#;

#[test]
fn generic_nominal_owner_and_method_arguments_are_distinct() {
    checked(&format!(
        "{CELL} i32 main() {{ auto value = Cell::<i32>::new(7); return value.value; }}"
    ));
    checked(&format!(
        "{CELL} u64 main() {{ return Cell::<i32>::choose::<u64>(1, 7); }}"
    ));
    checked(&format!(
        "{CELL} type Alias<T> = Cell<T>; i32 main() {{ auto value = Alias::<i32>::new(7); return value.value; }}"
    ));
    checked(&format!(
        "{CELL} i32 main() {{ Cell<i32> value = Cell::new(7); return value.value; }}"
    ));
    let mut compilation = parsed(&format!(
        "{CELL} Cell<u64> bad() {{ return Cell::<i32>::new(7); }}"
    ));
    assert!(
        compilation.check_mir().is_none(),
        "explicit i32 owner was replaced by the result hint"
    );
}

#[test]
fn generic_constructor_paths_preserve_const_arguments_and_enum_variants() {
    checked(
        "struct Buffer<const usize N> {} impl<const usize N> Buffer<N> { usize capacity() { return N; } } usize main() { return Buffer::<4>::capacity(); }",
    );
    checked(
        "enum Choice<T> { Some(T), None } i32 main() { auto value = Choice::<i32>::Some(7); return match (move value) { Choice::Some(n) => n, Choice::None => 0 }; }",
    );
    checked(
        "enum Choice<T> { Some(T), None } i32 main() { auto value = Choice::<i32>::None; return match value { Choice::Some(n) => n, Choice::None => 0 }; }",
    );
}

#[test]
fn qualified_generic_constructor_paths_resolve_the_owner_module() {
    let mut compilation = Compilation::default();
    for (path, source) in [
        (
            "cell.cavo",
            "module util::cell; pub struct Cell<T> { T value; } impl<T> Cell<T> { pub Self new(T value) { return Self { value: move value }; } }",
        ),
        (
            "app.cavo",
            "module util::app; import util::cell; i32 main() { auto value = cell::Cell::<i32>::new(7); return 0; }",
        ),
    ] {
        let file = compilation.sources.add(path, source.into()).unwrap();
        compilation.parse(file);
    }
    assert!(
        compilation.check_mir().is_some(),
        "{:#?}",
        compilation.diagnostics
    );
}

// Each frozen production has a source example through the actual lexer/parser.
// This is a compatibility corpus, not a proof that two grammar formalisms agree.
const PRODUCTIONS: &[(&[&str], &str)] = &[
    (
        &["module", "import", "path"],
        "module app::main; i32 f(); import app::other;",
    ),
    (
        &[
            "item",
            "visibility",
            "declaration",
            "attribute",
            "attribute-token",
        ],
        "@custom(one, [two], {three}) pub(package) struct S {};",
    ),
    (
        &["record", "field", "type", "identifier"],
        "struct S<T> { pub T value; &mut i32 view; i32[4] data; } union U { i32 value; };",
    ),
    (
        &["enumeration", "variants", "variant", "types"],
        "enum E { Empty, Tuple(i32, bool,), Named { i32 value; }, Tag = 4 };",
    ),
    (
        &["alias", "callable", "lifetime", "bounds"],
        "type F = for<'a> fn(&'a i32, dyn Trait + Send) -> i32 @nosuspend;",
    ),
    (
        &["trait", "generics", "generic"],
        "trait Trait<T: Other, const usize N, 'a>: Parent { void f(Self self); }",
    ),
    (
        &["implementation"],
        "impl<T> !Send for S<T> {} contract impl Send for Owner because \"reviewed\";",
    ),
    (
        &["function", "parameters", "parameter", "clause"],
        "const i32 f(move i32 n, ...) requires n > 0 ensures result > 0 { return n; }",
    ),
    (
        &[
            "contract-declaration",
            "generic-arguments",
            "generic-argument",
        ],
        "contract Valid<T>(ptr<T> p) { requires Readable<T>(p, 1); }",
    ),
    (&["extern-block"], "extern \"C\" { i32 f(i32 n); }"),
    (
        &["block", "statement", "variable", "if-statement"],
        "void f() { const i32 n = 1; { ; } if (n > 0) {} else if (n < 0) {} else {} while (false) { break; } scope named { defer {} contract {} } assume true because \"reviewed\"; return; }",
    ),
    (
        &["assignment", "assign-op", "for-statement"],
        "void f() { i32 x = 1; x += 1; for (i32 i = 0; i < 2; i += 1) { continue; } for (auto n in data) { x = n; } }",
    ),
    (
        &["static-assert"],
        "static_assert(1 + 1 == 2, \"arithmetic\");",
    ),
    (
        &[
            "expression",
            "prefix",
            "unary-op",
            "binary-op",
            "postfix",
            "arguments",
        ],
        "void f() { auto v = move *(&mut x); bool b = !false && true || false; i32 n = ((1 + 2) * 3 << 1) & 7 | 2 ^ 1; auto a = Cell::<i32>::new(0); auto r = identity::<i32>(a.value[0])?; scope { auto task = spawn work(); } }",
    ),
    (
        &["record-value", "array"],
        "void f() { auto s = S { value: 1 }; auto a = [1, 2,]; auto b = [0; 4]; auto empty = []; }",
    ),
    (
        &["closure", "capture"],
        "void f() { auto c = [move x, &y, &mut z](i32 n) -> i32 { return n; }; }",
    ),
    (
        &["match", "arm", "pattern"],
        "i32 f(E e) { return match e { E::Some(n) if n > 0 => n, E::None => 0, _ => 1 }; }",
    ),
    (
        &["literal", "integer", "floating", "string", "character"],
        "void f() { i32 a = 0xff; f64 b = 1.25e2; auto s = \"line\\n\"; char c = 'x'; bool yes = true; ptr<i32> p = null; }",
    ),
];

#[test]
fn every_frozen_production_has_a_parser_conformance_example() {
    assert_eq!(syntax::GRAMMAR_VERSION, "cavo-0.1");
    let mut covered = BTreeSet::new();
    for &(productions, source) in PRODUCTIONS {
        let compilation = parsed(source);
        assert!(
            compilation.diagnostics.is_empty(),
            "{productions:?}\n{:#?}",
            compilation.diagnostics
        );
        covered.extend(productions.iter().copied());
    }
    for line in syntax::GRAMMAR.lines() {
        if let Some((name, _)) = line.split_once(" = ") {
            assert!(covered.contains(name), "missing parser fixture for {name}");
        }
    }
}

#[test]
fn excluded_extensions_and_rust_style_const_parameters_are_not_silently_parsed() {
    for source in [
        "struct S<const N: usize> {}",
        "void f() { match n { 1 | 2 => 3 }; }",
        "void f() { match n { 1..4 => 3 }; }",
        "void f() { match n { S { field } => field }; }",
        "void f() { asm volatile { \"nop\" }; }",
        "void f() { value |> next; }",
    ] {
        assert!(
            !parsed(source).diagnostics.is_empty(),
            "unexpected extension: {source}"
        );
    }
}
