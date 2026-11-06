use cavo_compiler::Compilation;

fn check(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("modular.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation.check_mir();
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

fn rejected(source: &str, code: &str) {
    let compilation = check(source);
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn public_reference_stores_are_declared_and_implementation_checked() {
    let header = "@effects(reads(value), writes(slot.*), normal(slot.* = value)) pub void set<'a>(&mut &'a i32 slot, &'a i32 value)";
    accepted(&format!(
        "{header} {{ *slot = value; }} void use() {{ i32 a = 1; i32 b = 2; auto r = &a; set(&mut r, &b); a = 3; }}"
    ));
    rejected(&format!("{header} {{ }}"), "E-EFFECT-REFINE");
}

#[test]
fn omitted_frames_are_conservative_and_never_inferred_from_public_bodies() {
    for body in [
        "",
        "auto temporary = *left; *left = *right; *right = temporary;",
    ] {
        rejected(
            &format!(
                "pub void exchange<'a>(&mut &'a i32 left, &mut &'a i32 right) {{ {body} }} void use() {{ i32 a = 1; i32 b = 2; auto x = &a; auto y = &b; exchange(&mut x, &mut y); a = 3; i32 n = *y; }}"
            ),
            "E-MIR-BORROW",
        );
    }
}

#[test]
fn effect_promises_are_checked_independently_of_call_site_use() {
    accepted("@effects(bounded, pure) pub i32 identity(i32 value) { return value; }");
    rejected(
        "void opaque(); @effects(noalloc) pub void f() { opaque(); }",
        "E-EFFECT-BOUND",
    );
    rejected("@effects(bounded) pub void f() { f(); }", "E-EFFECT-BOUND");
    rejected(
        "@effects(no_callback) pub void f(fn() -> void callback) { callback(); }",
        "E-EFFECT-REFINE",
    );
}

#[test]
fn checked_capsules_hide_runtime_bodies_and_reject_tampering() {
    use cavo_compiler::modular::capsule::{self, Module, Source};
    let make = |body: &str| {
        capsule::build(vec![Source {
            name: "math.cavo".into(),
            text: format!("module math; @effects(bounded, pure) pub i32 value() {{ {body} }}"),
        }])
        .unwrap()
    };
    let first = make("return 1;");
    let second = make("return 2;");
    assert_eq!(first.interface(), second.interface());
    assert_ne!(first.implementation(), second.implementation());
    let text = first.encode();
    let module = Module::decode(&text).unwrap();
    let mut compilation = Compilation::default();
    module.load_into(&mut compilation).unwrap();
    let file = compilation
        .sources
        .add(
            "main.cavo",
            "import math; i32 main() { return math::value(); }".into(),
        )
        .unwrap();
    compilation.parse(file);
    let (hir, _) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    assert!(
        !hir.functions
            .iter()
            .any(|f| { compilation.symbols.get(hir.definitions[f.definition].name) == "value" })
    );
    assert!(Module::decode(&text.replace("return 1", "return 3")).is_err());
    let rejected = vec![Source {
        name: "bad.cavo".into(),
        text: "@effects(bounded) pub void f() { f(); }".into(),
    }];
    assert!(capsule::build(rejected).is_err());
}

#[test]
fn loading_a_module_does_not_certify_its_unresolved_prototypes() {
    use cavo_compiler::modular::capsule::{self, Source};
    let module = capsule::build(vec![Source {
        name: "decl.cavo".into(),
        text: "module decl; @effects(pure) pub void unavailable();".into(),
    }])
    .unwrap();
    let mut compilation = Compilation::default();
    module.load_into(&mut compilation).unwrap();
    let file = compilation
        .sources
        .add(
            "caller.cavo",
            "import decl; @effects(pure) void f() { decl::unavailable(); }".into(),
        )
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-EFFECT-BOUND")
    );
    let opaque = vec![Source {
        name: "opaque.cavo".into(),
        text: "extern \"C\" { i32 external(); } pub i32 wrapper() { return external(); }".into(),
    }];
    assert!(
        capsule::build(opaque)
            .unwrap_err()
            .contains("E-MODULE-COVERAGE")
    );
}

#[test]
fn trait_preconditions_cannot_be_strengthened_and_postconditions_cannot_disappear() {
    rejected(
        "trait T { i32 f(&Self self, i32 value); } struct S {} impl T for S { i32 f(&Self self, i32 value) requires value > 0 { return value; } }",
        "E-CONTRACT-REFINE",
    );
    rejected(
        "trait T { i32 f(&Self self, i32 value) ensures result > 0; } struct S {} impl T for S { i32 f(&Self self, i32 value) { return value; } }",
        "E-CONTRACT-REFINE",
    );
    accepted(
        "trait T { i32 f(&Self self, i32 value) requires value > 0 ensures result > 0; } struct S {} impl T for S { i32 f(&Self self, i32 n) requires n > 0 ensures result > 0 { return n; } }",
    );
}

#[test]
fn trait_callers_keep_declared_requirements_when_a_body_weakens_them() {
    let mut compilation = check(
        "@lang(readable) contract Readable<T>(ptr<const T> p, usize n) {} trait T { void f(&Self self, ptr<const i32> p) requires Readable::<i32>(p, 1); } struct S {} impl T for S { void f(&Self self, ptr<const i32> p) {} } void caller(ptr<const i32> p) { S value = S {}; value.f(p); }",
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-CONTRACT-003"),
        "{:#?}",
        compilation.diagnostics
    );
    compilation.diagnostics.clear();
}

#[test]
fn checked_module_premises_remain_assumptions_in_callers() {
    use cavo_compiler::{
        contracts::Assessment,
        modular::capsule::{self, Source},
    };
    let source = "module lib; @lang(readable) contract Readable<T>(ptr<const T> p, usize n) {} @intrinsic(ptr_read) i32 raw_read(ptr<const i32> p); @effects(pure) pub i32 load(ptr<const i32> p) { contract { assume Readable::<i32>(p, 1) because \"foreign owner lease\"; return raw_read(p); } }";
    let module = capsule::build(vec![Source {
        name: "lib.cavo".into(),
        text: source.into(),
    }])
    .unwrap();
    let mut compilation = Compilation::default();
    module.load_into(&mut compilation).unwrap();
    let file = compilation.sources.add("caller.cavo", "import lib; @intrinsic(as_ptr) ptr<const i32> address(&i32 n); @intrinsic(ptr_read) i32 read_value(ptr<const i32> p); i32 main(ptr<const i32> p) { i32 n = lib::load(p); contract { return read_value(address(&n)); } }".into()).unwrap();
    compilation.parse(file);
    compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let report = &compilation.mir_analysis.as_ref().unwrap().contracts;
    assert!(
        report
            .obligations
            .iter()
            .flat_map(|o| &o.components)
            .any(|c| matches!(c.assessment, Assessment::Assumed(_)))
    );
    assert!(report.json(&compilation.sources).contains("module_premise"));
}

#[test]
fn hiding_a_body_preserves_the_trust_of_its_worker_frame() {
    use cavo_compiler::{
        contracts::Trust,
        modular::capsule::{self, Source},
    };
    let module = capsule::build(vec![Source {
        name: "owner.cavo".into(),
        text: "@lang(send) trait Send {} struct Owner { ptr<i32> p; } contract impl Send for Owner because \"allocation follows its owner\"; pub Owner identity(Owner value) { return move value; }".into(),
    }]).unwrap();
    let mut compilation = Compilation::default();
    module.load_into(&mut compilation).unwrap();
    let program = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    assert!(program.modular.assumptions.values().flatten().any(|trust|
        matches!(trust, Trust::Module { reason, .. } if reason.as_ref() == "allocation follows its owner")));
}
