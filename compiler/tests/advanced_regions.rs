use cavo_compiler::{
    Compilation, hir,
    local::{RegionStep, Verdict},
};

fn check(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut c = Compilation::default();
    let file = c.sources.add("advanced.cavo", source.into()).unwrap();
    c.parse(file);
    let program = c.check();
    (c, program)
}
fn passes(source: &str) -> (Compilation, hir::Program) {
    let (c, p) = check(source);
    assert!(c.diagnostics.is_empty(), "{source}\n{:#?}", c.diagnostics);
    let p = p.unwrap();
    c.local_analysis.as_ref().unwrap().validate(&p).unwrap();
    assert_eq!(
        c.local_analysis.as_ref().unwrap().verdict,
        Verdict::Undetermined
    );
    (c, p)
}
fn fails(source: &str, code: &str) {
    let (c, p) = check(source);
    assert!(p.is_none(), "unexpected approval: {source}");
    assert!(
        c.diagnostics.iter().any(|d| d.code == code),
        "expected {code}: {:#?}",
        c.diagnostics
    );
}

#[test]
fn nested_input_reads_keep_separate_lifetime_origins() {
    let (c, _) = passes(
        "&'b i32 inner<'a,'b>(&'a &'b i32 input) { return *input; } i32 f() { i32 x = 1; auto r = &x; auto result = inner(&r); return *result; }",
    );
    assert!(
        c.local_analysis.unwrap().regions[0]
            .inputs
            .iter()
            .any(|i| i.path == [RegionStep::Deref])
    );
    fails(
        "&'static i32 bad<'a,'b>(&'a &'b i32 input) { return *input; }",
        "E-REGION-RETURN",
    );
}

#[test]
fn nested_type_well_formedness_implies_outlives() {
    passes("&'a i32 shorter<'a,'b>(&'a &'b i32 input) { return *input; }");
    fails(
        "&'b i32 longer<'a,'b>(&'a &'b i32 input) { i32 local = 1; return &local; }",
        "E-BORROW-RETURN",
    );
}

#[test]
fn mutable_nested_lifetimes_are_invariant() {
    fails(
        "&'a mut &i32 view<'a>(&'a mut &'static i32 input) { return move input; } void f(&'static i32 input) { &'static i32 slot=input; auto reference=view(&mut slot); i32 local=1; *reference=&local; }",
        "E-REGION-STORE",
    );
    passes("&'a mut &'b i32 id<'a,'b>(&'a mut &'b i32 input) { return move input; }");
    fails(
        "&'a mut &'a i32 weaken<'a,'b>(&'a mut &'b i32 input) { return move input; }",
        "E-REGION-INVARIANT",
    );
}

#[test]
fn higher_ranked_callbacks_are_fresh_for_each_call() {
    passes(
        "&i32 id(&i32 x) { return x; } i32 run(fn(&i32) -> &i32 cb) { i32 x=1; return *cb(&x); } i32 f() { return run(id); }",
    );
    passes(
        "&'a i32 id<'a>(&'a i32 x) { return x; } i32 run(for<'r> fn(&'r i32) -> &'r i32 callback) { i32 x = 1; auto a = callback(&x); i32 y = 2; auto b = callback(&y); return *a + *b; } i32 f() { return run(id); }",
    );
    passes(
        "&i32 id(&i32 x) { return x; } i32 f() { auto callback = id; i32 x = 1; auto result = callback(&x); return *result; }",
    );
}

#[test]
fn a_static_only_callback_is_not_universally_callable() {
    fails(
        "&'static i32 static_only(&'static i32 x) { return x; } void run(for<'a> fn(&'a i32) -> &'a i32 callback) {} void f() { run(static_only); }",
        "E-TYPE-MISMATCH",
    );
    passes(
        "&'static str constant(&str x) { return \"ok\"; } void run(for<'a> fn(&'a str) -> &'a str callback) {} void f() { run(constant); }",
    );
}

#[test]
fn external_function_values_cannot_masquerade_as_managed_callbacks() {
    fails(
        "extern \"C\" { i32 native(i32 x); } void run(fn(i32) -> i32 callback) {} void f() { run(native); }",
        "E-FRONTEND-STAGE",
    );
}

#[test]
fn nested_binders_shadow_names_without_capturing_or_leaking_regions() {
    fails(
        "void f(for<'a> fn(Bad) -> i32 cb) {} type Bad = &'a i32;",
        "E-REGION-NAME",
    );
    passes(
        "void f(for<'a> fn(Callback) -> i32 cb) {} type Callback = for<'a> fn(&'a i32) -> &'a i32;",
    );
    passes(
        "type Callback = for<'a> fn(&'a i32) -> &'a i32; &'a i32 id<'a>(&'a i32 x) { return x; } i32 f() { Callback cb = id; i32 x=1; return *cb(&x); }",
    );
    passes(
        "void same(for<'a> fn(for<'a> fn(&'a i32) -> &'a i32) -> i32 cb) { for<'b> fn(for<'c> fn(&'c i32) -> &'c i32) -> i32 copy = cb; }",
    );
    fails(
        "void bad(for<'a> fn(&'a i32) -> &'a i32 cb) { &'a i32 escaped; }",
        "E-REGION-NAME",
    );
    fails(
        "void bad(for<'a,'a> fn(&'a i32) -> &'a i32 cb) {}",
        "E-REGION-NAME",
    );
    fails("void bad(for<'static> fn() -> i32 cb) {}", "E-REGION-NAME");
    fails("void bad(for<T> fn(T) -> T cb) {}", "E-PARSE-REGION");
}

#[test]
fn indirect_elided_regions_are_shared_within_a_call_and_fresh_between_calls() {
    use cavo_compiler::types::Ty;
    let (_, p) = passes(
        "i32 f(fn(&i32) -> &i32 cb) { i32 x=1; auto a=cb(&x); i32 y=2; auto b=cb(&y); return *a + *b; }",
    );
    let mut regions = Vec::new();
    for e in &p.functions[0].expressions {
        if let hir::ExprKind::Call {
            parameter_types, ..
        } = &e.kind
        {
            let Ty::Reference { region: input, .. } = *p.types.get(parameter_types[0]) else {
                panic!()
            };
            let Ty::Reference { region: result, .. } = *p.types.get(e.ty) else {
                panic!()
            };
            assert_eq!(input, result);
            regions.push(result);
        }
    }
    assert_eq!(regions.len(), 2);
    assert_ne!(regions[0], regions[1]);
}

#[test]
fn higher_ranked_result_lifetimes_cannot_be_strengthened_or_unified_incorrectly() {
    fails(
        "&'a i32 id<'a>(&'a i32 x) { return x; } void need(for<'a> fn(&'a i32) -> &'static i32 cb) {} void f() { need(id); }",
        "E-TYPE-MISMATCH",
    );
    fails(
        "&'a i32 first<'a>(&'a i32 x, &'a i32 y) { return x; } void need(for<'a,'b> fn(&'a i32,&'b i32) -> &'a i32 cb) {} void f() { need(first); }",
        "E-TYPE-MISMATCH",
    );
    // An outer existential cannot be chosen from a nested universal universe.
    fails(
        "void f<'x>(for<'a> fn(for<'b> fn(&'a i32) -> i32) -> i32 actual) { for<'c> fn(for<'d> fn(&'d i32) -> i32) -> i32 invalid = actual; }",
        "E-TYPE-MISMATCH",
    );
}

#[test]
fn frozen_capabilities_cannot_be_hidden_behind_multiple_references() {
    fails(
        "void use(& &mut i32 parent, &mut i32 child) {} void f() { i32 x=1; auto p=&mut x; auto c=&mut *p; use(&p,move c); }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "void use(& & &mut i32 parent, &mut i32 child) {} void f() { i32 x=1; auto p=&mut x; auto outer=&p; auto c=&mut *p; use(&outer,move c); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn nested_input_records_and_reference_stores_preserve_lifetimes() {
    passes(
        "struct Holder<T> { T value; } &'b i32 read<'a,'b>(&'a Holder<&'b i32> holder) { return holder.value; } i32 f<'b>(Holder<&'b i32> h) { return *read(&h); }",
    );
    passes("void replace<'a>(&mut &'a i32 slot, &'a i32 value) { *slot=value; }");
    passes("i32 read(&mut &mut i32 slot) { **slot=2; return **slot; }");
}

#[test]
fn bound_region_scope_is_checked_at_hir_boundaries() {
    use cavo_compiler::types::{Region, Ty};
    let (_, mut p) = passes("void f(for<'a> fn(&'a i32) -> &'a i32 cb) {}");
    let inner = p.types.builtin("i32").unwrap();
    let escaping = p.types.intern(Ty::Reference {
        region: Region::Bound { depth: 0, index: 0 },
        mutable: false,
        inner,
    });
    p.functions[0].locals[0].ty = escaping;
    assert!(p.validate().is_err());
}
