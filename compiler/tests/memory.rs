use cavo_compiler::{
    Compilation, hir,
    local::{MemoryLoan, MemoryOrigin, Verdict},
};

fn check(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut c = Compilation::default();
    let file = c.sources.add("memory.cavo", source.into()).unwrap();
    c.parse(file);
    let p = c.check();
    (c, p)
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
fn fails(source: &str, code: &str) -> Compilation {
    let (c, p) = check(source);
    assert!(p.is_none(), "unexpected approval: {source}");
    assert!(
        c.diagnostics.iter().any(|d| d.code == code),
        "{source}\nexpected {code}: {:#?}",
        c.diagnostics
    );
    c
}

const SET: &str = "void replace<'a>(&mut &'a i32 slot, &'a i32 value) { *slot=value; }";

#[test]
fn reference_stores_replace_the_callers_origin_and_release_the_old_loan() {
    let (c, _) = passes(&format!(
        "{SET} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; replace(&mut slot,&fresh); old=3; return *slot; }}"
    ));
    let r = c.local_analysis.unwrap();
    let effect = r.functions[0].memory.as_ref().unwrap();
    assert!(effect.normal_return);
    assert_eq!(effect.writes.len(), 1);
    assert!(effect.writes[0].definite);
    assert!(matches!(
        effect.writes[0].value.origins[0],
        MemoryOrigin::Reference {
            loan: MemoryLoan::Input(2),
            ..
        }
    ));
    fails(
        &format!(
            "{SET} i32 f() {{ i32 old=1; auto slot=&old; {{ i32 fresh=2; replace(&mut slot,&fresh); }} return *slot; }}"
        ),
        "E-BORROW-LIFETIME",
    );
}

#[test]
fn input_memory_cannot_retain_a_local_or_an_unrelated_lifetime() {
    fails(
        "void bad<'a>(&mut &'a i32 slot) { i32 local=1; *slot=&local; }",
        "E-REGION-STORE",
    );
    fails(
        "void bad<'a,'b>(&mut &'a i32 slot, &'b i32 value) { *slot=value; }",
        "E-REGION-STORE",
    );
    fails(
        &format!(
            "{SET} void f(&'static i32 input) {{ &'static i32 slot=input; i32 local=1; replace(&mut slot,&local); }}"
        ),
        "E-REGION-STORE",
    );
}

#[test]
fn caller_keeps_new_origins_and_conditional_stores_keep_old_origins() {
    let setter =
        "void maybe<'a>(&mut &'a i32 slot, &'a i32 value, bool c) { if(c) { *slot=value; } }";
    fails(
        &format!(
            "{setter} i32 f(bool c) {{ i32 old=1; i32 fresh=2; auto slot=&old; maybe(&mut slot,&fresh,c); old=3; return *slot; }}"
        ),
        "E-BORROW-CONFLICT",
    );
    fails(
        &format!(
            "{SET} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; replace(&mut slot,&fresh); fresh=3; return *slot; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn return_before_a_store_uses_the_entry_snapshot() {
    let source = "&'a i32 swap<'a>(&mut &'a i32 slot, &'a i32 value) { auto old=*slot; *slot=value; return old; }";
    passes(&format!(
        "{source} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; auto previous=swap(&mut slot,&fresh); return *previous+*slot; }}"
    ));
    fails(
        &format!(
            "{source} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; auto previous=swap(&mut slot,&fresh); old=3; return *previous; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn forwarded_and_recursive_effects_reach_a_fixed_point() {
    passes(&format!(
        "void outer<'a>(&mut &'a i32 slot,&'a i32 value) {{ replace(move slot,value); }} {SET} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; outer(&mut slot,&fresh); old=3; return *slot; }}"
    ));
    let recursive = "void update<'a>(&mut &'a i32 slot,&'a i32 value,bool again) { if(again) { update(move slot,value,false); return; } *slot=value; }";
    passes(&format!(
        "{recursive} i32 f(bool c) {{ i32 old=1; i32 fresh=2; auto slot=&old; update(&mut slot,&fresh,c); old=3; return *slot; }}"
    ));
}

#[test]
fn a_reborrow_returned_through_nested_input_freezes_its_original_parent() {
    let helper = "&'a i32 shared<'a>(& &'a mut i32 slot) { return &**slot; }";
    fails(
        &format!(
            "{helper} i32 f() {{ i32 x=1; auto parent=&mut x; auto child=shared(&parent); *parent=2; return *child; }}"
        ),
        "E-BORROW-CONFLICT",
    );
    passes(&format!(
        "{helper} i32 f() {{ i32 x=1; auto parent=&mut x; auto child=shared(&parent); i32 observed=*child; *parent=2; return observed; }}"
    ));
}

#[test]
fn record_fields_and_whole_records_keep_their_payload_shapes() {
    passes(
        "struct Holder<T> { T view; i32 tag; } void set<'a>(&mut Holder<&'a i32> h,&'a i32 value) { h.view=value; } i32 f<'a>(Holder<&'a i32> h,&'a i32 value) { set(&mut h,value); h.tag=3; return *h.view; }",
    );
    passes(
        "struct Holder<T> { T view; i32 tag; } void set<'a>(&mut Holder<&'a i32> h,Holder<&'a i32> value) { *h=value; } i32 f<'a>(Holder<&'a i32> h,Holder<&'a i32> value) { set(&mut h,value); return *h.view; }",
    );
}

#[test]
fn sequential_calls_and_writes_use_the_latest_memory_state() {
    let wrapper = "&'a i32 update<'a>(&mut &'a i32 slot,&'a i32 value) { replace(&mut *slot,value); return *slot; }";
    passes(&format!(
        "{SET} {wrapper} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; auto result=update(&mut slot,&fresh); old=3; return *result; }}"
    ));
    let two = "void update<'a>(&mut &'a i32 a,&mut &'a i32 b,&'a i32 value) { *a=value; *b=*a; }";
    passes(&format!(
        "{two} i32 f() {{ i32 olda=1; i32 oldb=2; i32 value=3; auto a=&olda; auto b=&oldb; update(&mut a,&mut b,&value); olda=4; oldb=5; return *a+*b; }}"
    ));
}

#[test]
fn moved_mutable_references_are_stored_without_copying_the_capability() {
    let setter =
        "void set<'a>(&mut &'a mut i32 slot,&'a mut i32 value) { *slot=move value; **slot=7; }";
    passes(&format!(
        "{setter} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&mut old; set(&mut slot,&mut fresh); old=3; *slot+=1; return old+*slot; }}"
    ));
    fails(
        "void bad<'a>(&mut &'a mut i32 slot) { auto stolen=move *slot; }",
        "E-FRONTEND-STAGE",
    );
}

#[test]
fn branch_correlations_cannot_duplicate_one_mutable_loan_into_two_live_arguments() {
    let choose = "void choose<'a>(bool c,&mut &'a mut i32 a,&mut &'a mut i32 b,&'a mut i32 value) { if(c) { *a=move value; } else { *b=move value; } } void use(&mut i32 a,&mut i32 b) {}";
    fails(
        &format!(
            "{choose} void f(bool c) {{ i32 x=1; i32 y=2; i32 z=3; auto a=&mut x; auto b=&mut y; choose(c,&mut a,&mut b,&mut z); use(move a,move b); }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn known_function_values_apply_effects_and_unknown_writers_fail_closed() {
    passes(&format!(
        "{SET} i32 f() {{ i32 old=1; i32 fresh=2; auto slot=&old; auto callback=replace; callback(&mut slot,&fresh); old=3; return *slot; }}"
    ));
    fails(
        "void f<'a>(fn(&mut &'a i32,&'a i32) -> void writer,&mut &'a i32 slot,&'a i32 value) { writer(move slot,value); }",
        "E-FRONTEND-STAGE",
    );
}

#[test]
fn unknown_readonly_callbacks_create_fresh_loans_for_nested_mutable_inputs() {
    fails(
        "i32 f<'a>(fn(& &'a mut i32) -> &'a i32 reader,&'a mut i32 value) { auto view=reader(&value); *value=2; return *view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn memory_reports_reject_invalid_input_ids_and_cyclic_loan_graphs() {
    let (mut c, p) = passes(SET);
    let r = c.local_analysis.as_mut().unwrap();
    r.functions[0].memory.as_mut().unwrap().writes[0]
        .target
        .input = usize::MAX;
    assert!(r.validate(&p).is_err());
    let (mut c, p) = passes("&'a i32 reborrow<'a>(&'a i32 value) { return &*value; }");
    let r = c.local_analysis.as_mut().unwrap();
    let m = r.functions[0].memory.as_mut().unwrap();
    m.loans = vec![vec![MemoryLoan::Fresh(1)], vec![MemoryLoan::Fresh(0)]];
    assert!(r.validate(&p).is_err());
}

#[test]
fn mutable_callable_cells_cannot_weaken_their_lifetime_quantifiers() {
    fails(
        "type Universal=for<'a> fn(&'a i32) -> &'a i32; &'static i32 static_only(&'static i32 x) { return x; } &i32 id(&i32 x) { return x; } void weaken(&mut fn(&'static i32) -> &'static i32 slot) { *slot=static_only; } void f() { Universal callback=id; weaken(&mut callback); }",
        "E-REGION-INVARIANT",
    );
}

#[test]
fn unknown_callable_writes_cannot_leave_a_stale_known_function_target() {
    fails(
        &format!(
            "type Setter=for<'s,'a> fn(&'s mut &'a i32,&'a i32) -> void; {SET} i32 f(fn(&mut Setter) -> void change) {{ Setter callback=replace; change(&mut callback); i32 old=1; i32 fresh=2; auto slot=&old; callback(&mut slot,&fresh); old=3; return *slot; }}"
        ),
        "E-FRONTEND-STAGE",
    );
}

#[test]
fn function_values_returned_by_factories_register_dynamic_summary_dependencies() {
    fails(
        "type Setter=for<'s,'a> fn(&'s mut &'a i32,&'a i32) -> void; i32 entry() { i32 old=1; auto slot=&old; { i32 fresh=2; helper(&mut slot,&fresh); } return *slot; } void helper<'a>(&mut &'a i32 slot,&'a i32 value) { auto callback=factory(); callback(move slot,value); } Setter factory() { return wrapper; } void wrapper<'a>(&mut &'a i32 slot,&'a i32 value) { replace(move slot,value); } void replace<'a>(&mut &'a i32 slot,&'a i32 value) { *slot=value; }",
        "E-BORROW-LIFETIME",
    );
}

#[test]
fn independent_functions_do_not_share_an_inference_run_budget() {
    let source = (0..4097)
        .map(|i| format!("void budget_case_{i}() {{}}\n"))
        .collect::<String>();
    let (c, program) = check(&source);
    assert!(program.is_some(), "{:#?}", c.diagnostics);
    assert!(
        c.local_analysis
            .unwrap()
            .regions
            .iter()
            .all(|c| c.body_checked)
    );
}

#[test]
fn known_callable_stores_replace_the_target_set() {
    let declarations = format!(
        "type Setter=for<'s,'a> fn(&'s mut &'a i32,&'a i32) -> void; {SET} void noop<'a>(&mut &'a i32 slot,&'a i32 value) {{}} void change(&mut Setter target) {{ *target=noop; }}"
    );
    fails(
        &format!(
            "{declarations} i32 f() {{ Setter callback=replace; change(&mut callback); i32 old=1; i32 fresh=2; auto slot=&old; callback(&mut slot,&fresh); old=3; return *slot; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn short_circuit_with_a_nonreturning_operand_preserves_the_normal_path() {
    let source = "bool diverge() { return diverge(); } void update<'a>(bool ignored,&mut &'a i32 slot,&'a i32 value) { *slot=value; } i32 entry(bool condition) { bool flag=condition && diverge(); i32 old=1; auto slot=&old; { i32 fresh=2; update(flag,&mut slot,&fresh); } return *slot; }";
    fails(source, "E-BORROW-LIFETIME");
    passes(
        "bool diverge() { return diverge(); } bool f(bool c) { bool flag=c && diverge(); return flag; }",
    );
}
