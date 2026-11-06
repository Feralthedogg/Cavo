use cavo_compiler::{
    Compilation, hir,
    local::{self, Verdict},
    types::{Region, Ty},
};

fn check(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut c = Compilation::default();
    let file = c.sources.add("regions.cavo", source.into()).unwrap();
    c.parse(file);
    let p = c.check();
    (c, p)
}
fn passes(source: &str) -> (Compilation, hir::Program) {
    let (c, p) = check(source);
    assert!(c.diagnostics.is_empty(), "{source}\n{:#?}", c.diagnostics);
    let p = p.unwrap();
    let report = c.local_analysis.as_ref().unwrap();
    report.validate(&p).unwrap();
    assert_eq!(report.verdict, Verdict::Undetermined);
    assert!(report.regions.iter().all(|c| !c.has_body || c.body_checked));
    (c, p)
}
fn fails(source: &str, code: &str) -> Compilation {
    let (c, p) = check(source);
    assert!(p.is_none(), "expected {code} for {source}");
    assert!(
        c.diagnostics.iter().any(|d| d.code == code),
        "{source}\nexpected {code}: {:#?}",
        c.diagnostics
    );
    c
}

#[test]
fn declared_return_regions_are_checked_against_the_actual_input() {
    passes("&'a i32 first<'a, 'b>(&'a i32 a, &'b i32 b) { return a; }");
    fails(
        "&'a i32 bad<'a, 'b>(&'a i32 a, &'b i32 b) { return b; }",
        "E-REGION-RETURN",
    );
    passes("&'a i32 choose<'a>(&'a i32 a, &'a i32 b, bool c) { if (c) { return a; } return b; }");
}

#[test]
fn calls_retain_only_the_inputs_selected_by_the_declared_return_region() {
    passes(
        "&'a i32 first<'a, 'b>(&'a i32 a, &'b i32 b) { return a; } i32 f() { i32 x = 1; &i32 view; { i32 y = 2; view = first(&x, &y); y = 3; } return *view; }",
    );
    fails(
        "&'a i32 choose<'a>(&'a i32 a, &'a i32 b, bool c) { if (c) { return a; } return b; } i32 f(bool c) { i32 x = 1; &i32 view; { i32 y = 2; view = choose(&x, &y, c); } return *view; }",
        "E-BORROW-LIFETIME",
    );
}

#[test]
fn elision_requires_one_reference_input_or_a_body_checked_static_origin() {
    passes("&i32 id(&i32 value, i32 ignored) { return value; }");
    passes("&str text() { return \"hello\"; } &'static str f() { return text(); }");
    fails(
        "&i32 ambiguous(&i32 a, &i32 b) { return a; }",
        "E-REGION-ELISION",
    );
    fails(
        "&i32 bad() { i32 local = 1; return &local; }",
        "E-BORROW-RETURN",
    );
}

#[test]
fn static_requirements_use_origin_instead_of_the_value_type_label() {
    passes(
        "&'static str id(&'static str text) { return text; } &'static str f() { return id(\"hello\"); }",
    );
    fails(
        "&'static i32 bad(&i32 value) { return value; }",
        "E-REGION-RETURN",
    );
    fails(
        "void need(&'static i32 value) {} void f() { i32 local = 1; need(&local); }",
        "E-REGION-ARG",
    );
    fails(
        "void f() { i32 local = 1; &'static i32 forged = &local; }",
        "E-REGION-STORE",
    );
    fails(
        "struct Hold { &'static i32 view; } void f() { i32 local = 1; Hold hold = Hold { view: &local }; }",
        "E-REGION-STORE",
    );
}

#[test]
fn generic_instantiation_cannot_hide_a_static_argument_requirement() {
    fails(
        "T choose<T>(T a, T b) { return move b; } void need(&'static i32 value) {} void f(&'static i32 value) { i32 local = 1; need(choose(value, &local)); }",
        "E-REGION-ARG",
    );
}

#[test]
fn generic_record_input_components_preserve_the_declared_region() {
    passes(
        "struct Hold<T> { T view; } &'a T get<'a, T>(Hold<&'a T> value) { return value.view; } i32 f<'a>(Hold<&'a i32> value) { auto view = get::<i32>(move value); return *view; }",
    );
}

#[test]
fn declared_local_lifetimes_cannot_be_strengthened() {
    passes("void f<'a>(&'a i32 value) { &'a i32 view = value; }");
    fails(
        "void f<'a, 'b>(&'a i32 a, &'b i32 b) { &'a i32 view = b; }",
        "E-REGION-STORE",
    );
    fails(
        "void f<'a>(&'a i32 value) { i32 local = 1; &'a i32 view = &local; }",
        "E-REGION-STORE",
    );
}

#[test]
fn unknown_duplicate_and_reserved_lifetime_names_are_rejected() {
    fails("&'a i32 bad(&i32 value) { return value; }", "E-REGION-NAME");
    fails("void f<'a, 'a>() {}", "E-NAME-DUPLICATE");
    fails("void f<'static>() {}", "E-REGION-NAME");
    let names = (0..65)
        .map(|i| format!("'a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    fails(&format!("void f<{names}>() {{}}"), "E-REGION-LIMIT");
}

#[test]
fn call_region_variables_are_fresh_and_equal_only_within_the_same_instantiation() {
    let (_, p) = passes(
        "&'a i32 select<'a>(&'a i32 a, &'a i32 b) { return a; } i32 f() { i32 x = 1; i32 y = 2; auto a = (select)(&x, &x); auto b = select(&y, &y); return *a + *b; }",
    );
    let f = p.functions.last().unwrap();
    let mut calls = Vec::new();
    for expr in &f.expressions {
        if let hir::ExprKind::Call {
            parameter_types, ..
        } = &expr.kind
        {
            let region = |ty| match p.types.get(ty) {
                Ty::Reference { region, .. } => *region,
                _ => panic!(),
            };
            assert_eq!(region(parameter_types[0]), region(parameter_types[1]));
            assert_eq!(region(parameter_types[0]), region(expr.ty));
            calls.push(region(expr.ty));
        }
    }
    assert_eq!(calls.len(), 2);
    assert_ne!(calls[0], calls[1]);
}

#[test]
fn regions_inside_actual_type_arguments_keep_the_callers_binder() {
    let (_, p) = passes(
        "T identity<T>(T value) { return move value; } &'a T f<'a, T>(&'a T value) { return identity::<&'a T>(value); }",
    );
    let f = p.functions.last().unwrap();
    let call = f
        .expressions
        .iter()
        .find(|e| matches!(e.kind, hir::ExprKind::Call { .. }))
        .unwrap();
    assert!(
        matches!(p.types.get(call.ty), Ty::Reference { region: Region::Named { owner, .. }, .. } if *owner == f.definition)
    );
}

#[test]
fn named_contracts_work_through_forward_and_recursive_calls() {
    passes(
        "&'a i32 first<'a>(&'a i32 value, bool again) { if (again) { return second(value, false); } return value; } &'a i32 second<'a>(&'a i32 value, bool again) { return first(value, again); }",
    );
    let c = fails(
        "&'a i32 first<'a>(&'a i32 value, bool again) { if (again) { return second(value, false); } return value; } &'a i32 second<'a>(&'a i32 value, bool again) { i32 local = 1; return &local; }",
        "E-BORROW-RETURN",
    );
    assert!(
        c.local_analysis
            .unwrap()
            .regions
            .iter()
            .all(|c| !c.body_checked)
    );
}

#[test]
fn prototypes_need_summaries_and_managed_indirect_calls_keep_region_contracts() {
    fails(
        "extern \"C\" { &'a i32 external<'a>(&'a i32 value); } &i32 f(&i32 value) { return external(value); }",
        "E-FRONTEND-STAGE",
    );
    passes(
        "&'a i32 id<'a>(&'a i32 value) { return value; } &i32 f(&i32 value) { auto indirect = id; return indirect(value); }",
    );
}

#[test]
fn local_mutable_reborrow_freezes_and_then_restores_the_parent() {
    passes(
        "i32 f() { i32 x = 1; auto parent = &mut x; auto child = &mut *parent; *child += 1; *parent += 2; return x; }",
    );
    fails(
        "i32 f() { i32 x = 1; auto parent = &mut x; auto child = &mut *parent; *parent = 2; return *child; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "i32 f() { i32 x = 1; auto parent = &mut x; auto child = &mut *parent; i32 observed = *parent; return *child + observed; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn reborrows_from_input_referents_have_real_conflict_identity() {
    passes(
        "i32 f(&mut i32 value) { auto child = &mut *value; *child += 1; *value += 2; return *value; }",
    );
    fails(
        "i32 f(&mut i32 value) { auto child = &mut *value; *value = 2; return *child; }",
        "E-BORROW-CONFLICT",
    );
    passes("i32 f(&i32 value) { auto child = &*value; return *child + *value; }");
}

#[test]
fn shared_children_allow_parent_reads_but_forbid_writes() {
    passes(
        "i32 f(&mut i32 value) { auto child = &*value; i32 observed = *value; return *child + observed; }",
    );
    fails(
        "i32 f(&mut i32 value) { auto child = &*value; *value = 2; return *child; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "void f(&i32 value) { auto invalid = &mut *value; }",
        "E-BORROW-MUTABLE",
    );
}

#[test]
fn nested_reborrow_ancestry_restores_each_parent_in_order() {
    passes(
        "i32 f(&mut i32 value) { auto child = &mut *value; auto grandchild = &mut *child; *grandchild += 1; *child += 2; *value += 3; return *value; }",
    );
    fails(
        "i32 f(&mut i32 value) { auto child = &mut *value; auto grandchild = &mut *child; *child = 2; return *grandchild; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "i32 f(&mut i32 value) { auto child = &mut *value; auto grandchild = &mut *child; *value = 2; return *grandchild; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn disjoint_input_fields_can_be_reborrowed_without_freezing_the_whole_record() {
    passes(
        "struct Pair { i32 left; i32 right; } i32 f(&mut Pair pair) { auto left = &mut pair.left; auto right = &mut pair.right; *left += *right; pair.left += 1; return pair.left; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } i32 f(&mut Pair pair) { auto left = &mut pair.left; pair.left = 2; return *left; }",
        "E-BORROW-CONFLICT",
    );
    passes(
        "struct Pair { i32 left; i32 right; } i32 f(&mut Pair pair) { auto left = &mut pair.left; pair.right = 2; return *left; }",
    );
}

#[test]
fn a_frozen_parent_cannot_be_moved_into_a_call_or_aggregate() {
    fails(
        "void consume(&mut i32 value) { *value = 2; } i32 f(&mut i32 value) { auto child = &mut *value; consume(move value); return *child; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Hold { &mut i32 view; } i32 f(&mut i32 value) { auto child = &mut *value; Hold hold = Hold { view: move value }; return *child; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn stored_mutable_reference_fields_keep_reborrow_ancestry() {
    passes(
        "struct Pair { i32 left; i32 right; } struct Hold { &mut Pair view; } i32 f(Pair pair) { Hold hold = Hold { view: &mut pair }; auto child = &mut hold.view.left; *child = 2; hold.view.right = 3; return hold.view.left; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } struct Hold { &mut Pair view; } i32 f(Pair pair) { Hold hold = Hold { view: &mut pair }; auto child = &mut hold.view.left; hold.view.left = 2; return *child; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn a_returned_reborrow_keeps_the_callers_parent_frozen() {
    let id = "&'a mut T id<'a, T>(&'a mut T value) { return &mut *value; }";
    passes(&format!(
        "{id} i32 f(&mut i32 value) {{ auto child = id(&mut *value); *child += 1; *value += 2; return *value; }}"
    ));
    fails(
        &format!(
            "{id} i32 f(&mut i32 value) {{ auto child = id(&mut *value); *value = 2; return *child; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn shared_return_types_downgrade_permissions_without_erasing_the_loan() {
    let share = "&'a i32 share<'a>(&'a mut i32 value) { return &*value; }";
    passes(&format!(
        "{share} i32 f(&mut i32 value) {{ auto child = share(&mut *value); i32 observed = *value + *child; *value = 2; return observed; }}"
    ));
    fails(
        &format!(
            "{share} i32 f(&mut i32 value) {{ auto child = share(&mut *value); *value = 2; return *child; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn static_return_annotations_do_not_erase_exclusive_parent_loans() {
    let share = "&'static i32 share(&'static mut i32 value) { return &*value; }";
    fails(
        &format!(
            "{share} i32 f(&'static mut i32 value) {{ auto child = share(&mut *value); *value = 2; return *child; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn reborrow_origins_survive_branches_and_loop_backedges() {
    fails(
        "i32 f(&mut i32 first, &mut i32 second, bool c) { &mut i32 child; if (c) { child = &mut *first; } else { child = &mut *second; } *first = 2; return *child; }",
        "E-BORROW-CONFLICT",
    );
    passes(
        "i32 f(&mut i32 value, bool c) { while (c) { auto child = &mut *value; *child += 1; *value += 2; } return *value; }",
    );
    fails(
        "void use(i32 n) {} void f(&mut i32 value, bool c) { auto child = &mut *value; while (c) { use(*child); *value = 2; } }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn parameter_storage_and_its_original_referent_are_distinct_places() {
    passes(
        "&mut i32 f(&mut i32 value) { auto child = &mut *value; i32 local = 2; value = &mut local; return move child; }",
    );
    fails(
        "&mut i32 f(&mut i32 value) { i32 local = 2; value = &mut local; return move value; }",
        "E-BORROW-RETURN",
    );
}

#[test]
fn returned_local_reborrows_still_cannot_escape() {
    fails(
        "&i32 f() { i32 value = 1; auto parent = &mut value; return &*parent; }",
        "E-BORROW-RETURN",
    );
    fails(
        "&'a i32 f<'a>(&'a i32 input) { i32 value = 1; auto parent = &mut value; return &*parent; }",
        "E-BORROW-RETURN",
    );
}

#[test]
fn nested_mutable_reference_regions_are_never_silently_weakened() {
    passes("&'a mut &i32 identity<'a>(&'a mut &'static i32 input) { return move input; }");
    fails(
        "&'static i32 bad<'a>(&'a &i32 input) { return *input; }",
        "E-REGION-RETURN",
    );
    passes(
        "void inspect(&mut [&i32] values) {} void f(&'static i32 value) { auto data = [value]; inspect(&mut data); }",
    );
    fails(
        "&'a mut &'a i32 bad<'a,'b>(&'a mut &'b i32 input) { return move input; }",
        "E-REGION-INVARIANT",
    );
}

#[test]
fn deep_reborrow_lineages_fail_closed_at_the_analysis_limit() {
    let mut source = String::from("void f() { i32 value = 0; auto r0 = &mut value;");
    for index in 1..140 {
        source.push_str(&format!("auto r{index} = &mut *r{};", index - 1));
    }
    source.push('}');
    let c = fails(&source, "E-LOCAL-LIMIT");
    let report = c.local_analysis.unwrap();
    assert!(!report.functions[0].local_complete);
    assert!(report.functions[0].findings.is_empty());
}

#[test]
fn body_summaries_preserve_precise_returned_subfields_and_their_loans() {
    let field = "struct Pair { i32 left; i32 right; } &'a mut i32 left<'a>(&'a mut Pair value) { return &mut value.left; }";
    passes(&format!(
        "{field} i32 f(Pair pair) {{ auto view = left(&mut pair); *view = 2; return pair.right; }}"
    ));
    passes(&format!(
        "{field} i32 f(Pair pair) {{ auto view = left(&mut pair); pair.right = 2; return *view; }}"
    ));
    fails(
        &format!(
            "{field} i32 f(Pair pair) {{ auto view=left(&mut pair); pair.left=2; return *view; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn region_and_reborrow_report_ids_are_structurally_checked() {
    let (mut c, p) = passes("&'a mut i32 id<'a>(&'a mut i32 value) { return &mut *value; }");
    let report = c.local_analysis.as_mut().unwrap();
    report.regions[0].return_inputs.push(usize::MAX);
    assert!(report.validate(&p).is_err());
    report.regions[0].return_inputs.pop();
    let trace = report.functions[0].reborrows.first_mut().unwrap();
    trace
        .parents
        .push(local::LoanId::Input(local::PlaceId(u32::MAX)));
    assert!(report.validate(&p).is_err());
}
