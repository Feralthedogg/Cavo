use cavo_compiler::{
    Compilation, hir,
    local::{self, Verdict},
};

fn check(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut c = Compilation::default();
    let file = c.sources.add("ownership.cavo", source.into()).unwrap();
    c.parse(file);
    let p = c.check();
    (c, p)
}

fn passes(source: &str) {
    let (c, p) = check(source);
    assert!(c.diagnostics.is_empty(), "{source}\n{:#?}", c.diagnostics);
    let p = p.unwrap();
    let report = c.local_analysis.unwrap();
    report.validate(&p).unwrap();
    assert_eq!(report.verdict, Verdict::Undetermined);
    assert!(
        report
            .functions
            .iter()
            .all(|f| f.local_complete && f.nll.is_some())
    );
}

fn fails(source: &str, code: &str) {
    let (c, p) = check(source);
    assert!(p.is_none(), "expected {code} for {source}");
    assert!(
        c.diagnostics.iter().any(|d| d.code == code),
        "{source}\nexpected {code}: {:#?}",
        c.diagnostics
    );
}

const PAIR: &str = "struct Pair<T> { T left; T right; }";

#[test]
fn partial_moves_preserve_sibling_values_and_reject_repeated_or_whole_uses() {
    passes(&format!(
        "{PAIR} T f<T>(Pair<T> pair) {{ T first = move pair.left; return move pair.right; }}"
    ));
    for tail in [
        "return move pair.left;",
        "Pair<T> copy = move pair; return move copy.left;",
        "auto view = &pair.left; return move pair.right;",
    ] {
        fails(
            &format!("{PAIR} T f<T>(Pair<T> pair) {{ T first = move pair.left; {tail} }}"),
            "E-MOVE-USE",
        );
    }
}

#[test]
fn reinitializing_a_moved_field_restores_the_complete_owner() {
    passes(&format!(
        "{PAIR} Pair<T> f<T>(Pair<T> pair, T next) {{ T first = move pair.left; pair.left = move next; return move pair; }}"
    ));
    fails(
        &format!(
            "{PAIR} Pair<T> f<T>(Pair<T> pair, T next, bool c) {{ T first = move pair.left; if (c) {{ pair.left = move next; }} return move pair; }}"
        ),
        "E-MOVE-USE",
    );
}

#[test]
fn field_by_field_initialization_requires_every_field_on_every_path() {
    passes(&format!(
        "{PAIR} Pair<i32> f() {{ Pair<i32> pair; pair.left = 1; pair.right = 2; return pair; }}"
    ));
    passes(&format!(
        "{PAIR} Pair<i32> f(bool c) {{ Pair<i32> pair; pair.left = 1; if (c) {{ pair.right = 2; }} else {{ pair.right = 3; }} return pair; }}"
    ));
    fails(
        &format!("{PAIR} Pair<i32> f() {{ Pair<i32> pair; pair.left = 1; return pair; }}"),
        "E-INIT-READ",
    );
    fails(
        &format!(
            "{PAIR} Pair<i32> f(bool c) {{ Pair<i32> pair; pair.left = 1; if (c) {{ pair.right = 2; }} return pair; }}"
        ),
        "E-INIT-READ",
    );
}

#[test]
fn nested_partial_moves_and_parent_reinitialization_are_consistent() {
    let source = format!("{PAIR} struct Tree<T> {{ Pair<T> first; Pair<T> second; }}");
    passes(&format!(
        "{source} T f<T>(Tree<T> tree) {{ T first = move tree.first.left; return move tree.first.right; }}"
    ));
    passes(&format!(
        "{source} Tree<T> f<T>(Tree<T> tree, Pair<T> next) {{ T first = move tree.first.left; tree.first = move next; return move tree; }}"
    ));
    fails(
        &format!(
            "{source} T f<T>(Tree<T> tree) {{ Pair<T> first = move tree.first; return move tree.first.right; }}"
        ),
        "E-MOVE-USE",
    );
}

#[test]
fn loop_backedges_track_field_reconsumption_and_repair() {
    fails(
        &format!(
            "{PAIR} void take<T>(T value) {{}} void f<T>(Pair<T> pair, bool c) {{ while (c) {{ take(move pair.left); }} }}"
        ),
        "E-MOVE-USE",
    );
    passes(&format!(
        "{PAIR} void take<T>(T value) {{}} Pair<T> f<T>(Pair<T> pair, T next, bool c) {{ while (c) {{ take(move pair.left); pair.left = move next; break; }} return move pair; }}"
    ));
    fails(
        &format!(
            "{PAIR} Pair<T> f<T>(Pair<T> pair, bool c) {{ if (c) {{ T value = move pair.left; }} return move pair; }}"
        ),
        "E-MOVE-USE",
    );
}

#[test]
fn input_reference_fields_can_be_moved_independently() {
    passes(
        "struct Views { &mut i32 left; &mut i32 right; } i32 f(Views views) { auto left = move views.left; auto right = move views.right; *left += *right; return *left; }",
    );
    fails(
        "struct Views { &mut i32 left; &mut i32 right; } void f(Views views) { auto left = move views.left; auto again = move views.left; }",
        "E-MOVE-USE",
    );
}

#[test]
fn partial_moves_keep_reference_origins_in_the_correct_field() {
    passes(
        "struct Views { &mut i32 left; &mut i32 right; } i32 f() { i32 x = 1; i32 y = 2; Views views = Views { left: &mut x, right: &mut y }; auto left = move views.left; *left += 1; x = 3; *views.right += 1; return x + y; }",
    );
    fails(
        "struct Views { &mut i32 left; &mut i32 right; } i32 f() { i32 x = 1; i32 y = 2; Views views = Views { left: &mut x, right: &mut y }; auto right = move views.right; x = 3; return *views.left + *right; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn full_record_moves_preserve_nested_reference_payloads() {
    passes(
        "struct Inner { &i32 view; } struct Outer { Inner first; Inner second; } i32 f() { i32 x = 1; i32 y = 2; Outer outer = Outer { first: Inner { view: &x }, second: Inner { view: &y } }; Outer copy = outer; i32 old = *copy.second.view; y = 3; return *copy.first.view + old; }",
    );
}

#[test]
fn temporary_field_selection_preserves_the_selected_shape_and_discards_other_origins() {
    let declarations =
        "struct Views { &i32 left; &i32 right; } struct Outer { Views first; Views second; }";
    let setup = "i32 x = 1; i32 y = 2; i32 z = 3; Views selected = (Outer { first: Views { left: &x, right: &y }, second: Views { left: &z, right: &z } }).first;";
    fails(
        &format!(
            "{declarations} i32 f() {{ {setup} i32 old = *selected.left; y = 4; return *selected.right + old; }}"
        ),
        "E-BORROW-CONFLICT",
    );
    passes(&format!(
        "{declarations} i32 f() {{ {setup} z = 4; return *selected.right + z; }}"
    ));
}

#[test]
fn possible_rvalue_destructors_retain_loans_through_the_full_expression() {
    fails(
        "struct Bundle<T> { i32 number; T payload; } Bundle<T> carry<T>(Bundle<T> value, &i32 view) { return move value; } i32 change(&mut i32 value) { *value = 2; return 2; } void use(i32 a, i32 b) {} void f<T>(Bundle<T> value) { i32 x = 1; use(carry(move value, &x).number, change(&mut x)); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn a_live_sibling_loan_allows_partial_moves_but_not_overlapping_moves() {
    passes(
        "struct Record<T> { T value; i32 tag; } T f<T>(Record<T> record) { auto tag = &mut record.tag; T value = move record.value; *tag = 3; return move value; }",
    );
    fails(
        &format!(
            "{PAIR} T f<T>(Pair<T> pair) {{ auto view = &pair.left; T value = move pair.left; auto later = &view; return move value; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn nll_releases_shared_and_exclusive_loans_after_their_last_use() {
    passes(
        "i32 f() { i32 value = 1; auto view = &value; i32 old = *view; value = 2; return value + old; }",
    );
    passes(
        "i32 f() { i32 value = 1; auto view = &mut value; *view += 1; value += 2; return value; }",
    );
    passes(
        "i32 f() { i32 value = 1; auto unused = &mut value; auto next = &mut value; *next = 2; return value; }",
    );
    fails(
        "i32 f() { i32 value = 1; auto view = &value; value = 2; return *view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn copied_and_moved_reference_holders_keep_loans_live_until_the_final_holder_use() {
    passes(
        "i32 f() { i32 x = 1; auto first = &x; auto second = first; i32 old = *second; x = 3; return x + old; }",
    );
    fails(
        "i32 f() { i32 x = 1; auto first = &x; auto second = first; x = 3; return *second; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "i32 f() { i32 x = 1; auto first = &mut x; auto second = move first; return *first; }",
        "E-MOVE-USE",
    );
}

#[test]
fn nll_keeps_transitive_reference_to_reference_loans_live() {
    fails(
        "i32 f() { i32 x = 1; auto view = &x; auto indirect = &view; x = 3; return **indirect; }",
        "E-BORROW-CONFLICT",
    );
    passes(
        "i32 f() { i32 x = 1; auto view = &x; auto indirect = &view; i32 old = **indirect; x = 3; return x + old; }",
    );
    fails(
        "struct Hold { &i32 view; } i32 f() { i32 x = 1; Hold hold = Hold { view: &x }; auto indirect = &hold; x = 3; return *indirect.view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn nll_can_release_a_rhs_loan_before_the_assignment_store() {
    passes("i32 f() { i32 x = 1; auto view = &x; x = *view + 1; return x; }");
    fails(
        "i32 f() { i32 x = 1; auto view = &x; x = *view + 1; return *view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn argument_temporaries_and_projected_reference_handles_do_not_end_early() {
    fails(
        "void use(&i32 view, i32 value) {} i32 change(&mut i32 value) { *value = 2; return 2; } void f() { i32 x = 1; auto view = &x; use(view, change(&mut x)); }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Pair { i32 left; i32 right; } struct Hold { &mut Pair view; } i32 consume(&mut Pair value) { return 1; } void f(Pair pair) { Hold hold = Hold { view: &mut pair }; hold.view.left = consume(move hold.view); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn branch_specific_liveness_and_future_uses_are_distinguished() {
    passes(
        "i32 f(bool c) { i32 x = 1; auto view = &x; if (c) { i32 old = *view; } else { x = 3; } return x; }",
    );
    fails(
        "i32 f(bool c) { i32 x = 1; auto view = &x; x = 3; if (c) { return *view; } return x; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn loop_liveness_includes_the_next_iteration() {
    fails(
        "void use(i32 value) {} void f(bool c) { i32 x = 1; auto view = &x; while (c) { use(*view); x = 2; } }",
        "E-BORROW-CONFLICT",
    );
    passes(
        "void use(i32 value) {} i32 f(bool c) { i32 x = 1; while (c) { auto view = &x; use(*view); x += 1; } return x; }",
    );
}

#[test]
fn break_continue_and_constant_short_circuit_paths_preserve_nll() {
    passes(
        "void use(i32 value) {} i32 f(bool c, bool stop) { i32 x = 1; while (c) { auto view = &x; if (stop) { x = 2; break; } use(*view); x += 1; continue; } return x; }",
    );
    passes(
        "bool read(&i32 view) { return *view > 0; } void f() { i32 x = 1; auto view = &x; x = 2; bool ignored = false && read(view); }",
    );
    fails(
        "bool read(&i32 view) { return *view > 0; } void f(bool c) { i32 x = 1; auto view = &x; x = 2; bool ignored = c && read(view); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn record_field_liveness_releases_only_the_dead_payload_loan() {
    passes(
        "struct Views { &i32 left; &i32 right; } i32 f() { i32 x = 1; i32 y = 2; Views views = Views { left: &x, right: &y }; i32 old = *views.right; y = 3; return *views.left + old; }",
    );
}

#[test]
fn possible_destructor_uses_keep_opaque_generic_loans_live() {
    fails(
        "T carry<T>(T value, &i32 view) { return move value; } void f<T>(T value) { i32 x = 1; T pending = carry(move value, &x); x = 3; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "T carry<T>(T value, &i32 view) { return move value; } void f<T>(T value) { T pending; { i32 x = 1; pending = carry(move value, &x); } }",
        "E-BORROW-LIFETIME",
    );
}

#[test]
fn overwrites_strongly_update_exact_fields_and_weakly_update_ambiguous_targets() {
    passes(
        "struct Hold { &i32 view; } i32 f() { i32 x = 1; i32 y = 2; Hold hold = Hold { view: &x }; hold.view = &y; x = 3; return *hold.view + x; }",
    );
    fails(
        "struct Hold { &i32 view; } i32 f(bool c) { i32 x = 1; i32 y = 2; Hold a = Hold { view: &x }; Hold b = Hold { view: &x }; &mut Hold target; if (c) { target = &mut a; } else { target = &mut b; } target.view = &y; x = 3; return *a.view + *b.view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn expired_unused_references_do_not_extend_storage_but_return_escape_is_rejected() {
    passes("void f() { &i32 view; { i32 x = 1; view = &x; } }");
    fails(
        "i32 f() { &i32 view; { i32 x = 1; view = &x; } return *view; }",
        "E-BORROW-LIFETIME",
    );
    fails(
        "&i32 f() { i32 x = 1; auto view = &x; return view; }",
        "E-BORROW-RETURN",
    );
}

#[test]
fn indexed_moves_remain_unsupported_while_local_reborrows_are_checked() {
    fails(
        "T f<T>(T[2] values) { return move values[0]; }",
        "E-FRONTEND-STAGE",
    );
    passes("void f() { i32 x = 1; auto view = &mut x; auto nested = &mut *view; }");
}

#[test]
fn nll_report_rejects_invalid_leaf_sets_block_shapes_and_missing_analysis() {
    let (mut c, p) = check("i32 f() { i32 x = 1; auto view = &x; return *view; }");
    let p = p.unwrap();
    let report = c.local_analysis.as_mut().unwrap();
    let nll = report.functions[0].nll.as_mut().unwrap();
    let saved = nll.leaves[0];
    nll.leaves[0] = local::PlaceId(u32::MAX);
    assert!(report.validate(&p).is_err());
    report.functions[0].nll.as_mut().unwrap().leaves[0] = saved;
    report.functions[0]
        .nll
        .as_mut()
        .unwrap()
        .block_entry
        .clear();
    assert!(report.validate(&p).is_err());
    report.functions[0].nll = None;
    assert!(report.validate(&p).is_err());
}
