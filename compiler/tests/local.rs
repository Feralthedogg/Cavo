use cavo_compiler::{
    Compilation, hir,
    local::{self, Assessment, Evidence, Predicate, Verdict},
};

fn checked(source: &str) -> (Compilation, Option<hir::Program>) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("local.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let program = compilation.check();
    (compilation, program)
}

fn passes(source: &str) -> (Compilation, hir::Program) {
    let (compilation, program) = checked(source);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let program = program.unwrap();
    compilation
        .local_analysis
        .as_ref()
        .unwrap()
        .validate(&program)
        .unwrap();
    (compilation, program)
}

fn fails(source: &str, code: &str) -> Compilation {
    let (compilation, program) = checked(source);
    assert!(program.is_none(), "expected {code} for {source}");
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == code),
        "expected {code}: {:#?}",
        compilation.diagnostics
    );
    assert_eq!(
        compilation.local_analysis.as_ref().unwrap().verdict,
        Verdict::Rejected
    );
    compilation
}

#[test]
fn local_success_retains_types_and_incomplete_global_coverage() {
    let (compilation, program) = passes("i32 main() { i32 value = 1; value += 2; return value; }");
    assert_eq!(program.stage, hir::ValidationStage::Types);
    let report = compilation.local_analysis.as_ref().unwrap();
    assert_eq!(report.verdict, Verdict::Undetermined);
    assert!(!report.not_analyzed.is_empty());
    assert!(report.functions[0].local_complete);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.assessment == Assessment::Established)
    );
}

#[test]
fn non_copy_moves_require_spelling_and_invalidate_the_old_owner() {
    fails(
        "T bad<T>(T value) { T other = value; return move other; }",
        "E-MOVE-EXPLICIT",
    );
    fails(
        "void take<T>(T value) {} T bad<T>(T value) { take(move value); return move value; }",
        "E-MOVE-USE",
    );
    passes("T good<T>(T value) { T other = move value; return move other; }");
    passes("i32 good(i32 value) { i32 other = move value; return value + other; }");
}

#[test]
fn structural_copy_includes_generic_records_and_enum_payloads() {
    passes(
        "struct Wrap<T> { T value; } Wrap<i32> copy(Wrap<i32> first) { Wrap<i32> second = first; return first; }",
    );
    passes(
        "enum Choice<T> { None, Some(T) } Choice<i32> copy(Choice<i32> first) { Choice<i32> second = first; return first; }",
    );
    fails(
        "struct Wrap<T> { T value; } Wrap<T> bad<T>(Wrap<T> first) { Wrap<T> second = first; return move second; }",
        "E-MOVE-EXPLICIT",
    );
}

#[test]
fn branch_merges_keep_moves_and_reinitialization_path_sensitive() {
    fails(
        "void take<T>(T value) {} T f<T>(bool c, T value) { if (c) { take(move value); } return move value; }",
        "E-MOVE-USE",
    );
    passes(
        "void take<T>(T value) {} T f<T>(T value, T next) { take(move value); value = move next; return move value; }",
    );
    passes(
        "void take<T>(T value) {} T f<T>(bool c, T value, T next) { if (c) { take(move value); value = move next; } return move value; }",
    );
    fails(
        "void take<T>(T value) {} T f<T>(bool c, T value, T next) { take(move value); if (c) { value = move next; } return move value; }",
        "E-MOVE-USE",
    );
}

#[test]
fn loop_backedges_detect_repeated_consumption_and_do_not_duplicate_diagnostics() {
    let compilation = fails(
        "void take<T>(T value) {} void f<T>(bool c, T value) { while (c) { take(move value); } }",
        "E-MOVE-USE",
    );
    assert_eq!(
        compilation
            .diagnostics
            .iter()
            .filter(|d| d.code == "E-MOVE-USE")
            .count(),
        1
    );
    fails(
        "bool take<T>(T value) { return true; } void f<T>(T value) { while (take(move value)) {} }",
        "E-MOVE-USE",
    );
    passes(
        "void take<T>(T value) {} void f<T>(bool c, T value, T next) { while (c) { take(move value); value = move next; break; } }",
    );
}

#[test]
fn break_skips_for_update_while_continue_executes_it() {
    passes(
        "void take<T>(T value) {} T f<T>(T value) { for (i32 i = 0; i < 3; take(move value)) { break; } return move value; }",
    );
    fails(
        "void take<T>(T value) {} void f<T>(T value) { for (i32 i = 0; i < 3; take(move value)) { continue; } }",
        "E-MOVE-USE",
    );
    passes("i32 f() { i32 value; while (true) { value = 1; break; } return value; }");
}

#[test]
fn short_circuit_preserves_conditional_moves_and_constant_unreachable_paths() {
    passes(
        "bool take<T>(T value) { return true; } T f<T>(T value) { bool result = false && take(move value); return move value; }",
    );
    passes(
        "bool take<T>(T value) { return true; } T f<T>(T value) { bool result = true || take(move value); return move value; }",
    );
    fails(
        "bool take<T>(T value) { return true; } T f<T>(bool c, T value) { bool result = c && take(move value); return move value; }",
        "E-MOVE-USE",
    );
    passes(
        "void take<T>(T value) {} T f<T>(T value) { if (false) { take(move value); } return move value; }",
    );
}

#[test]
fn direct_shared_loans_allow_reads_and_forbid_conflicting_writes() {
    passes(
        "i32 f() { i32 value = 1; auto first = &value; auto second = first; return *first + *second; }",
    );
    fails(
        "void f() { i32 value = 1; auto view = &value; value = 2; i32 seen = *view; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "void f() { i32 value = 1; auto view = &value; auto editor = &mut value; i32 seen = *view; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn distinct_record_fields_can_be_borrowed_exclusively_at_the_same_time() {
    passes(
        "struct Pair { i32 left; i32 right; } i32 f() { Pair pair = Pair { left: 1, right: 2 }; { auto left = &mut pair.left; auto right = &mut pair.right; *left += 10; *right += 20; } return pair.left + pair.right; }",
    );
    passes(
        "struct Pair { i32 left; i32 right; } i32 f() { Pair pair = Pair { left: 1, right: 2 }; auto left = &mut pair.left; pair.right = 7; *left += pair.right; return *left; }",
    );
}

#[test]
fn same_field_and_whole_owner_accesses_still_conflict() {
    for use_ in [
        "auto second = &mut pair.left;",
        "auto second = &pair.left;",
        "pair.left = 3;",
        "Pair copy = pair;",
        "auto whole = &pair;",
        "pair = Pair { left: 3, right: 4 };",
    ] {
        fails(
            &format!(
                "struct Pair {{ i32 left; i32 right; }} void f() {{ Pair pair = Pair {{ left: 1, right: 2 }}; auto first = &mut pair.left; {use_} *first += 1; }}"
            ),
            "E-BORROW-CONFLICT",
        );
    }
    passes(
        "struct Pair { i32 left; i32 right; } i32 f(Pair pair) { auto first = &pair.left; auto second = &pair.left; return *first + *second; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } void f(Pair pair) { auto whole = &mut pair; pair.right = 3; whole.left = 4; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn nested_field_paths_distinguish_siblings_and_retain_ancestor_conflicts() {
    let declarations =
        "struct Pair { i32 left; i32 right; } struct Tree { Pair first; Pair second; }";
    passes(&format!(
        "{declarations} i32 f(Tree tree) {{ auto first = &mut tree.first.left; auto sibling = &mut tree.first.right; auto second = &mut tree.second.left; *first = *sibling + *second; return *first; }}"
    ));
    fails(
        &format!(
            "{declarations} void f(Tree tree) {{ auto first = &tree.first; auto nested = &mut tree.first.left; i32 seen = first.left; }}"
        ),
        "E-BORROW-CONFLICT",
    );
    fails(
        &format!(
            "{declarations} void f(Tree tree) {{ auto nested = &tree.first.left; tree.first = tree.second; i32 seen = *nested; }}"
        ),
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn field_paths_survive_reference_moves_calls_and_aggregate_transport() {
    passes(
        "struct Pair { i32 left; i32 right; } &mut i32 identity(&mut i32 value) { return move value; } i32 f(Pair pair) { auto first = identity(&mut pair.left); auto next = move first; pair.right = 3; *next = pair.right; return *next; }",
    );
    passes(
        "struct Pair { i32 left; i32 right; } struct Hold { &mut i32 view; } i32 f(Pair pair) { Hold hold = Hold { view: &mut pair.left }; auto view = move hold.view; pair.right = 3; *view += pair.right; return *view; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } &mut i32 identity(&mut i32 value) { return move value; } void f(Pair pair) { auto view = identity(&mut pair.left); pair.left = 3; *view = 4; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn projecting_through_a_reference_keeps_its_original_field_prefix() {
    passes(
        "struct Pair { i32 left; i32 right; } struct Tree { Pair first; Pair second; } i32 f(Tree tree) { auto view = &mut tree.first; auto second = &mut tree.second; view.left = second.right; return view.left; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } struct Tree { Pair first; Pair second; } void f(Tree tree) { auto view = &mut tree.first; view.left = 3; auto conflict = &mut tree.first.right; view.left = 4; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Pair { i32 left; i32 right; } i32 consume(&mut Pair pair) { return 1; } void f(Pair pair) { auto view = &mut pair; view.left = consume(move view); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn sibling_call_arguments_hold_independent_temporary_loans() {
    passes(
        "struct Pair { i32 left; i32 right; } void update(&mut i32 left, &mut i32 right) { *left += *right; } i32 f(Pair pair) { update(&mut pair.left, &mut pair.right); return pair.left; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } void update(&mut i32 left, &mut i32 right) {} void f(Pair pair) { update(&mut pair.left, &mut pair.left); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn array_indices_remain_coarse_without_losing_an_outer_record_field() {
    passes(
        "struct Buffer { i32[2] data; i32 tag; } i32 f(Buffer buffer, usize index) { auto item = &mut buffer.data[index]; buffer.tag = 3; *item += buffer.tag; return *item; }",
    );
    fails(
        "void f(i32[2] data) { auto first = &mut data[0]; auto second = &mut data[1]; *first = 3; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Pair { i32 left; i32 right; } void f(Pair[2] pairs, usize a, usize b) { auto first = &mut pairs[a].left; auto second = &mut pairs[b].right; *first = 3; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Pair { i32 left; i32 right; } void f(Pair[2] pairs) { auto whole = &mut pairs[0]; whole.left = 1; auto second = &mut pairs[1].right; whole.right = 3; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn branch_merged_origins_keep_every_possible_borrowed_field() {
    passes(
        "struct Pair { i32 left; i32 right; i32 tag; } i32 f(Pair pair, bool c) { &mut i32 view; if (c) { view = &mut pair.left; } else { view = &mut pair.right; } pair.tag = 3; *view = pair.tag; return *view; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } void f(Pair pair, bool c) { &mut i32 view; if (c) { view = &mut pair.left; } else { view = &mut pair.right; } pair.left = 3; *view = 4; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn initialization_and_storage_lifetimes_remain_checked_with_partial_moves() {
    fails(
        "struct Pair { i32 left; i32 right; } void f() { Pair pair; auto view = &pair.left; }",
        "E-INIT-READ",
    );
    passes(
        "struct Pair<T> { T left; i32 right; } T f<T>(Pair<T> pair) { auto view = &pair.right; T left = move pair.left; i32 seen = *view; return move left; }",
    );
    fails(
        "struct Pair { i32 left; i32 right; } &i32 f(Pair pair) { return &pair.left; }",
        "E-BORROW-RETURN",
    );
    fails(
        "struct Pair { i32 left; i32 right; } i32 f() { &i32 view; { Pair pair = Pair { left: 1, right: 2 }; view = &pair.left; } return *view; }",
        "E-BORROW-LIFETIME",
    );
    passes(
        "struct Pair { i32 left; i32 right; } void f(&mut Pair pair) { auto view = &mut pair.left; }",
    );
}

#[test]
fn generic_aliases_shadowing_and_loop_reuse_preserve_place_identity() {
    passes(
        "struct Pair<T> { T left; T right; } type IntPair = Pair<i32>; i32 f(IntPair pair, bool c) { while (c) { auto first = &mut pair.left; auto second = &mut pair.right; *first += *second; } return pair.left; }",
    );
    passes(
        "struct Pair { i32 left; i32 right; } void f(Pair pair) { auto first = &mut pair.left; { Pair pair = Pair { left: 1, right: 2 }; auto second = &mut pair.left; *second = *first; } }",
    );
}

#[test]
fn exclusive_loan_access_and_move_transfer_keep_the_reference_unique() {
    passes(
        "i32 f() { i32 value = 1; { auto first = &mut value; auto second = move first; *second += 1; *second = *second + 1; } return value; }",
    );
    fails(
        "void f() { i32 value = 1; auto first = &mut value; auto second = first; }",
        "E-MOVE-EXPLICIT",
    );
    fails(
        "void f() { i32 value = 1; auto first = &mut value; auto second = &mut value; *first = 2; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "i32 f() { i32 value = 1; auto editor = &mut value; return value + *editor; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn call_arguments_hold_temporary_loans_and_release_them_after_a_known_call() {
    fails(
        "void use(&i32 first, &mut i32 second) {} void f() { i32 value = 0; use(&value, &mut value); }",
        "E-BORROW-CONFLICT",
    );
    passes(
        "void use(&mut i32 value) { *value += 1; } i32 f() { i32 value = 0; use(&mut value); use(&mut value); return value; }",
    );
    passes(
        "i32 read(&mut i32 value) { return *value; } void use(i32 first, &mut i32 second) {} void f() { i32 value = 0; use(read(&mut value), &mut value); }",
    );
}

#[test]
fn a_destination_keeps_its_non_copy_reference_handle_alive_during_the_rhs() {
    fails(
        "i32 take(&mut i32 value) { return 1; } void f() { i32 value = 0; auto editor = &mut value; *(editor) = take(move editor); }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn escaping_local_storage_and_returning_local_addresses_are_rejected() {
    fails(
        "i32 f() { &i32 view; { i32 value = 1; view = &value; } return *view; }",
        "E-BORROW-LIFETIME",
    );
    fails(
        "&i32 f() { i32 value = 1; return &value; }",
        "E-BORROW-RETURN",
    );
    passes("&i32 f(&i32 value) { return value; }");
    passes("&mut i32 f(&mut i32 value) { return move value; }");
}

#[test]
fn loop_exit_cleanup_releases_iteration_borrows() {
    passes(
        "i32 f() { i32 value = 0; while (true) { auto editor = &mut value; *editor = 1; break; } return value; }",
    );
    passes(
        "i32 f(bool c) { i32 value = 0; while (c) { auto editor = &mut value; *editor += 1; continue; } return value; }",
    );
}

#[test]
fn unsupported_reference_sensitive_cases_have_explicit_analysis_gaps() {
    let compilation = fails(
        "extern \"C\" { void retain(&i32 value); } void f() { i32 value = 0; retain(&value); }",
        "E-FRONTEND-STAGE",
    );
    assert!(
        compilation
            .local_analysis
            .as_ref()
            .unwrap()
            .functions
            .iter()
            .any(|function| !function.local_complete
                && function
                    .findings
                    .iter()
                    .any(|finding| finding.assessment == Assessment::NotAnalyzed))
    );
    passes("void f() { i32 value = 0; auto first = &mut value; auto next = &*first; }");
    fails(
        "&'static i32 f(&i32 value) { return value; }",
        "E-REGION-RETURN",
    );
}

#[test]
fn a_user_function_named_free_does_not_manufacture_a_heap_release_effect() {
    passes("void free(&i32 value) {} i32 f() { i32 value = 1; free(&value); return value; }");
}

#[test]
fn an_invalid_rhs_does_not_establish_the_destination() {
    let compilation = fails(
        "void take<T>(T value) {} void f<T>(T value) { take(move value); T bad = move value; T next = move bad; }",
        "E-MOVE-USE",
    );
    let source = compilation.sources.files()[0].text();
    let report = compilation.local_analysis.as_ref().unwrap();
    assert!(
        report
            .functions
            .iter()
            .flat_map(|function| &function.findings)
            .any(
                |finding| matches!(finding.predicate, Predicate::Available(_))
                    && finding.assessment == Assessment::NotEstablished
                    && &source[finding.span.start as usize..finding.span.end as usize] == "bad"
            )
    );
}

#[test]
fn rvalue_index_evaluation_is_left_to_right_and_not_duplicated() {
    let source = "i32[1] array(&mut i32 count) { *count += 1; return [42]; } usize next(&mut i32 count) { *count += 1; return 0; } i32 f() { i32 count = 0; return array(&mut count)[next(&mut count)]; }";
    let (compilation, _) = passes(source);
    let function = compilation
        .local_analysis
        .as_ref()
        .unwrap()
        .functions
        .last()
        .unwrap();
    let count = function
        .findings
        .iter()
        .filter(|finding| {
            matches!(finding.predicate, Predicate::NoLoanConflict(_))
                && &source[finding.span.start as usize..finding.span.end as usize] == "&mut count"
        })
        .count();
    assert_eq!(count, 2);
}

#[test]
fn local_evidence_is_acyclic_and_has_real_source_events() {
    let (mut compilation, program) = passes("i32 f() { i32 value = 1; return value; }");
    let report = compilation.local_analysis.as_mut().unwrap();
    let function = &mut report.functions[0];
    assert!(!function.cfg.events.is_empty());
    let index = function
        .evidence
        .iter()
        .position(|evidence| matches!(evidence, Evidence::LocalCheck { .. }))
        .unwrap();
    if let Evidence::LocalCheck { inputs, .. } = &mut function.evidence[index] {
        inputs.push(local::EvidenceId(index as u32));
    }
    assert!(report.validate(&program).is_err());
}

#[test]
fn analysis_has_an_explicit_cfg_resource_limit() {
    let mut source = String::from("void f() {");
    for index in 0..2050 {
        source.push_str(&format!("i32 value{index} = 0;"));
    }
    source.push('}');
    fails(&source, "E-LOCAL-LIMIT");
}

#[test]
fn repeated_checks_replace_the_old_report_after_new_parse_errors() {
    let (mut compilation, _) = passes("i32 f() { return 1; }");
    let file = compilation
        .sources
        .add("bad.cavo", "void bad( {".into())
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check().is_none());
    assert!(compilation.local_analysis.is_none());
}

#[test]
fn invalid_hir_is_rejected_before_local_lowering() {
    let (_, mut program) = passes("i32 f(i32 value) { return value; }");
    program.functions[0].parameters[0] = hir::LocalId(u32::MAX);
    let mut diagnostics = Vec::new();
    let report = local::analyze(&mut program, &mut diagnostics);
    assert_eq!(report.verdict, Verdict::Rejected);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-LOCAL-INTERNAL")
    );
}

#[test]
fn corrupt_cfg_operation_ids_are_not_valid_analysis_artifacts() {
    let (mut compilation, program) = passes("i32 f(i32 value) { return value; }");
    let report = compilation.local_analysis.as_mut().unwrap();
    report.functions[0].cfg.blocks[0].operations[0] = local::cfg::Operation::Parameter {
        local: hir::LocalId(u32::MAX),
        event: local::EventId(0),
    };
    assert!(report.validate(&program).is_err());
}

#[test]
fn place_arenas_reject_cycles_wrong_owners_and_duplicate_field_identities() {
    let (mut compilation, program) = passes(
        "struct Pair { i32 left; i32 right; } void f(Pair pair) { auto first = &pair.left; auto second = &pair.right; }",
    );
    let report = compilation.local_analysis.as_mut().unwrap();
    let places = &mut report.functions[0].places;
    let index = places.iter().position(|p| p.projection.is_some()).unwrap();
    let original = places[index];
    places[index].projection.as_mut().unwrap().base = local::PlaceId(index as u32);
    assert!(report.validate(&program).is_err());
    report.functions[0].places[index] = original;
    report.functions[0].places[index].owner = hir::LocalId(u32::MAX);
    assert!(report.validate(&program).is_err());
    report.functions[0].places[index] = original;
    report.functions[0].places.push(original);
    assert!(report.validate(&program).is_err());
    report.functions[0].places.pop();
    report.validate(&program).unwrap();
}

#[test]
fn no_loan_conflict_evidence_requires_a_valid_place_id() {
    let (mut compilation, program) = passes("void f(i32 value) { auto view = &value; }");
    let report = compilation.local_analysis.as_mut().unwrap();
    let function = &mut report.functions[0];
    let finding = function
        .findings
        .iter_mut()
        .find(|finding| matches!(finding.predicate, Predicate::NoLoanConflict(_)))
        .unwrap();
    let invalid = Predicate::NoLoanConflict(local::PlaceId(u32::MAX));
    finding.predicate = invalid;
    if let Evidence::LocalCheck { predicate, .. } =
        &mut function.evidence[finding.evidence.0 as usize]
    {
        *predicate = invalid;
    }
    assert!(report.validate(&program).is_err());
}

#[test]
fn transformed_unknown_fields_do_not_establish_disjoint_places() {
    let (_, mut program) = passes(
        "struct Pair { i32 left; i32 right; } void f(Pair pair) { auto view = &pair.left; }",
    );
    let function = &mut program.functions[0];
    let field = function
        .expressions
        .iter_mut()
        .find(|expression| matches!(expression.kind, hir::ExprKind::Field { .. }))
        .unwrap();
    if let hir::ExprKind::Field { index, .. } = &mut field.kind {
        *index = u32::MAX;
    }
    let mut diagnostics = Vec::new();
    let report = local::analyze(&mut program, &mut diagnostics);
    assert_eq!(report.verdict, Verdict::Rejected);
    assert!(!report.functions[0].local_complete);
    assert!(diagnostics.iter().any(|d| d.code == "E-FRONTEND-STAGE"));
}

#[test]
fn shared_expression_dags_are_bounded_without_approving_an_unfinished_result() {
    let (_, mut program) = passes("i32 f(i32 value) { return value; }");
    let function = &mut program.functions[0];
    let statement = function.body.statements[0];
    let hir::StmtKind::Return(Some(mut expression)) =
        function.statements[statement.0 as usize].kind
    else {
        panic!()
    };
    let span = function.expressions[expression.0 as usize].span;
    for _ in 0..20 {
        let next = hir::ExprId(function.expressions.len() as u32);
        function.expressions.push(hir::Expr {
            kind: hir::ExprKind::Binary {
                op: cavo_compiler::syntax::ast::BinaryOp::Add,
                left: expression,
                right: expression,
            },
            ty: function.result,
            span,
        });
        expression = next;
    }
    function.statements[statement.0 as usize].kind = hir::StmtKind::Return(Some(expression));
    program.validate().unwrap();
    let mut diagnostics = Vec::new();
    let report = local::analyze(&mut program, &mut diagnostics);
    assert_eq!(report.verdict, Verdict::Rejected);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-LOCAL-LIMIT")
    );
    assert!(!report.functions[0].local_complete);
    assert!(report.functions[0].findings.is_empty());
}

#[test]
fn cyclic_structural_type_entries_are_rejected_before_substitution() {
    let (_, mut program) = passes("struct Node { ptr<Node> next; } void f() {}");
    let next = cavo_compiler::types::TyId(program.types.values().len() as u32);
    let cyclic = program.types.intern(cavo_compiler::types::Ty::Reference {
        region: cavo_compiler::types::Region::Infer(999),
        mutable: false,
        inner: next,
    });
    assert_eq!(cyclic, next);
    program.records[0].fields[0].ty = cyclic;
    assert!(program.validate().is_err());
    let mut diagnostics = Vec::new();
    assert_eq!(
        local::analyze(&mut program, &mut diagnostics).verdict,
        Verdict::Rejected
    );
}

#[test]
fn deeply_nested_transformed_field_types_do_not_recurse_without_a_bound() {
    let (_, mut program) = passes("struct Record { i32 value; } void f() {}");
    let mut ty = program.records[0].fields[0].ty;
    for _ in 0..4096 {
        ty = program.types.intern(cavo_compiler::types::Ty::Array {
            inner: ty,
            length: 1,
        });
    }
    program.records[0].fields[0].ty = ty;
    program.validate().unwrap();
    let mut diagnostics = Vec::new();
    let report = local::analyze(&mut program, &mut diagnostics);
    assert_eq!(report.verdict, Verdict::Undetermined);
    assert!(!report.not_analyzed.is_empty());
}

#[test]
fn rhs_borrows_are_active_when_the_destination_is_written() {
    fails(
        "struct Node { &Node next; } void f(Node value) { value.next = &value; }",
        "E-BORROW-CONFLICT",
    );
    fails(
        "struct Node { &Node next; } void f(Node value) { value = Node { next: &value }; }",
        "E-BORROW-CONFLICT",
    );
}

#[test]
fn deeply_nested_transformed_conditions_and_statements_are_bounded() {
    let (_, mut program) = passes("void f() { if (true) {} }");
    let function = &mut program.functions[0];
    let statement = function.body.statements[0];
    let hir::StmtKind::If { mut condition, .. } = function.statements[statement.0 as usize].kind
    else {
        panic!()
    };
    let span = function.expressions[condition.0 as usize].span;
    for _ in 0..4096 {
        let next = hir::ExprId(function.expressions.len() as u32);
        function.expressions.push(hir::Expr {
            kind: hir::ExprKind::Group(condition),
            ty: cavo_compiler::types::TyId::BOOL,
            span,
        });
        condition = next;
    }
    if let hir::StmtKind::If {
        condition: current, ..
    } = &mut function.statements[statement.0 as usize].kind
    {
        *current = condition;
    }
    program.validate().unwrap();
    let mut diagnostics = Vec::new();
    assert_eq!(
        local::analyze(&mut program, &mut diagnostics).verdict,
        Verdict::Rejected
    );
    assert!(diagnostics.iter().any(|d| d.code == "E-LOCAL-LIMIT"));

    let (_, mut program) = passes("void f() {}");
    let function = &mut program.functions[0];
    let mut statements = Vec::new();
    for _ in 0..4096 {
        let id = hir::StmtId(function.statements.len() as u32);
        function.statements.push(hir::Stmt {
            kind: hir::StmtKind::Block(hir::Block {
                statements,
                span: function.body.span,
            }),
            span: function.body.span,
        });
        statements = vec![id];
    }
    function.body.statements = statements;
    program.validate().unwrap();
    let mut diagnostics = Vec::new();
    assert_eq!(
        local::analyze(&mut program, &mut diagnostics).verdict,
        Verdict::Rejected
    );
    assert!(diagnostics.iter().any(|d| d.code == "E-LOCAL-LIMIT"));
}

#[test]
fn temporary_origin_limits_reject_without_discarding_loans() {
    let elements = std::iter::repeat_n("&value", 65)
        .collect::<Vec<_>>()
        .join(",");
    let source = format!("void f() {{ i32 value = 1; auto views = [{elements}]; }}");
    let compilation = fails(&source, "E-LOCAL-LIMIT");
    assert!(!compilation.local_analysis.as_ref().unwrap().functions[0].local_complete);
    passes(
        "i32 f() { i32 value = 1; auto view = &value; auto views = [view; 1000]; return *view; }",
    );
}
