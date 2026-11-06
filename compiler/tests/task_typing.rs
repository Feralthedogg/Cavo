use cavo_compiler::{Compilation, mir};

const CORE: &str = r#"
@lang(result) enum Outcome<T, E> { Ok(T), Err(E) }
@lang(task) struct Work<'scope, T> {}
@lang(spawn_error) struct Admission<F> { F capture; }
@lang(task_error) enum Fault { Cancelled, Panicked }
impl<'scope, T> Work<'scope, T> {
    @intrinsic(task_join) Outcome<T, Fault> join(Self self);
    @intrinsic(task_cancel) void cancel(&Self self);
    @intrinsic(task_ignore) void ignore_result(Self self);
}
"#;

fn parse(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("tasks.cavo", format!("{CORE}\n{source}"))
        .unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) -> (Compilation, cavo_compiler::hir::Program, mir::Program) {
    let mut compilation = parse(source);
    let (hir, mir) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, hir, mir)
}

fn rejected(source: &str, code: &str) {
    let mut compilation = parse(source);
    assert!(compilation.check_mir().is_none(), "accepted {source}");
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn typed_spawn_preserves_admission_errors_and_scope_drain_edges() {
    let (_, _, program) = checked(
        "i32 child(i32 n) { return n + 1; } void parent() { scope { auto admission = spawn child(4); } }",
    );
    assert!(
        program
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .any(|b| matches!(b.terminator, mir::Terminator::Spawn { .. }))
    );
    assert!(
        program
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .any(|b| matches!(b.terminator, mir::Terminator::TaskDrain { .. }))
    );
}

#[test]
fn join_consumes_the_typed_handle_and_returns_a_typed_result() {
    checked(
        "i32 child(i32 n) { return n; } i32 parent() { scope { auto admission = spawn child(4); return match (move admission) { Outcome::Ok(task) => match task.join() { Outcome::Ok(n) => n, Outcome::Err(_) => 0 }, Outcome::Err(_) => 0 }; } }",
    );
}

#[test]
fn borrowed_captures_stay_live_until_the_scope_barrier() {
    checked(
        "i32 child(&i32 n) { return *n; } void parent() { i32 n = 7; scope { auto admission = spawn child(&n); } n = 8; }",
    );
    rejected(
        "i32 child(&i32 n) { return *n; } void parent() { i32 n = 7; scope { auto admission = spawn child(&n); n = 8; } }",
        "E-MIR-BORROW",
    );
}

#[test]
fn tasks_require_scope_and_nontransferable_values_are_rejected() {
    rejected(
        "i32 child() { return 1; } void f() { auto x = spawn child(); }",
        "E-TASK-SCOPE",
    );
    rejected(
        "@task_bound struct Guard {} void child(Guard value) {} void f() { scope { Guard g = Guard {}; auto x = spawn child(g); } }",
        "E-TASK-TRANSFER",
    );
}

#[test]
fn removing_a_drain_cannot_release_registry_storage() {
    let (_, mut hir, mut program) =
        checked("void child() {} void parent() { scope { auto x = spawn child(); } }");
    let body = program
        .functions
        .iter_mut()
        .find(|body| {
            body.blocks
                .iter()
                .any(|b| matches!(b.terminator, mir::Terminator::Spawn { .. }))
        })
        .unwrap();
    for block in &mut body.blocks {
        if let mir::Terminator::TaskDrain { next, .. } = block.terminator {
            block.terminator = mir::Terminator::Goto(next);
        }
    }
    let error = program.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("drain"), "{error}");
}

#[test]
fn join_releases_its_child_loan_and_preserves_other_children() {
    checked(
        "i32 child(&i32 n) { return *n; } void parent() { i32 n = 7; scope { auto receipt = spawn child(&n); match (move receipt) { Outcome::Ok(task) => { auto result = task.join(); n = 8; }, Outcome::Err(_) => {} }; } }",
    );
    rejected(
        "i32 child(&i32 n) { return *n; } void parent() { i32 n = 7; scope { auto first = spawn child(&n); auto second = spawn child(&n); match (move first) { Outcome::Ok(task) => { auto result = task.join(); n = 8; }, Outcome::Err(_) => {} }; } }",
        "E-MIR-BORROW",
    );
}

#[test]
fn task_observation_cannot_be_fabricated_reused_or_moved_to_another_task() {
    rejected(
        "void f() { Work<'static, i32> task = Work {}; }",
        "E-TASK-CONSTRUCT",
    );
    rejected(
        "i32 child() { return 1; } void f() { scope { auto r = spawn child(); match (move r) { Outcome::Ok(task) => { auto a = task.join(); auto b = task.join(); }, Outcome::Err(_) => {} }; } }",
        "E-MOVE-USE",
    );
    rejected(
        "@thread_bound i32 child() { return 1; } void f() { scope { auto r = spawn child(); } }",
        "E-CALLABLE-IDENTITY",
    );
}

#[test]
fn trusted_transfer_contracts_keep_their_assumptions_and_cannot_override_identity() {
    let traits = "@lang(send) trait Send {} @lang(sync) trait Sync {} @lang(task_transfer) trait TaskTransfer {} @lang(suspend_safe) trait SuspendSafe {}";
    let wrapper = "struct Owner { ptr<i32> address; } contract impl Send for Owner because \"owner migrates with its allocation\"; contract impl TaskTransfer for Owner because \"unique ownership leaves the parent\"; contract impl SuspendSafe for Owner because \"owner remains valid while parked\";";
    let (compilation, _, _) = checked(&format!(
        "{traits} {wrapper} void child(Owner owner) {{}} void parent(Owner owner) {{ scope {{ auto r = spawn child(move owner); }} }}"
    ));
    assert!(
        !compilation
            .mir_analysis
            .as_ref()
            .unwrap()
            .tasks
            .assumptions
            .is_empty()
    );
    rejected(
        &format!(
            "{traits} @task_bound struct Guard {{}} contract impl TaskTransfer for Guard because \"incorrect identity override\"; void child(Guard g) {{}} void parent() {{ scope {{ auto r = spawn child(Guard {{}}); }} }}"
        ),
        "E-TASK-TRANSFER",
    );
}

#[test]
fn rejected_admission_returns_an_affine_callable_capture() {
    checked(
        "i32 child(i32 n) { return n; } i32 parent() { scope { auto receipt = spawn child(4); return match (move receipt) { Outcome::Ok(task) => match task.join() { Outcome::Ok(n) => n, Outcome::Err(_) => 0 }, Outcome::Err(error) => (move error.capture)() }; } }",
    );
}

#[test]
fn a_joined_reference_keeps_its_capture_origin() {
    rejected(
        "&i32 child(&i32 n) { return n; } &'static i32 parent() { i32 n = 1; scope { auto receipt = spawn child(&n); return match (move receipt) { Outcome::Ok(task) => match task.join() { Outcome::Ok(value) => value, Outcome::Err(_) => &n }, Outcome::Err(_) => &n }; } }",
        "E-MIR-BORROW",
    );
}

#[test]
fn cancellation_and_discarding_observation_do_not_release_child_loans() {
    for operation in ["task.cancel();", "task.ignore_result();"] {
        rejected(
            &format!(
                "i32 child(&i32 n) {{ return *n; }} void parent() {{ i32 n = 1; scope {{ auto receipt = spawn child(&n); match (move receipt) {{ Outcome::Ok(task) => {{ {operation} n = 2; }}, Outcome::Err(_) => {{}} }}; }} }}"
            ),
            "E-MIR-BORROW",
        );
    }
}

#[test]
fn hir_rejects_a_spawn_retargeted_to_a_missing_scope() {
    let (_, mut hir, _) =
        checked("void child() {} void parent() { scope { auto r = spawn child(); } }");
    let expression = hir
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.expressions)
        .find(|e| matches!(e.kind, cavo_compiler::hir::ExprKind::Spawn { .. }))
        .unwrap();
    if let cavo_compiler::hir::ExprKind::Spawn { scope, .. } = &mut expression.kind {
        *scope = u32::MAX;
    }
    assert!(hir.validate().is_err());
}

#[test]
fn generic_spawn_is_rechecked_after_concrete_instantiation() {
    let mut compilation = parse(
        "@lang(send) trait Send {} @lang(task_transfer) trait TaskTransfer {} T child<T: Send + TaskTransfer>(T n) { return move n; } void parent<T: Send + TaskTransfer>(T n) { scope { auto receipt = spawn child::<T>(move n); } } void main() { parent::<i32>(2); }",
    );
    assert!(
        compilation.check_monomorphized().is_some(),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn module_export_cannot_hide_an_unchecked_worker_frame() {
    use cavo_compiler::modular::capsule::{Source, build};
    let module = build(vec![Source {
        name: "library.cavo".into(),
        text: "module library; @thread_bound struct Affine { i32 value; } void opaque(); pub i32 child() { Affine owner = Affine { value: 1 }; opaque(); return owner.value; }".into(),
    }]).unwrap();
    let mut compilation =
        parse("import library; void parent() { scope { auto receipt = spawn library::child(); } }");
    module.load_into(&mut compilation).unwrap();
    assert!(compilation.check_mir().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-TASK-LIVE"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn partial_initialization_does_not_skip_worker_frame_checks() {
    rejected(
        "@thread_bound struct Local { i32 n; } void child() {} void parent() { Local value; value.n = 1; scope { auto receipt = spawn child(); } i32 n = value.n; }",
        "E-TASK-LIVE",
    );
}
