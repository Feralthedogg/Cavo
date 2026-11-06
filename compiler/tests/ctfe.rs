use cavo_compiler::{Compilation, ctfe, hir};

fn compilation(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("ctfe.cavo", source.into()).unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = compilation(source);
    let program = compilation.check_types();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    (compilation, program.expect("typed constant program"))
}

fn definition(compilation: &Compilation, program: &hir::Program, name: &str) -> hir::DefId {
    hir::DefId(
        program
            .definitions
            .iter()
            .position(|definition| compilation.symbols.get(definition.name) == name)
            .unwrap() as u32,
    )
}

fn value(compilation: &Compilation, program: &hir::Program, name: &str) -> ctfe::Value {
    ctfe::evaluate_global(
        program,
        definition(compilation, program, name),
        ctfe::Limits::default(),
    )
    .unwrap()
}

fn rejects(source: &str, code: &str) {
    let mut compilation = compilation(source);
    assert!(compilation.check_types().is_none(), "accepted {source}");
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == code),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn forward_constants_and_const_functions_supply_array_lengths() {
    let (compilation, program) = checked(
        "const usize SIZE = twice(BASE); const usize BASE = 5; const usize twice(usize value) { return value * 2; } void f() { byte[SIZE] data = [0; SIZE]; const usize MORE = SIZE + 2; byte[MORE] extra = [0; MORE]; }",
    );
    assert_eq!(
        value(&compilation, &program, "SIZE").usize_value(),
        Some(10)
    );
    let function = program
        .functions
        .iter()
        .find(|function| {
            compilation
                .symbols
                .get(program.definitions[function.definition.0 as usize].name)
                == "f"
        })
        .unwrap();
    assert!(function.locals.iter().any(|local| matches!(
        program.types.get(local.ty),
        cavo_compiler::types::Ty::Array { length: 12, .. }
    )));
}

#[test]
fn scalar_loops_and_decreasing_recursion_are_evaluated() {
    let (compilation, program) = checked(
        "const usize factorial(usize n) { if (n == 0) { return 1; } return n * factorial(n - 1); } const usize sum(usize n) { usize total = 0; for (usize i = 0; i < n; i += 1) { if (i == 2) { continue; } total += i; } return total; } const usize FACT = factorial(6); const usize SUM = sum(5);",
    );
    assert_eq!(
        value(&compilation, &program, "FACT").usize_value(),
        Some(720)
    );
    assert_eq!(value(&compilation, &program, "SUM").usize_value(), Some(8));
}

#[test]
fn unselected_value_dependencies_do_not_create_cycles_or_traps() {
    let (compilation, program) = checked(
        "const bool SELF = false && SELF; const bool SAFE = true || (1usize / 0usize == 0usize); const usize selected(bool take) { if (take) { return CYCLE; } return 7; } const usize CYCLE = selected(false);",
    );
    assert_eq!(value(&compilation, &program, "SELF").boolean(), Some(false));
    assert_eq!(value(&compilation, &program, "SAFE").boolean(), Some(true));
    assert_eq!(
        value(&compilation, &program, "CYCLE").usize_value(),
        Some(7)
    );
    rejects("const bool BAD = false && missing;", "E-NAME-UNKNOWN");
}

#[test]
fn active_value_cycles_and_repeated_call_queries_are_diagnosed() {
    rejects("const usize A = B; const usize B = A;", "E-CONST-CYCLE");
    rejects(
        "const usize same(usize value) { return same(value); } const usize A = same(1);",
        "E-CONST-CYCLE",
    );
}

#[test]
fn target_checked_arithmetic_rejects_overflow_zero_division_and_shifts() {
    for source in [
        "const u8 BAD = 255u8 + 1u8;",
        "const usize BAD = 1usize / 0usize;",
        "const i8 BAD = -128i8 / -1i8;",
        "const i8 BAD = -128i8 % -1i8;",
        "const usize BAD = 1usize << 64usize;",
        "const usize BAD = usize::MAX + 1usize;",
    ] {
        rejects(source, "E-CONST-EVAL");
    }
}

#[test]
fn scalar_contracts_observe_actual_arguments_old_and_result() {
    let source = "const usize increment(usize value) requires value < usize::MAX ensures result == old(value) + 1 { value += 1; return value; } const usize GOOD = increment(41);";
    let (compilation, program) = checked(source);
    assert_eq!(
        value(&compilation, &program, "GOOD").usize_value(),
        Some(42)
    );
    rejects(
        "const usize f(usize n) requires n != 0 { return n; } const usize BAD = f(0);",
        "E-CONST-CONTRACT",
    );
    rejects(
        "const usize f(usize n) ensures result > old(n) { return n; } const usize BAD = f(2);",
        "E-CONST-CONTRACT",
    );
}

#[test]
fn align_up_checks_preconditions_before_target_arithmetic() {
    let function = "const usize align_up(usize value, usize alignment) requires alignment != 0 && (alignment & (alignment - 1)) == 0 && value <= usize::MAX - (alignment - 1) { return (value + (alignment - 1)) & ~(alignment - 1); }";
    let (compilation, program) = checked(&format!(
        "{function} const usize A = align_up(usize::MAX - 63, 64); const usize B = align_up(usize::MAX, 1);"
    ));
    assert_eq!(
        value(&compilation, &program, "A").usize_value(),
        Some(u64::MAX - 63)
    );
    assert_eq!(
        value(&compilation, &program, "B").usize_value(),
        Some(u64::MAX)
    );
    for arguments in ["1, 0", "1, 3", "usize::MAX, 64"] {
        rejects(
            &format!("{function} const usize BAD = align_up({arguments});"),
            "E-CONST-CONTRACT",
        );
    }
}

#[test]
fn optional_runtime_calls_keep_runtime_trap_and_contract_behavior() {
    checked("const usize trap() { return 1usize / 0usize; } usize f() { return trap(); }");
    checked(
        "const usize need(usize n) requires n != 0 { return n; } usize f() { return need(0); }",
    );
    rejects(
        "const usize need(usize n) requires n != 0 { return n; } const usize BAD = need(0);",
        "E-CONST-CONTRACT",
    );
}

#[test]
fn static_assert_is_a_declaration_check_not_a_runtime_parameter_test() {
    checked(
        "const usize N = 8; static_assert(N > 0, \"positive\"); void f() { const usize M = N + 1; static_assert(M == 9); }",
    );
    rejects("static_assert(false, \"must hold\");", "E-CONST-ASSERT");
    rejects(
        "const usize f(usize n) { static_assert(n > 0); return n; }",
        "E-CONST-CONTEXT",
    );
}

#[test]
fn runtime_and_shadowed_bindings_cannot_become_array_lengths() {
    rejects(
        "usize runtime() { return 4; } void f() { const usize N = runtime(); byte[N] data; }",
        "E-CONST-CONTEXT",
    );
    rejects(
        "const usize N = 4; void f(usize N) { byte[N] data; }",
        "E-CONST-CONTEXT",
    );
    checked("usize runtime() { return 4; } void f() { const usize N = runtime(); }");
}

#[test]
fn non_const_calls_and_forbidden_effects_are_rejected_even_in_unselected_branches() {
    rejects(
        "usize ordinary() { return 1; } const usize BAD = ordinary();",
        "E-CONST-CONTEXT",
    );
    rejects(
        "usize ordinary() { return 1; } const usize f() { if (false) { return ordinary(); } return 2; }",
        "E-CONST-CONTEXT",
    );
    rejects("const f64 BAD = 1.0 + 2.0;", "E-CONST-CONTEXT");
}

#[test]
fn required_constants_have_explicit_fuel_and_data_limits() {
    rejects(
        "const usize spin() { while (true) {} return 0; } const usize BAD = spin();",
        "E-CONST-LIMIT",
    );
    rejects("const byte[1000000] BAD = [0; 1000000];", "E-CONST-LIMIT");
}

#[test]
fn cache_hits_replay_logical_fuel_cost() {
    let (compilation, program) = checked(
        "const usize plus(usize x) { return x + 1; } const usize SAME = plus(1) + plus(1); const usize DIFFERENT = plus(1) + plus(2);",
    );
    let minimum = |name| {
        let definition = definition(&compilation, &program, name);
        (1..100)
            .find(|&fuel| {
                ctfe::evaluate_global(
                    &program,
                    definition,
                    ctfe::Limits {
                        fuel,
                        ..ctfe::Limits::default()
                    },
                )
                .is_ok()
            })
            .unwrap()
    };
    assert_eq!(minimum("SAME"), minimum("DIFFERENT"));
}

#[test]
fn target_width_is_explicit_and_malformed_constant_ir_is_rejected() {
    let (compilation, mut program) =
        checked("const usize BIG = 4294967296; const usize plus(usize x) { return x + 1; }");
    let target32 = ctfe::Limits {
        pointer_bits: 32,
        ..ctfe::Limits::default()
    };
    assert_eq!(
        ctfe::evaluate_global(
            &program,
            definition(&compilation, &program, "BIG"),
            target32
        )
        .unwrap_err()
        .code,
        "E-CONST-EVAL"
    );
    let body = program.constants.functions.values_mut().next().unwrap();
    body.expressions[0].kind = ctfe::ExprKind::Local(u32::MAX);
    assert!(program.constants.validate(&program).is_err());
}

#[test]
fn primitive_bounds_follow_the_evaluation_target() {
    let (compilation, program) = checked("const usize MAX = usize::MAX;");
    let target32 = ctfe::Limits {
        pointer_bits: 32,
        ..ctfe::Limits::default()
    };
    let value = ctfe::evaluate_global(
        &program,
        definition(&compilation, &program, "MAX"),
        target32,
    )
    .unwrap();
    assert_eq!(value.usize_value(), Some(u32::MAX.into()));
}
