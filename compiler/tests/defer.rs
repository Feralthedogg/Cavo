use cavo_compiler::{Compilation, hir, mir};

fn parse(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("defer.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = parse(source);
    let result = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (hir, mir) = result.unwrap();
    (compilation, hir, mir)
}

fn body<'a>(
    compilation: &Compilation,
    hir: &hir::Program,
    mir: &'a mir::Program,
    name: &str,
) -> &'a mir::Body {
    mir.functions
        .iter()
        .find(|body| {
            compilation
                .symbols
                .get(hir.definitions[body.definition.0 as usize].name)
                == name
        })
        .unwrap()
}

fn call_name<'a>(
    compilation: &'a Compilation,
    hir: &hir::Program,
    callee: &mir::Operand,
) -> &'a str {
    let mir::Operand::Function { definition, .. } = callee else {
        panic!("direct test callee");
    };
    compilation
        .symbols
        .get(hir.definitions[definition.0 as usize].name)
}

/// Observe cleanup control flow only; call results and numeric execution are not
/// interpreted. The fixtures use direct calls and constant loop conditions.
fn calls_on_path(
    compilation: &Compilation,
    hir: &hir::Program,
    body: &mir::Body,
    failure: Option<mir::ExitKind>,
) -> Vec<String> {
    let mut block = body.entry;
    let mut calls = Vec::new();
    for _ in 0..512 {
        block = match &body.block(block).terminator {
            mir::Terminator::Goto(next) | mir::Terminator::Drop { next, .. } => *next,
            mir::Terminator::Call {
                callee,
                arguments,
                normal,
                panic,
                cancel,
                ..
            } => {
                let name = call_name(compilation, hir, callee);
                calls.push(format!("{name}:{arguments:?}"));
                match (name, failure) {
                    ("work", Some(mir::ExitKind::Panic)) => *panic,
                    ("work", Some(mir::ExitKind::Cancel)) => *cancel,
                    _ => *normal,
                }
            }
            mir::Terminator::Switch {
                condition:
                    mir::Operand::Constant {
                        value: hir::Constant::Bool(value),
                        ..
                    },
                yes,
                no,
            } => {
                if *value {
                    *yes
                } else {
                    *no
                }
            }
            mir::Terminator::Return | mir::Terminator::Resume(_) => return calls,
            other => panic!("unexpected test control flow: {other:?}"),
        };
    }
    panic!("defer path exceeded test budget");
}

#[test]
fn deferred_calls_run_in_reverse_registration_on_every_function_exit() {
    let (compilation, hir, mir) = checked(
        "void mark(i32 value) {} void work() {} i32 f() { defer { mark(1); } defer { mark(2); } work(); return 7; }",
    );
    let body = body(&compilation, &hir, &mir, "f");
    for failure in [
        None,
        Some(mir::ExitKind::Panic),
        Some(mir::ExitKind::Cancel),
    ] {
        let calls = calls_on_path(&compilation, &hir, body, failure);
        assert_eq!(calls.len(), 3);
        assert!(calls[0].starts_with("work:"));
        assert!(calls[1].contains("magnitude: 2"), "{calls:?}");
        assert!(calls[2].contains("magnitude: 1"), "{calls:?}");
    }
}

#[test]
fn deferred_mutation_is_lowered_only_into_cleanup_blocks() {
    let (compilation, hir, mir) = checked(
        "void set(&mut i32 value) { *value = 7; } void f() { i32 value = 0; defer { set(&mut value); } }",
    );
    let body = body(&compilation, &hir, &mir, "f");
    let mut cleanup_calls = 0;
    for block in &body.blocks {
        if let mir::Terminator::Call {
            callee,
            panic,
            cancel,
            ..
        } = &block.terminator
            && call_name(&compilation, &hir, callee) == "set"
        {
            cleanup_calls += 1;
            assert!(block.cleanup.is_some());
            assert!(matches!(
                body.block(*panic).terminator,
                mir::Terminator::Abort
            ));
            assert!(matches!(
                body.block(*cancel).terminator,
                mir::Terminator::Abort
            ));
        }
    }
    assert!(cleanup_calls > 0);
}

#[test]
fn defer_captures_keep_their_loans_live_until_cleanup() {
    let mut compilation = parse(
        "void read(i32 value) {} void f() { i32 value = 1; defer { read(value); } value = 2; }",
    );
    assert!(compilation.check().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.starts_with("E-BORROW")),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn break_runs_its_defer_before_leaving_the_loop_scope() {
    let (compilation, hir, mir) =
        checked("void mark(i32 value) {} void f() { while (true) { defer { mark(3); } break; } }");
    let calls = calls_on_path(
        &compilation,
        &hir,
        body(&compilation, &hir, &mir, "f"),
        None,
    );
    assert_eq!(calls.len(), 1);
    assert!(calls[0].contains("magnitude: 3"));
}

#[test]
fn continue_runs_cleanup_on_each_iteration() {
    let (compilation, hir, mir) = checked(
        "void mark(i32 value) {} void f() { while (true) { defer { mark(4); } continue; } }",
    );
    let body = body(&compilation, &hir, &mir, "f");
    let mut block = body.entry;
    let mut calls = 0;
    for _ in 0..128 {
        block = match &body.block(block).terminator {
            mir::Terminator::Goto(next) => *next,
            mir::Terminator::Switch { yes, .. } => *yes,
            mir::Terminator::Call { callee, normal, .. } => {
                assert_eq!(call_name(&compilation, &hir, callee), "mark");
                assert!(body.block(block).cleanup.is_some());
                calls += 1;
                if calls == 2 {
                    return;
                }
                *normal
            }
            other => panic!("unexpected loop cleanup: {other:?}"),
        };
    }
    panic!("continue did not execute its cleanup twice");
}

#[test]
fn cleanup_cannot_escape_or_contain_unbounded_control() {
    for deferred in ["return;", "while (true) {}", "break;", "continue;"] {
        let mut compilation = parse(&format!("void f() {{ defer {{ {deferred} }} }}"));
        assert!(compilation.check().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E-DEFER-CONTROL")
        );
    }
}

#[test]
fn public_lowering_rechecks_deferred_call_effects_after_hir_changes() {
    let mut compilation =
        parse("void leaf() {} void spin() { while (true) {} } void f() { defer { leaf(); } }");
    let mut hir = compilation.check_types().unwrap();
    let definition = |name| {
        hir.definitions
            .iter()
            .position(|definition| compilation.symbols.get(definition.name) == name)
            .map(|index| hir::DefId(index as u32))
            .unwrap()
    };
    let leaf = definition("leaf");
    let spin = definition("spin");
    for function in &mut hir.functions {
        for expression in &mut function.expressions {
            if let hir::ExprKind::Definition(target) = &mut expression.kind
                && *target == leaf
            {
                *target = spin;
            }
        }
    }
    hir.validate().unwrap();
    let error = mir::lower(&mut hir).unwrap_err();
    assert!(error.message.contains("bounded"), "{error}");
}

#[test]
fn nested_defer_is_registered_when_its_enclosing_cleanup_executes() {
    let (compilation, hir, mir) =
        checked("void mark(i32 value) {} void f() { defer { defer { mark(1); } mark(2); } }");
    let calls = calls_on_path(
        &compilation,
        &hir,
        body(&compilation, &hir, &mir, "f"),
        None,
    );
    assert_eq!(calls.len(), 2);
    assert!(calls[0].contains("magnitude: 2"));
    assert!(calls[1].contains("magnitude: 1"));
}

#[test]
fn early_return_restores_each_defers_declaring_scope_before_execution() {
    let (compilation, hir, mir) = checked(
        "void mark(i32 value) {} void f() { defer { mark(1); } { i32 later = 9; defer { mark(2); } return; } }",
    );
    let calls = calls_on_path(
        &compilation,
        &hir,
        body(&compilation, &hir, &mir, "f"),
        None,
    );
    assert_eq!(calls.len(), 2);
    assert!(calls[0].contains("magnitude: 2"));
    assert!(calls[1].contains("magnitude: 1"));
}

#[test]
fn prepared_return_provenance_survives_deferred_control_flow() {
    let helper = "&i32 keep(&i32 value, bool flag) { defer { if (flag) { i32 a = 1; } else { i32 b = 2; } } return value; }";
    let mut safe = parse(&format!(
        "{helper} i32 read(&i32 input, bool flag) {{ auto value = keep(input, flag); return *value; }}"
    ));
    assert!(safe.check().is_some(), "{:#?}", safe.diagnostics);
    let mut escaped = parse(&format!(
        "{helper} &i32 bad() {{ i32 local = 1; return keep(&local, true); }}"
    ));
    assert!(
        escaped.check().is_none(),
        "cleanup erased the return value's local-storage origin"
    );
    assert!(
        escaped.diagnostics.iter().any(|diagnostic| matches!(
            diagnostic.code,
            "E-BORROW-RETURN" | "E-REGION-RETURN" | "E-LIFETIME-RETURN"
        )),
        "{:#?}",
        escaped.diagnostics
    );
}
