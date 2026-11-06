use cavo_compiler::{
    Compilation, external, hir, mir,
    mir::effects::{self, Boundedness, Effect, Unknown},
};

fn lowered(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("effects.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let mut hir = compilation.check_types().unwrap_or_else(|| {
        panic!("{:#?}", compilation.diagnostics);
    });
    let mir = mir::lower(&mut hir).unwrap();
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

fn definition(compilation: &Compilation, hir: &hir::Program, name: &str) -> hir::DefId {
    hir.definitions
        .iter()
        .position(|definition| compilation.symbols.get(definition.name) == name)
        .map(|index| hir::DefId(index as u32))
        .unwrap()
}

#[test]
fn finite_source_calls_are_bounded_and_fatal_traps_are_not_panics() {
    let (compilation, hir, mir) = lowered(
        "@nosuspend @nocancel @nopanic @noalloc i32 caller(i32 x) { return leaf(x); } i32 leaf(i32 x) { return x + 1; }",
    );
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    assert!(report.violations.is_empty());
    for summary in &report.functions {
        assert_eq!(summary.bounded, Boundedness::Established);
        assert!(summary.cleanup_safe());
        assert!(summary.effects.is_empty());
        assert!(summary.may_abort);
        assert!(summary.assumptions.is_empty());
    }
}

#[test]
fn recursive_components_and_loops_cannot_establish_cleanup_boundedness() {
    let (compilation, hir, mir) = lowered(
        "void caller() { a(); } void a() { b(); } void b() { a(); } void spin(bool run) { while (run) {} }",
    );
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    for summary in &report.functions {
        assert_eq!(summary.bounded, Boundedness::MayDiverge);
        assert!(!summary.cleanup_safe());
    }
}

#[test]
fn declaration_bounds_do_not_approve_unknown_indirect_effects() {
    let (compilation, hir, mir) = lowered(
        "@nosuspend void invoke(fn() -> void callback) { callback(); } void caller(fn() -> void callback) { invoke(callback); }",
    );
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    let invoke = definition(&compilation, &hir, "invoke");
    assert_eq!(report.violations.len(), 1);
    assert_eq!(report.violations[0].definition, invoke);
    for summary in &report.functions {
        // The implementation retains its uncertainty; callers use the stable
        // declaration. The failed refinement still rejects the whole program.
        assert_eq!(
            summary.unknown.contains(&Unknown::IndirectCall),
            summary.definition == invoke
        );
        assert_eq!(summary.bounded, Boundedness::Unknown);
        assert!(!summary.cleanup_safe());
    }
}

#[test]
fn effect_upper_bounds_are_checked_instead_of_becoming_evidence() {
    let (compilation, hir, mir) =
        lowered("extern \"C\" { void native(); } @effects() void caller() { native(); }");
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    assert_eq!(report.violations.len(), 1);
    let caller = report
        .get(definition(&compilation, &hir, "caller"))
        .unwrap();
    assert!(caller.effects.contains(&Effect::Ffi));
    assert!(caller.unknown.contains(&Unknown::ExternalCall));
    assert!(!caller.cleanup_safe());
}

fn external_assumption(
    function: hir::DefId,
    span: cavo_compiler::source::Span,
) -> external::SummaryReport {
    let digest = external::Summaries::digest("effect fixture");
    external::SummaryReport {
        schema: 2,
        assumption: external::AssumptionId(7),
        id: "effects".into(),
        version: "1".into(),
        digest,
        declared_artifact: digest,
        function,
        signature: digest,
        source: span,
        status: external::SummaryStatus::Assumed,
        not_established: Vec::new(),
        returns: Vec::new(),
        effects: external::Effects {
            no_retain: Some(true),
            no_free: Some(true),
            no_callback: Some(true),
            no_unwind: Some(true),
            no_suspend: Some(true),
            no_block: Some(true),
            no_allocate: Some(true),
            preserves_validity: Some(true),
            reads: Some(Vec::new()),
            writes: Some(Vec::new()),
            stores: Some(Vec::new()),
        },
    }
}

#[test]
fn trusted_external_absence_stays_assumed_and_does_not_prove_bounded_cleanup() {
    let (compilation, hir, mir) = lowered(
        "extern \"C\" { void native(); } void middle() { native(); } void caller() { middle(); }",
    );
    let native = definition(&compilation, &hir, "native");
    let assumption = external_assumption(native, hir.definitions[native].span);
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[assumption]).unwrap();
    for summary in &report.functions {
        assert!(summary.assumptions.contains(&external::AssumptionId(7)));
        assert!(summary.unknown.contains(&Unknown::ExternalCall));
        assert_eq!(summary.bounded, Boundedness::Unknown);
        assert!(!summary.cleanup_safe());
    }
}

#[test]
fn opaque_drop_glue_is_not_a_proven_pure_cleanup_operation() {
    let (compilation, hir, mir) = lowered("void discard<T>(T value) {}");
    let report = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    assert!(report.functions[0].unknown.contains(&Unknown::DropGlue));
    assert!(!report.functions[0].cleanup_safe());
}

#[test]
fn source_cleanup_candidates_are_order_independent_and_reject_recursive_helpers() {
    let (compilation, mut hir, _) = lowered(
        "void forward(&mut i32 value) { leaf(value); } void leaf(&mut i32 value) { *value = 1; } void recursive() { recursive(); }",
    );
    let candidates = effects::cleanup_candidates(&mut hir).unwrap();
    assert!(candidates.allows(definition(&compilation, &hir, "forward")));
    assert!(candidates.allows(definition(&compilation, &hir, "leaf")));
    assert!(!candidates.allows(definition(&compilation, &hir, "recursive")));
}

#[test]
fn transformed_cleanup_calls_must_reestablish_bounded_effects() {
    let (compilation, mut hir, mut mir) = lowered(
        "void leaf() {} void spin() { while (true) {} } void caller() { defer { leaf(); } }",
    );
    let caller = definition(&compilation, &hir, "caller");
    let spin = definition(&compilation, &hir, "spin");
    let before = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    assert!(before.violations.is_empty());
    let body = mir
        .functions
        .iter_mut()
        .find(|body| body.definition == caller)
        .unwrap();
    let block = body
        .blocks
        .iter_mut()
        .find(|block| {
            block.cleanup.is_some() && matches!(block.terminator, mir::Terminator::Call { .. })
        })
        .unwrap();
    let mir::Terminator::Call { callee, .. } = &mut block.terminator else {
        unreachable!()
    };
    *callee = mir::Operand::Function {
        definition: spin,
        ty: hir.definitions[spin].ty,
    };
    mir.validate(&mut hir).unwrap();
    let after = effects::analyze(&mir, &hir, &compilation.symbols, &[]).unwrap();
    assert!(after.violations.iter().any(|violation| {
        violation.definition == caller && violation.message.contains("cleanup call")
    }));
}
