use cavo_compiler::{
    Compilation, hir, mono,
    types::{GenericArg, Ty},
};

fn typed(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("instances.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let hir = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, hir)
}

fn instantiate(
    compilation: &Compilation,
    hir: &hir::Program,
    roots: &[mono::InstanceKey],
    options: mono::Options,
) -> Result<mono::Program, mono::Error> {
    mono::instantiate(
        hir,
        roots,
        mono::Context {
            symbols: &compilation.symbols,
            sources: &compilation.sources,
            external: &[],
        },
        options,
    )
}

#[test]
fn generic_calls_create_canonical_concrete_mir_instances() {
    let (compilation, hir) = typed(
        "T identity<T>(T value) { return move value; } i32 a() { return identity(1); } i32 b() { return identity(2); } u64 c(u64 value) { return identity(value); }",
    );
    let roots = mono::default_roots(&hir);
    let program = instantiate(&compilation, &hir, &roots, mono::Options::default()).unwrap();
    let identity = hir.functions[0].definition;
    let instances: Vec<_> = program
        .instances
        .iter()
        .filter(|instance| instance.key.definition == identity)
        .collect();
    assert_eq!(instances.len(), 2);
    assert_eq!(program.mir.functions.len(), 5);
    assert!(
        program
            .mir
            .functions
            .iter()
            .flat_map(|body| &body.locals)
            .all(|local| !matches!(program.hir.types.get(local.ty), Ty::Parameter { .. }))
    );
    program.analysis.drops.require_concrete().unwrap();
}

#[test]
fn generic_record_fields_and_calls_are_revalidated_after_substitution() {
    let (compilation, hir) = typed(
        "struct Wrap<T> { T value; } T get<T>(Wrap<T> wrapped) { return move wrapped.value; } i32 f(Wrap<i32> value) { return get(move value); }",
    );
    let program = instantiate(
        &compilation,
        &hir,
        &mono::default_roots(&hir),
        mono::Options::default(),
    )
    .unwrap();
    assert_eq!(program.instances.len(), 2);
    let record = program
        .layouts
        .entries
        .iter()
        .find(|layout| matches!(layout.kind, cavo_compiler::layout::Kind::Record { .. }))
        .unwrap();
    assert_eq!((record.size, record.alignment), (4, 4));
    assert!(
        program
            .dump(&compilation.symbols)
            .contains("no native code generated")
    );
}

#[test]
fn explicit_roots_reject_missing_arguments_instead_of_using_template_types() {
    let (compilation, hir) = typed("T identity<T>(T value) { return move value; }");
    assert!(mono::default_roots(&hir).is_empty());
    let root = mono::InstanceKey {
        definition: hir.functions[0].definition,
        arguments: Vec::new(),
    };
    let error = instantiate(&compilation, &hir, &[root], mono::Options::default()).unwrap_err();
    assert_eq!(error.code, "E-MONO-ARGUMENT");
}

#[test]
fn recursive_instances_share_one_body_and_polymorphic_growth_is_bounded() {
    let (compilation, mut hir) = typed(
        "T again<T>(T value, bool done) { if (done) { return move value; } return again(move value, true); }",
    );
    let ty = hir.types.builtin("i32").unwrap();
    let root = mono::InstanceKey {
        definition: hir.functions[0].definition,
        arguments: vec![GenericArg::Type(ty)],
    };
    let program = instantiate(
        &compilation,
        &hir,
        std::slice::from_ref(&root),
        mono::Options::default(),
    )
    .unwrap();
    assert_eq!(program.instances.len(), 1);
    let options = mono::Options {
        limits: mono::Limits {
            instances_per_definition: 0,
            ..mono::Limits::default()
        },
        ..mono::Options::default()
    };
    assert_eq!(
        instantiate(&compilation, &hir, &[root], options)
            .unwrap_err()
            .code,
        "E-MONO-LIMIT"
    );
}

#[test]
fn const_generic_instances_resolve_lengths_values_and_dependent_assertions() {
    let (compilation, hir) = typed(
        "struct Buffer<const usize N> { static_assert(N > 0, \"positive capacity\"); byte[N] bytes; } usize capacity<const usize N>() { return N; } usize f(Buffer<4> buffer) { return capacity::<4>(); }",
    );
    let program = instantiate(
        &compilation,
        &hir,
        &mono::default_roots(&hir),
        mono::Options::default(),
    )
    .unwrap();
    assert!(program.layouts.entries.iter().any(|layout| matches!(
        layout.kind,
        cavo_compiler::layout::Kind::Array { count: 4, .. }
    )));
    assert!(
        program
            .mir
            .functions
            .iter()
            .flat_map(|body| &body.locals)
            .all(|local| !matches!(program.hir.types.get(local.ty), Ty::SymbolicArray { .. }))
    );
}
