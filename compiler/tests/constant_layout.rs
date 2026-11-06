use cavo_compiler::{
    Compilation, hir,
    layout::{self, Kind, TargetLayout},
};

fn parse(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("constant-layout.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    compilation
}

fn typed(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = parse(source);
    let program = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, program)
}

#[test]
fn enum_tags_evaluate_const_functions_and_checked_auto_increment() {
    let (compilation, mut program) = typed(
        "const usize base() { return 255; } enum Tag { A = base(), B, C = 2 } void f(Tag value) {}",
    );
    let ty = program.functions.last().unwrap().locals[0].ty;
    let layouts = layout::compute(
        &mut program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        &[ty],
    )
    .unwrap();
    let Kind::Enum {
        tag_bytes,
        variants,
        ..
    } = &layouts.get(ty).unwrap().kind
    else {
        panic!("enum layout");
    };
    assert_eq!(*tag_bytes, 2);
    assert_eq!(
        variants
            .iter()
            .map(|variant| variant.discriminant)
            .collect::<Vec<_>>(),
        [255, 256, 2]
    );
}

#[test]
fn enum_tag_collisions_and_overflow_do_not_create_fallback_values() {
    for (source, code) in [
        ("enum Tag { A = 2, B = 2 }", "E-ENUM-DISCRIMINANT"),
        ("enum Tag { A = usize::MAX, B }", "E-CONST-EVAL"),
    ] {
        let mut compilation = parse(source);
        assert!(compilation.check_types().is_none());
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == code),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn dependent_enum_tag_collisions_are_checked_at_concrete_layout() {
    let (compilation, mut program) =
        typed("enum Tag<const usize N> { A = N, B = 2 } void f(Tag<2> value) {}");
    let ty = program.functions[0].locals[0].ty;
    let error = layout::compute(
        &mut program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        &[ty],
    )
    .unwrap_err();
    assert!(error.message.contains("collide"), "{error}");
}

#[test]
fn the_combined_frontend_example_has_concrete_layout_and_destructor_instances() {
    let source = include_str!("../../examples/frontend/features.cavo");
    let mut compilation = parse(source);
    let program = compilation
        .check_monomorphized()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    assert!(!program.drop_instances.is_empty());
    assert!(!program.hir.vtables.is_empty());
    assert!(!program.hir.closures.is_empty());
    assert!(
        program
            .layouts
            .entries
            .iter()
            .any(|layout| layout.alignment == 16)
    );
    program.analysis.drops.require_concrete().unwrap();
}
