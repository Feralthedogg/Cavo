use cavo_compiler::{
    Compilation, hir,
    layout::{self, Kind, TargetLayout},
    types::{Ty, TyId},
};

fn typed(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("layout.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let hir = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, hir)
}

fn parameter(program: &hir::Program) -> TyId {
    let function = program.functions.last().unwrap();
    function.locals[function.parameters[0].0 as usize].ty
}

fn layouts(compilation: &Compilation, program: &mut hir::Program, roots: &[TyId]) -> layout::Table {
    layout::compute(
        program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        roots,
    )
    .unwrap()
}

#[test]
fn records_have_checked_padding_and_explicit_alignment() {
    let (compilation, mut program) = typed(
        "@repr(C) @align(16) struct Packet { byte tag; u64 value; u16 tail; } void f(Packet packet) {}",
    );
    let ty = parameter(&program);
    let table = layouts(&compilation, &mut program, &[ty]);
    let packet = table.get(ty).unwrap();
    assert_eq!((packet.size, packet.alignment), (32, 16));
    assert!(packet.c_compatible);
    let Kind::Record { fields, .. } = &packet.kind else {
        panic!("record layout");
    };
    assert_eq!(
        fields.iter().map(|field| field.offset).collect::<Vec<_>>(),
        [0, 8, 16]
    );
}

#[test]
fn generic_records_and_tagged_enums_use_concrete_payload_layouts() {
    let (compilation, mut program) = typed(
        "struct Wrap<T> { T value; byte tag; } enum Maybe<T> { None, Some(T) } void f(Maybe<Wrap<u64>> value) {}",
    );
    let ty = parameter(&program);
    let table = layouts(&compilation, &mut program, &[ty]);
    let value = table.get(ty).unwrap();
    assert_eq!((value.size, value.alignment), (24, 8));
    let Kind::Enum {
        tag_bytes,
        payload_offset,
        variants,
    } = &value.kind
    else {
        panic!("enum layout");
    };
    assert_eq!((*tag_bytes, *payload_offset), (1, 8));
    assert!(variants[0].fields.is_empty());
    let wrapped = table.get(variants[1].fields[0].ty).unwrap();
    assert_eq!((wrapped.size, wrapped.alignment), (16, 8));
}

#[test]
fn pointer_layout_does_not_follow_recursive_pointees_and_slices_are_wide() {
    let (compilation, mut program) =
        typed("struct Node { ptr<Node> next; } void f(&[i32] values) {}");
    let slice = parameter(&program);
    let node = program.records[0].definition;
    let node = program.definitions[node.0 as usize].ty;
    let table = layouts(&compilation, &mut program, &[slice, node]);
    assert_eq!(table.get(slice).unwrap().size, 16);
    assert_eq!(table.get(node).unwrap().size, 8);
}

#[test]
fn arrays_check_target_limits_without_allocating_constant_storage() {
    let (compilation, mut program) = typed("void f(u64[2] values) {}");
    let ty = parameter(&program);
    let target = TargetLayout {
        maximum_object_size: 8,
        ..TargetLayout::LP64
    };
    let error = layout::compute(
        &mut program,
        target,
        &compilation.symbols,
        &compilation.sources,
        &[ty],
    )
    .unwrap_err();
    assert!(error.message.contains("maximum object"));
    let enormous = program.types.intern(Ty::Array {
        inner: ty,
        length: u64::MAX,
    });
    let error = layout::compute(
        &mut program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        &[enormous],
    )
    .unwrap_err();
    assert!(error.message.contains("overflows"));
}

#[test]
fn unresolved_types_bad_alignment_and_unsized_values_fail_closed() {
    for alignment in [3, 1_073_741_824] {
        let mut invalid = Compilation::default();
        let file = invalid
            .sources
            .add(
                "bad-align.cavo",
                format!("@align({alignment}) struct Bad {{ i32 value; }} void f(Bad value) {{}}"),
            )
            .unwrap();
        invalid.parse(file);
        assert!(invalid.check_types().is_none());
        assert!(
            invalid
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E-CONST-EVAL")
        );
        // A later pass can mutate an already-checked artifact; layout must
        // independently retain the target alignment gate.
        let (compilation, mut program) =
            typed("@align(8) struct Bad { i32 value; } void f(Bad value) {}");
        let ty = parameter(&program);
        let owner = program.records[0].definition;
        let value = program.types.const_value(alignment);
        program.definitions[owner.0 as usize].attributes[0].constant = Some(value);
        assert!(
            layout::compute(
                &mut program,
                TargetLayout::LP64,
                &compilation.symbols,
                &compilation.sources,
                &[ty]
            )
            .is_err()
        );
    }
    let (compilation, mut program) = typed("void f<T>(T value) {}");
    let ty = parameter(&program);
    assert!(
        layout::compute(
            &mut program,
            TargetLayout::LP64,
            &compilation.symbols,
            &compilation.sources,
            &[ty]
        )
        .is_err()
    );
    assert!(
        layout::compute(
            &mut program,
            TargetLayout::LP64,
            &compilation.symbols,
            &compilation.sources,
            &[TyId::STR]
        )
        .is_err()
    );
}

#[test]
fn union_fields_overlay_and_packed_records_preserve_declared_order() {
    let (compilation, mut program) = typed(
        "@repr(C) struct Overlay { byte a; u64 b; } @packed struct Packed { byte a; u64 b; } void f(Packed value) {}",
    );
    let union = program.records[0].definition;
    // The storage query can describe a union without granting raw field access.
    program.definitions[union.0 as usize].kind = hir::DefinitionKind::Union;
    let union = program.definitions[union.0 as usize].ty;
    let packed = parameter(&program);
    let table = layouts(&compilation, &mut program, &[union, packed]);
    let overlay = table.get(union).unwrap();
    assert_eq!((overlay.size, overlay.alignment), (8, 8));
    let Kind::Union { fields } = &overlay.kind else {
        panic!("union layout");
    };
    assert!(fields.iter().all(|field| field.offset == 0));
    let packed = table.get(packed).unwrap();
    assert_eq!((packed.size, packed.alignment), (9, 1));
}

#[test]
fn module_constant_alignment_and_by_value_cycle_queries_are_checked() {
    let (compilation, mut program) = typed(
        "const usize CACHE = 32; @align(CACHE) struct Aligned { byte value; } void f(Aligned value) {}",
    );
    let ty = parameter(&program);
    let table = layouts(&compilation, &mut program, &[ty]);
    assert_eq!(
        (
            table.get(ty).unwrap().size,
            table.get(ty).unwrap().alignment
        ),
        (32, 32)
    );
    program.records[0].fields[0].ty = ty;
    let error = layout::compute(
        &mut program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        &[ty],
    )
    .unwrap_err();
    assert!(error.message.contains("recursive by-value"), "{error}");
}

#[test]
fn alignment_evaluates_const_function_calls_and_generic_parameters() {
    let (compilation, mut program) = typed(
        "const usize align_up(usize value, usize alignment) { return (value + (alignment - 1)) & ~(alignment - 1); } @align(align_up(17, 16)) struct Aligned { byte value; } void f(Aligned value) {}",
    );
    let ty = parameter(&program);
    assert_eq!(
        layouts(&compilation, &mut program, &[ty])
            .get(ty)
            .unwrap()
            .alignment,
        32
    );
    let (compilation, mut program) = typed(
        "@align(N) struct Aligned<const usize N> { byte value; } void f(Aligned<16> value) {}",
    );
    let ty = parameter(&program);
    assert_eq!(
        layouts(&compilation, &mut program, &[ty])
            .get(ty)
            .unwrap()
            .alignment,
        16
    );
}

#[test]
fn generic_alignment_rejects_invalid_concrete_instances() {
    let (compilation, mut program) = typed(
        "@align(N) struct Aligned<const usize N> { byte value; } void f(Aligned<3> value) {}",
    );
    let ty = parameter(&program);
    let error = layout::compute(
        &mut program,
        TargetLayout::LP64,
        &compilation.symbols,
        &compilation.sources,
        &[ty],
    )
    .unwrap_err();
    assert!(error.message.contains("power of two"), "{error}");
}

#[test]
fn enum_layout_uses_evaluated_discriminants_instead_of_variant_count() {
    let (compilation, mut program) =
        typed("enum Choice { Small = 1, Large = 4294967296 } void f(Choice value) {}");
    let ty = parameter(&program);
    let table = layouts(&compilation, &mut program, &[ty]);
    let Kind::Enum {
        tag_bytes,
        variants,
        ..
    } = &table.get(ty).unwrap().kind
    else {
        panic!("enum layout");
    };
    assert_eq!(*tag_bytes, 8);
    assert_eq!(
        variants
            .iter()
            .map(|variant| variant.discriminant)
            .collect::<Vec<_>>(),
        [1, 4294967296]
    );
}
