use cavo_compiler::{Compilation, external::interface, hir};

const CORE: &str = r#"
@lang(send) trait Send {}
@lang(sync) trait Sync {}
@lang(task_transfer) trait TaskTransfer {}
@lang(suspend_safe) trait SuspendSafe {}
@lang(copy) trait Copy {}
"#;

fn parsed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("negative.cavo", format!("{CORE}\n{source}"))
        .unwrap();
    compilation.parse(file);
    compilation
}

fn accepted(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = parsed(source);
    let (hir, _) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, hir)
}

fn rejected(source: &str, code: &str) {
    let mut compilation = parsed(source);
    assert!(compilation.check_mir().is_none(), "accepted {source}");
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn negative_markers_restrict_each_nominal_and_containing_type() {
    for marker in ["Send", "Sync", "TaskTransfer", "SuspendSafe"] {
        for ty in ["ThreadSlot", "Wrapper", "ThreadSlot[2]"] {
            rejected(
                &format!(
                    "struct ThreadSlot {{ u32 index; }} impl !{marker} for ThreadSlot {{}} struct Wrapper {{ ThreadSlot slot; }} void require<T: {marker}>(T value) {{}} void inspect({ty} value) {{ require(move value); }}"
                ),
                "E-TRAIT-BOUND",
            );
        }
    }
}

#[test]
fn disabling_send_does_not_disable_sync_or_shared_reference_send() {
    accepted(
        "struct ThreadSlot { u32 index; } impl !Send for ThreadSlot {} void require<T: Send + Sync>(T value) {} void inspect(&ThreadSlot slot) { require(slot); }",
    );
}

#[test]
fn negative_impls_are_untrusted_general_declarations() {
    let (compilation, program) = accepted(
        "struct Slot<T, const usize N> { T[N] data; } impl<T, const usize N> !Send for Slot<T, N> {}",
    );
    assert!(program.tasks.trusted.is_empty());
    let implementation = program
        .implementations
        .iter()
        .find(|item| item.negative)
        .unwrap();
    let trait_ = implementation.trait_ref.as_ref().unwrap();
    assert!(
        hir::traits::select_trait(&program, implementation.target, trait_)
            .unwrap()
            .is_none()
    );
    assert!(compilation.diagnostics.is_empty());
}

#[test]
fn negative_impls_cannot_specialize_or_add_conditional_bounds() {
    for declaration in [
        "impl !Send for Slot<i32> {}",
        "impl<T: Copy> !Send for Slot<T> {}",
    ] {
        rejected(
            &format!("struct Slot<T> {{ T value; }} {declaration}"),
            "E-IMPL-NEGATIVE",
        );
    }
    accepted("struct Slot<T: Copy> { T value; } impl<T: Copy> !Send for Slot<T> {}");
}

#[test]
fn negative_impls_reject_nonmarkers_methods_and_trusted_guarantees() {
    for source in [
        "struct Slot {} impl !Copy for Slot {}",
        "trait Ordinary {} struct Slot {} impl !Ordinary for Slot {}",
        "impl !Send for i32 {}",
        "struct Slot {} impl !Send for Slot { void method() {} }",
    ] {
        rejected(source, "E-IMPL-NEGATIVE");
    }
    rejected(
        "struct Slot {} contract impl !Send for Slot because \"not a guarantee\";",
        "E-IMPL-POLARITY",
    );
}

#[test]
fn positive_and_negative_witnesses_conflict_in_either_declaration_order() {
    for declarations in [
        "impl !Send for Slot {} contract impl Send for Slot because \"reviewed\";",
        "contract impl Send for Slot because \"reviewed\"; impl !Send for Slot {}",
        "impl !Send for Slot {} impl !Send for Slot {}",
    ] {
        rejected(
            &format!("struct Slot {{ u32 index; }} {declarations}"),
            "E-IMPL-OVERLAP",
        );
    }
}

#[test]
fn negative_markers_change_interface_identity_without_arena_or_parameter_names() {
    fn identity(declaration: &str, parameter: &str) -> (cavo_compiler::external::Digest, String) {
        let mut compilation = parsed(&format!(
            "struct Slot<{parameter}> {{ {parameter} value; }} {declaration} void api(Slot<i32> value);"
        ));
        let program = compilation
            .check_types()
            .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
        let functions =
            interface::interfaces(&program, &compilation.symbols, &compilation.sources).unwrap();
        let permissions =
            interface::copy_permissions(&program, &compilation.symbols, &compilation.sources)
                .unwrap();
        (
            functions[0].signature,
            interface::render_with_copy(&functions, &permissions),
        )
    }
    let original = identity("", "T").0;
    let (restricted, report) = identity("impl<T> !Send for Slot<T> {}", "T");
    assert_ne!(original, restricted);
    assert_eq!(restricted, identity("impl<U> !Send for Slot<U> {}", "U").0);
    assert!(report.contains("\"negative_traits\":[\"Send\"]"));
}
