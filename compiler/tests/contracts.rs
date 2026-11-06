use cavo_compiler::{
    Compilation,
    contracts::{Assessment, Verdict},
    mir,
};

const CORE: &str = r#"
@lang(copy) trait Copy {}
@lang(readable) contract Readable<T>(ptr<const T> address, usize count) {}
@lang(writable) contract Writable<T>(ptr<T> address, usize count) {}
@lang(initialized) contract Initialized<T>(ptr<T> address, usize count) {}
@intrinsic(as_ptr) ptr<const T> address<T>(&T value);
@intrinsic(as_mut_ptr) ptr<T> address_mut<T>(&mut T value);
@intrinsic(ptr_read) T read<T: Copy>(ptr<const T> address);
@intrinsic(ptr_read) T read_mut<T: Copy>(ptr<T> address);
@intrinsic(ptr_initialize) void initialize<T>(ptr<T> address, T value);
@intrinsic(allocate) ptr<T> allocate<T>(usize count);
@intrinsic(deallocate) void release<T>(ptr<T> address);
@intrinsic(ptr_offset) ptr<T> offset<T>(ptr<T> address, usize count);
"#;

fn parsed(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("contracts.cavo", format!("{CORE}\n{source}"))
        .unwrap();
    compilation.parse(file);
    compilation
}

fn checked(source: &str) -> (Compilation, mir::Program) {
    let mut compilation = parsed(source);
    let (_, program) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    compilation
        .mir_analysis
        .as_ref()
        .unwrap()
        .contracts
        .validate()
        .unwrap();
    (compilation, program)
}

fn rejected(source: &str, code: &str) -> Compilation {
    let mut compilation = parsed(source);
    assert!(compilation.check_mir().is_none(), "accepted {source}");
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "{:#?}",
        compilation.diagnostics
    );
    compilation
}

#[test]
fn reference_origins_authorize_copy_reads_inside_contract_boundaries() {
    let (compilation, _) = checked(
        "i32 f() { i32 value = 7; contract { auto p = address(&value); return read(p); } }",
    );
    let report = &compilation.mir_analysis.as_ref().unwrap().contracts;
    assert!(!report.obligations.is_empty());
    assert!(
        report
            .obligations
            .iter()
            .all(|o| o.verdict() == Verdict::Satisfied),
        "{report:#?}"
    );
}

#[test]
fn a_contract_block_does_not_authorize_an_arbitrary_pointer() {
    rejected(
        "i32 f(ptr<const i32> p) { contract { return read(p); } }",
        "E-CONTRACT-003",
    );
}

#[test]
fn initialized_heap_reads_and_affine_free_are_checked() {
    checked(
        "i32 f() { contract { auto p = allocate::<i32>(1); initialize(p, 42); i32 value = read_mut(p); release(p); return value; } }",
    );
    rejected(
        "i32 f() { contract { auto p = allocate::<i32>(1); return read_mut(p); } }",
        "E-CONTRACT-004",
    );
    rejected(
        "void f() { contract { auto p = allocate::<i32>(1); release(p); release(p); } }",
        "E-CONTRACT-004",
    );
}

#[test]
fn one_initialized_element_does_not_initialize_the_remaining_allocation() {
    rejected(
        "i32 f() { contract { auto p = allocate::<i32>(2); initialize(p, 1); auto next = offset(p, 1); return read_mut(next); } }",
        "E-CONTRACT-004",
    );
    checked(
        "i32 f() { contract { auto p = allocate::<i32>(2); auto next = offset(p, 1); initialize(next, 9); i32 value = read_mut(next); release(p); return value; } }",
    );
}

#[test]
fn free_invalidates_all_pointer_aliases_and_keeps_the_witness() {
    let compilation = rejected(
        "i32 f() { contract { auto p = allocate::<i32>(1); initialize(p, 2); auto alias = p; release(p); return read_mut(alias); } }",
        "E-CONTRACT-004",
    );
    assert!(compilation.diagnostics.iter().any(|d| {
        d.notes
            .iter()
            .any(|note| note.contains("allocation lifetime"))
    }));
}

#[test]
fn explicit_assumptions_remain_assumptions_and_unknown_calls_invalidate_them() {
    let (compilation, _) = checked(
        "i32 f(ptr<const i32> p) { contract { assume Readable::<i32>(p, 1) because \"driver lease\"; return read(p); } }",
    );
    let report = &compilation.mir_analysis.as_ref().unwrap().contracts;
    assert!(
        report
            .obligations
            .iter()
            .flat_map(|o| &o.components)
            .any(|c| matches!(c.assessment, Assessment::Assumed(_)))
    );
    rejected(
        "void opaque(); i32 f(ptr<const i32> p) { contract { assume Readable::<i32>(p, 1) because \"driver lease\"; opaque(); return read(p); } }",
        "E-CONTRACT-003",
    );
}

#[test]
fn named_requirements_are_checked_at_calls_and_available_to_implementations() {
    checked(
        "contract Valid<T>(ptr<const T> p) { requires Readable::<T>(p, 1); } i32 load(ptr<const i32> p) requires Valid::<i32>(p) { contract { return read(p); } } i32 f() { i32 n = 8; return load(address(&n)); }",
    );
    rejected(
        "i32 load(ptr<const i32> p) requires Readable::<i32>(p, 1) { contract { return read(p); } } i32 f(ptr<const i32> p) { return load(p); }",
        "E-CONTRACT-003",
    );
}

#[test]
fn ordinary_scalar_contracts_keep_runtime_guards_and_entry_snapshots() {
    let (_, program) = checked(
        "i32 next(i32 value) requires value < i32::MAX ensures result == old(value) + 1 { value += 1; return value; } i32 f() { return next(4); }",
    );
    assert!(
        program
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .any(|b| matches!(b.terminator, mir::Terminator::Switch { .. }))
    );
}

#[test]
fn borrowed_pointers_never_acquire_deallocation_authority() {
    rejected(
        "void f(&mut i32 value) { contract { auto p = address_mut(value); release(p); } }",
        "E-CONTRACT-004",
    );
}

#[test]
fn raw_take_requires_restoration_before_safe_use_and_cleanup() {
    let intrinsic = "@intrinsic(ptr_take) T take<T>(ptr<T> p);";
    rejected(
        &format!(
            "{intrinsic} i32 f() {{ i32 value = 3; contract {{ auto p = address_mut(&mut value); i32 n = take(p); }} return value; }}"
        ),
        "E-CONTRACT-003",
    );
    checked(&format!(
        "{intrinsic} i32 f() {{ i32 value = 3; contract {{ auto p = address_mut(&mut value); i32 n = take(p); initialize(p, n); }} return value; }}"
    ));
}

#[test]
fn union_reads_require_the_current_active_field() {
    checked(
        "union Bits { u32 integer; f32 decimal; } u32 f() { contract { Bits bits = Bits { integer: 7 }; return bits.integer; } }",
    );
    rejected(
        "union Bits { u32 integer; f32 decimal; } f32 f() { contract { Bits bits = Bits { integer: 7 }; return bits.decimal; } }",
        "E-CONTRACT-004",
    );
    rejected(
        "union Bits { u32 integer; f32 decimal; } void f() { Bits bits = Bits { integer: 7 }; }",
        "E-CONTRACT-BOUNDARY",
    );
}

#[test]
fn compiler_intrinsic_permissions_cannot_be_erased_into_plain_callbacks() {
    rejected(
        "@intrinsic(ptr_read) i32 load(ptr<const i32> p); i32 f(ptr<const i32> p) { fn(ptr<const i32>) -> i32 callback = load; return callback(p); }",
        "E-CALLABLE-IDENTITY",
    );
}

#[test]
fn audit_keys_and_retained_guard_certificates_are_deterministic_and_snapshot_bound() {
    let mut compilation = parsed("i32 f(i32 x) requires x > 0 { return x + 1; }");
    let (mut hir, mut program) = compilation.check_mir().unwrap();
    let report = &compilation.mir_analysis.as_ref().unwrap().contracts;
    let json = report.json(&compilation.sources);
    assert_eq!(json, report.json(&compilation.sources));
    assert!(json.contains("runtime_checks_retained"));
    report.validate_for(&program, &hir).unwrap();
    let block = program
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .find(|b| matches!(b.terminator, mir::Terminator::Checked { .. }))
        .unwrap();
    if let mir::Terminator::Checked { normal, .. } = block.terminator {
        block.terminator = mir::Terminator::Goto(normal);
    }
    assert!(report.validate_for(&program, &hir).is_err());
    hir.functions.clear();
    assert!(report.validate_for(&program, &hir).is_err());
}

#[test]
fn substituted_scalar_clauses_read_references_and_check_pure_helpers() {
    checked(
        "bool positive(i32 n) { return n > 0; } i32 read_positive(&i32 value) requires positive(*value) { return *value; } i32 f() { i32 n = 3; return read_positive(&n); }",
    );
}

#[test]
fn violations_keep_the_trust_dependency_of_their_free_witness() {
    let compilation = rejected(
        "@lang(owned_allocation) contract Owned<T>(ptr<T> p) {} void f(ptr<i32> p) { contract { assume Owned::<i32>(p) because \"foreign allocator ownership\"; release(p); release(p); } }",
        "E-CONTRACT-004",
    );
    let report = &compilation.mir_analysis.as_ref().unwrap().contracts;
    assert!(report.obligations.iter().flat_map(|o| &o.components).any(|c| {
        matches!(c.assessment, Assessment::Violated(id) if report.evidence.trust(id.0).is_some_and(|trust| !trust.is_empty()))
    }));
}

#[test]
fn unaligned_permissions_do_not_forge_a_natural_alignment_proof() {
    let declarations = "@lang(readable_unaligned) contract Unaligned<T>(ptr<const T> p, usize n) {} @intrinsic(ptr_read_unaligned) i32 read_u(ptr<const i32> p);";
    checked(&format!(
        "{declarations} i32 f(ptr<const i32> p) {{ contract {{ assume Unaligned::<i32>(p, 1) because \"packed device word\"; return read_u(p); }} }}"
    ));
    rejected(
        &format!(
            "{declarations} i32 f(ptr<const i32> p) {{ contract {{ assume Unaligned::<i32>(p, 1) because \"packed device word\"; return read(p); }} }}"
        ),
        "E-CONTRACT-003",
    );
}

#[test]
fn packed_fields_never_become_misaligned_safe_references() {
    rejected(
        "@repr(C, packed) struct Packet { byte padding; u32 word; } void f(Packet value) { auto r = &value.word; }",
        "E-BORROW-ALIGN",
    );
}

#[test]
fn a_raw_write_invalidates_possible_aliases_without_claiming_a_definite_violation() {
    rejected(
        "@lang(readable) contract ReadMut<T>(ptr<T> p, usize n) {} @intrinsic(ptr_replace) void replace<T>(ptr<T> p, T value); bool f(ptr<const bool> p, ptr<u32> q) requires Readable::<bool>(p, 1) && ReadMut::<u32>(q, 1) && Writable::<u32>(q, 1) { contract { replace(q, 2); return read(p); } }",
        "E-CONTRACT-003",
    );
}

#[test]
fn generic_take_does_not_reuse_an_entry_initialization_premise() {
    rejected(
        "@lang(readable) contract ReadMut<T>(ptr<T> p, usize n) {} @intrinsic(ptr_take) T take<T>(ptr<T> p); void f<T>(ptr<T> p) requires ReadMut::<T>(p, 1) && Writable::<T>(p, 1) { contract { T first = take(p); T second = take(p); } }",
        "E-CONTRACT-004",
    );
}

#[test]
fn copied_raw_pointer_wrappers_preserve_their_known_borrow_origins() {
    rejected(
        "struct Wrapper { ptr<i32> p; } void f() { i32 value = 1; auto p = address_mut(&mut value); Wrapper first = Wrapper { p: p }; Wrapper second = first; value = 2; contract { i32 n = read_mut(second.p); } }",
        "E-MIR-BORROW",
    );
}

#[test]
fn union_writes_update_copies_and_nested_union_tags() {
    checked(
        "union Bits { u32 integer; bool bit; } struct Outer { u32 tag; Bits bits; } bool f() { contract { Bits a = Bits { integer: 2 }; a.bit = true; Bits b = a; return b.bit; } }",
    );
    rejected(
        "union Bits { u32 integer; bool bit; } struct Outer { u32 tag; Bits bits; } bool f() { contract { Outer value = Outer { tag: 0, bits: Bits { integer: 2 } }; value.tag = 1; return value.bits.bit; } }",
        "E-CONTRACT-004",
    );
}

#[test]
fn required_contracts_cannot_be_erased_by_function_pointer_assignment() {
    rejected(
        "i32 load(ptr<const i32> p) requires Readable::<i32>(p, 1) { contract { return read(p); } } i32 f(ptr<const i32> p) { fn(ptr<const i32>) -> i32 callback = load; return callback(p); }",
        "E-CALLABLE-IDENTITY",
    );
}

#[test]
fn destructor_calls_cannot_leave_heap_evidence_current_in_the_caller() {
    rejected(
        "@lang(drop) trait Drop { void drop(&mut Self self); } @lang(owned_allocation) contract Owned<T>(ptr<T> p) {} @effects(free_memory, bounded) void destroy(ptr<i32> p) { contract { assume Owned::<i32>(p) because \"Owner allocation invariant\"; release(p); } } struct Owner { ptr<i32> p; } impl Drop for Owner { void drop(&mut Self self) { destroy(self.p); } } i32 f() { contract { auto p = allocate::<i32>(1); initialize(p, 1); { Owner owner = Owner { p: p }; } return read_mut(p); } }",
        "E-CONTRACT-003",
    );
}

#[test]
fn memory_primitive_roles_cannot_silently_ignore_source_requirements() {
    rejected(
        "@lang(readable) contract Extra<T>(ptr<const T> p, usize n) { requires false; }",
        "E-LANG-CONTRACT",
    );
}

#[test]
fn guard_certificates_cannot_forget_their_operand_dependencies() {
    let mut compilation = parsed("i32 f(i32 value) { return value + 1; }");
    let (hir, program) = compilation.check_mir().unwrap();
    let report = &mut compilation.mir_analysis.as_mut().unwrap().contracts;
    assert!(!report.guards[0].checks[0].dependencies.is_empty());
    report.guards[0].checks[0].dependencies.clear();
    report.certificates[0].dependencies.clear();
    assert!(report.validate_for(&program, &hir).is_err());
}

#[test]
fn an_unavailable_pass_does_not_hide_a_definite_violation() {
    use cavo_compiler::{contracts::*, external::digest::sha256, source::Span};
    let obligation = Obligation {
        key: sha256(b"test obligation"),
        span: Span::new(cavo_compiler::source::FileId(0), 0, 0),
        operation: "test".into(),
        components: vec![
            Component {
                name: "lifetime".into(),
                assessment: Assessment::Violated(WitnessId(EvidenceId(0))),
            },
            Component {
                name: "initialization".into(),
                assessment: Assessment::NotAnalyzed("test coverage gap".into()),
            },
        ],
    };
    assert_eq!(obligation.verdict(), Verdict::Rejected);
    assert_eq!(obligation.coverage(), Coverage::Partial);
    assert_eq!(obligation.code(), Some("E-CONTRACT-004"));
}

#[test]
fn different_trust_roots_have_different_external_evidence_keys() {
    use cavo_compiler::contracts::*;
    let mut compilation = parsed("void f() {}");
    compilation.check_mir().unwrap();
    let span = cavo_compiler::source::Span::new(cavo_compiler::source::FileId(0), 0, 0);
    let mut report = Report::default();
    for reason in ["first memory owner", "second memory owner"] {
        report
            .evidence
            .insert(Evidence {
                kind: EvidenceKind::Assumption,
                span,
                event: EventId(0),
                parents: vec![],
                trust: std::collections::BTreeSet::from([Trust::Source {
                    file: 0,
                    start: 0,
                    reason: reason.into(),
                }]),
                detail: "same operation".into(),
            })
            .unwrap();
    }
    let json = report.json(&compilation.sources);
    let keys: Vec<_> = json
        .split("\"key\":\"")
        .skip(1)
        .map(|entry| entry.split('"').next().unwrap())
        .collect();
    assert_eq!(keys.len(), 2);
    assert_ne!(keys[0], keys[1]);
}
