use cavo_compiler::{Compilation, hir, mir, types::TyId};
use mir::borrow::{FindingKind, Verdict};

fn typed(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("mir-borrow.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let mut hir = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let mir = mir::lower(&mut hir).unwrap();
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

fn report(source: &str) -> mir::borrow::Report {
    let (_, mut hir, mir) = typed(source);
    mir::borrow::analyze(&mir, &mut hir).unwrap()
}

#[test]
fn direct_loans_end_at_their_last_mir_use() {
    let report = report(
        "i32 f() { i32 value = 1; &mut i32 reference = &mut value; *reference = 2; value = 3; return value; }",
    );
    assert_eq!(
        report.functions[0].verdict,
        Verdict::Established,
        "{report:#?}"
    );
    assert_eq!(report.functions[0].loans.len(), 1);
    assert!(report.dump().contains("not a native certificate"));
}

#[test]
fn a_future_reference_use_rejects_an_intervening_write_on_mir() {
    // check_types deliberately bypasses the earlier HIR borrow analyzer.
    let report =
        report("i32 f() { i32 value = 1; &i32 reference = &value; value = 2; return *reference; }");
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.kind == FindingKind::Conflict)
    );
}

#[test]
fn record_field_loans_preserve_disjoint_storage() {
    let report = report(
        "struct Pair { i32 left; i32 right; } i32 f() { Pair pair = Pair { left: 1, right: 2 }; &mut i32 reference = &mut pair.left; pair.right = 3; *reference = 4; return pair.right; }",
    );
    assert_eq!(
        report.functions[0].verdict,
        Verdict::Established,
        "{report:#?}"
    );
}

#[test]
fn reborrows_suspend_the_parent_until_the_childs_last_use() {
    let good = report(
        "i32 f() { i32 value = 1; &mut i32 parent = &mut value; &mut i32 child = &mut *parent; *child = 2; *parent = 3; return value; }",
    );
    assert_eq!(good.functions[0].verdict, Verdict::Established, "{good:#?}");
    let bad = report(
        "i32 f() { i32 value = 1; &mut i32 parent = &mut value; &mut i32 child = &mut *parent; *parent = 3; return *child; }",
    );
    assert_eq!(bad.functions[0].verdict, Verdict::Rejected);
}

#[test]
fn defer_captures_keep_nested_reference_capabilities_live() {
    let good = report(
        "i32 f() { i32 value = 1; &mut i32 reference = &mut value; defer { *reference = 3; } return 7; }",
    );
    assert_eq!(good.functions[0].verdict, Verdict::Established, "{good:#?}");
    let bad = report(
        "i32 f() { i32 value = 1; &mut i32 reference = &mut value; defer { *reference = 3; } value = 2; return value; }",
    );
    assert_eq!(bad.functions[0].verdict, Verdict::Rejected, "{bad:#?}");
}

#[test]
fn returning_a_local_reference_is_rejected_on_cleanup_edges() {
    let report = report("&'static i32 f() { i32 value = 1; return &value; }");
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.kind == FindingKind::LocalEscape)
    );
}

#[test]
fn direct_source_reference_calls_are_established_from_mir_summaries() {
    let report = report(
        "&i32 identity(&i32 value) { return value; } i32 f(&i32 value) { &i32 result = identity(value); return *result; }",
    );
    assert_eq!(
        report.functions[1].verdict,
        Verdict::Established,
        "{report:#?}"
    );
    assert!(report.functions[1].gaps.is_empty());
    assert!(report.functions[1].assumptions.is_empty());
}

fn local_named(compilation: &Compilation, body: &mir::Body, name: &str) -> mir::LocalId {
    let index = body
        .locals
        .iter()
        .position(|local| {
            local
                .name
                .is_some_and(|symbol| compilation.symbols.get(symbol) == name)
        })
        .unwrap();
    mir::LocalId(index as u32)
}

#[test]
fn shared_reference_writes_cannot_be_introduced_by_a_mir_transform() {
    let (compilation, mut hir, mut mir) = typed(
        "i32 f() { i32 value = 1; &i32 reference = &value; i32 other = 0; other = 2; return *reference; }",
    );
    let body = &mut mir.functions[0];
    let other = local_named(&compilation, body, "other");
    let reference = local_named(&compilation, body, "reference");
    for statement in body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.statements)
    {
        if let mir::StatementKind::Assign {
            value: mir::Rvalue::AddressOf(place),
            ..
        } = &mut statement.kind
            && place.local == other
        {
            *place = mir::Place::local(reference).project(mir::Projection::Deref);
        }
    }
    let report = mir::borrow::analyze(&mir, &mut hir).unwrap();
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.kind == FindingKind::SharedWrite)
    );
}

#[test]
fn a_shared_outer_reference_does_not_grant_nested_exclusive_write_permission() {
    let (_, mut hir, mut mir) = typed("i32 f(& &mut i32 reference) { return **reference; }");
    let body = &mut mir.functions[0];
    let parameter = mir::LocalId(1);
    let place = mir::Place::local(parameter)
        .project(mir::Projection::Deref)
        .project(mir::Projection::Deref);
    let ty = hir.functions[0].result;
    let entry = &mut body.blocks[body.entry.0 as usize];
    entry.statements.push(mir::Statement {
        kind: mir::StatementKind::Assign {
            destination: place,
            value: mir::Rvalue::Use(mir::Operand::Constant {
                value: hir::Constant::Integer {
                    magnitude: 3,
                    negative: false,
                },
                ty,
            }),
        },
        span: entry.span,
    });
    let report = mir::borrow::analyze(&mir, &mut hir).unwrap();
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.kind == FindingKind::SharedWrite)
    );
}

#[test]
fn panic_cleanup_uses_participate_in_mir_loan_liveness() {
    let (compilation, mut hir, mut mir) = typed(
        "void tick(); i32 f() { i32 value = 1; &i32 reference = &value; tick(); return *reference; }",
    );
    let body = &mut mir.functions[0];
    let owner = local_named(&compilation, body, "value");
    let reference = local_named(&compilation, body, "reference");
    let panic = body
        .blocks
        .iter()
        .find_map(|block| match block.terminator {
            mir::Terminator::Call { panic, .. } => Some(panic),
            _ => None,
        })
        .unwrap();
    let ty = body.local(owner).ty;
    let span = body.block(panic).span;
    let write = mir::StatementKind::Assign {
        destination: mir::Place::local(owner),
        value: mir::Rvalue::Use(mir::Operand::Constant {
            value: hir::Constant::Integer {
                magnitude: 9,
                negative: false,
            },
            ty,
        }),
    };
    let read = mir::StatementKind::Assign {
        destination: mir::Place::local(body.return_local),
        value: mir::Rvalue::Use(mir::Operand::Copy(
            mir::Place::local(reference).project(mir::Projection::Deref),
        )),
    };
    body.blocks[panic.0 as usize].statements.splice(
        0..0,
        [
            mir::Statement { kind: write, span },
            mir::Statement { kind: read, span },
        ],
    );
    assert_ne!(ty, TyId::VOID);
    let report = mir::borrow::analyze(&mir, &mut hir).unwrap();
    assert_eq!(report.functions[0].verdict, Verdict::Rejected);
    assert!(
        report.functions[0]
            .findings
            .iter()
            .any(|finding| finding.block == panic && finding.kind == FindingKind::Conflict)
    );
}
