use cavo_compiler::{Compilation, hir, mir};

fn typed(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("mir-variants.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let mut hir = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let mir = mir::lower(&mut hir).unwrap();
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

fn variant(compilation: &Compilation, hir: &hir::Program, name: &str) -> hir::DefId {
    hir::DefId(
        hir.definitions
            .iter()
            .position(|definition| compilation.symbols.get(definition.name) == name)
            .unwrap() as u32,
    )
}

fn downcast_owner(place: &mir::Place) -> Option<mir::Place> {
    let index = place
        .projection
        .iter()
        .position(|projection| matches!(projection, mir::Projection::Downcast(_)))?;
    Some(mir::Place {
        local: place.local,
        projection: place.projection[..index].to_vec(),
    })
}

fn retag(
    destination: mir::Place,
    tag: hir::DefId,
    span: cavo_compiler::source::Span,
) -> mir::Statement {
    mir::Statement {
        kind: mir::StatementKind::Assign {
            destination,
            value: mir::Rvalue::Variant {
                definition: tag,
                fields: Vec::new(),
            },
        },
        span,
    }
}

#[test]
fn ending_a_borrowed_value_cannot_expose_an_uninitialized_pointee() {
    let (_, mut hir, mut mir) =
        typed("void replace<T>(&mut T target, T value) { *target = move value; }");
    let body = &mut mir.functions[0];
    let next = body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            mir::Terminator::Drop { place, next, .. }
                if place.projection.contains(&mir::Projection::Deref) =>
            {
                Some(*next)
            }
            _ => None,
        })
        .unwrap();
    body.blocks[next.0 as usize].statements.remove(0);
    let error = mir.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("immediately restore"), "{error}");
}

#[test]
fn retagging_invalidates_a_prior_variant_test() {
    let (compilation, mut hir, mut mir) = typed(
        "enum E { Item(i32), Empty } i32 f(E value) { return match value { E::Item(x) => x, E::Empty => 0 }; }",
    );
    let empty = variant(&compilation, &hir, "Empty");
    let body = &mut mir.functions[0];
    let (block, statement, owner) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .find_map(|(statement, value)| match &value.kind {
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::Use(mir::Operand::Copy(place)),
                        ..
                    } => downcast_owner(place).map(|owner| (block, statement, owner)),
                    _ => None,
                })
        })
        .unwrap();
    let span = body.blocks[block].span;
    body.blocks[block]
        .statements
        .insert(statement, retag(owner, empty, span));
    let error = mir.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("discriminant"), "{error}");
}

#[test]
fn a_captured_payload_address_does_not_survive_retagging_its_owner() {
    let (compilation, mut hir, mut mir) = typed(
        "enum E { Item(&'static mut i32), Empty } &'static mut i32 f(E value, &'static mut i32 fallback) { return match (move value) { E::Item(x) => move x, E::Empty => move fallback }; }",
    );
    let empty = variant(&compilation, &hir, "Empty");
    let body = &mut mir.functions[0];
    let (block, statement, owner) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .find_map(|(statement, value)| match &value.kind {
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::AddressOf(place),
                        ..
                    } => downcast_owner(place).map(|owner| (block, statement, owner)),
                    _ => None,
                })
        })
        .unwrap();
    let span = body.blocks[block].span;
    body.blocks[block]
        .statements
        .insert(statement + 1, retag(owner, empty, span));
    let error = mir.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("capture"), "{error}");
}

#[test]
fn enum_payload_moves_invalidate_the_selected_owned_field() {
    let (_, mut hir, mut mir) = typed(
        "enum E<T> { Item(T), Empty } T f<T>(E<T> value, T fallback) { return match (move value) { E::Item(x) => move x, E::Empty => move fallback }; }",
    );
    let body = &mut mir.functions[0];
    let (block, statement, destination, source) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .find_map(|(statement, value)| match &value.kind {
                    mir::StatementKind::Assign {
                        destination,
                        value: mir::Rvalue::Use(mir::Operand::Move(place)),
                    } if body.local(place.local).kind == mir::LocalKind::Address => {
                        Some((block, statement, destination.clone(), place.clone()))
                    }
                    _ => None,
                })
        })
        .unwrap();
    let span = body.blocks[block].span;
    body.blocks[block].statements.insert(
        statement + 1,
        mir::Statement {
            kind: mir::StatementKind::Assign {
                destination,
                value: mir::Rvalue::Use(mir::Operand::Move(source)),
            },
            span,
        },
    );
    let error = mir.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("uninitialized or moved"), "{error}");
}

#[test]
fn internal_capture_cannot_hide_a_user_drop_ancestor_from_move_checks() {
    let (compilation, mut hir, mut mir) = typed(
        "@lang(drop) trait Dispose { void drop(&mut Self self); } struct Owner { i32 value; } impl Dispose for Owner { void drop(&mut Self self) {} } i32 f(Owner owner) { owner.value += 1; return owner.value; }",
    );
    let id = variant(&compilation, &hir, "f");
    let body = mir
        .functions
        .iter_mut()
        .find(|body| body.definition == id)
        .unwrap();
    let locals = &body.locals;
    let operand = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.statements)
        .find_map(|statement| match &mut statement.kind {
            mir::StatementKind::Assign {
                value: mir::Rvalue::Use(operand @ mir::Operand::Copy(_)),
                ..
            } => {
                let mir::Operand::Copy(place) = operand else {
                    unreachable!()
                };
                (locals[place.local.0 as usize].kind == mir::LocalKind::Address).then_some(operand)
            }
            _ => None,
        })
        .unwrap();
    let mir::Operand::Copy(place) = operand else {
        unreachable!()
    };
    *operand = mir::Operand::Move(place.clone());
    let error = mir.validate(&mut hir).unwrap_err();
    assert!(error.message.contains("user Drop"), "{error}");
}
