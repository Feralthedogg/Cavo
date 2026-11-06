use cavo_compiler::{Compilation, hir, mir, types::Ty};

fn compilation(source: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("dyn.cavo", source.into()).unwrap();
    compilation.parse(file);
    compilation
}

fn typed(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = compilation(source);
    let program = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, program)
}

#[test]
fn dyn_conversion_records_the_concrete_method_and_declared_signature() {
    let (_, program) = typed(
        "trait Measure { i32 measure(&Self self); }
         struct Counter { i32 value; }
         impl Measure for Counter { i32 measure(&Self self) { return self.value; } }
         i32 read(&dyn Measure value) { return value.measure(); }
         i32 f() { Counter value = Counter { value: 7 }; return read(&value); }",
    );
    assert_eq!(program.vtables.len(), 1);
    let table = &program.vtables[0];
    assert!(matches!(
        program.types.get(table.concrete),
        Ty::Named { .. }
    ));
    assert_eq!(table.slots.len(), 1);
    let slot = &table.slots[0];
    assert_ne!(slot.declaration, slot.implementation);
    assert!(
        program
            .functions
            .iter()
            .any(|function| function.definition == slot.implementation)
    );
    assert!(matches!(
        program.types.get(slot.signature),
        Ty::Function { .. }
    ));
}

#[test]
fn dynamic_calls_are_explicit_mir_operations_and_reborrow_mutable_receivers() {
    let mut compilation = compilation(
        "trait Change { void change(&mut Self self); }
         struct Counter { i32 value; }
         impl Change for Counter { void change(&mut Self self) { self.value += 1; } }
         void update(&mut dyn Change value) { value.change(); value.change(); }
         void f() { Counter value = Counter { value: 0 }; update(&mut value); }",
    );
    let (_, program) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let calls = program
        .functions
        .iter()
        .flat_map(|body| &body.blocks)
        .filter(|block| matches!(block.terminator, mir::Terminator::DynCall { .. }))
        .count();
    assert_eq!(calls, 2);
    assert!(
        program
            .functions
            .iter()
            .flat_map(|body| &body.blocks)
            .flat_map(|block| &block.statements)
            .any(|statement| {
                matches!(
                    statement.kind,
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::DynCoerce { .. },
                        ..
                    }
                )
            })
    );
}

#[test]
fn non_object_safe_traits_are_rejected_even_without_a_concrete_conversion() {
    for method in [
        "T identity<T>(&Self self, T value);",
        "Self duplicate(&Self self);",
        "&Self duplicate(&Self self);",
        "i32 compare(&Self self, &Self other);",
        "i32 consume(move Self self);",
        "i32 static_method();",
    ] {
        let mut compilation = compilation(&format!(
            "trait Bad {{ {method} }} void use(&dyn Bad value) {{}}",
        ));
        assert!(compilation.check_types().is_none(), "accepted {method}");
        assert!(
            compilation.diagnostics.iter().any(|diagnostic| {
                diagnostic.code.starts_with("E-TRAIT") && diagnostic.message.contains("dyn")
            }),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn dyn_conversion_requires_an_actual_matching_implementation() {
    let mut compilation = compilation(
        "trait Measure { i32 measure(&Self self); }
         struct Counter { i32 value; }
         void use(&dyn Measure value) {}
         void f() { Counter value = Counter { value: 0 }; use(&value); }",
    );
    assert!(compilation.check_types().is_none());
    assert!(
        compilation.diagnostics.iter().any(|diagnostic| {
            diagnostic.code.starts_with("E-TRAIT") && diagnostic.message.contains("implementation")
        }),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn dyn_signatures_are_resolved_independently_of_source_declaration_order() {
    let (_, program) = typed(
        "i32 read(&dyn Measure value) { return value.measure(); }
         trait Measure { i32 measure(&Self self); }
         struct Counter { i32 value; }
         impl Measure for Counter { i32 measure(&Self self) { return self.value; } }
         i32 f() { Counter value = Counter { value: 7 }; return read(&value); }",
    );
    assert_eq!(program.vtables.len(), 1);
}

#[test]
fn dyn_methods_preserve_method_lifetime_binders() {
    let (_, program) = typed(
        "trait View { &'a i32 view<'a>(&'a Self self); }
         struct Store { i32 value; }
         impl View for Store { &'a i32 view<'a>(&'a Self self) { return &self.value; } }
         i32 f() { Store value = Store { value: 8 }; &dyn View view = &value; return *view.view(); }",
    );
    assert_eq!(program.vtables.len(), 1);
    assert_eq!(program.vtables[0].slots.len(), 1);
}

#[test]
fn supertrait_dispatch_retains_every_declared_slot() {
    let (_, program) = typed(
        "trait Base { i32 base(&Self self); }
         trait Derived: Base { i32 derived(&Self self); }
         struct Value { i32 number; }
         impl Base for Value { i32 base(&Self self) { return self.number; } }
         impl Derived for Value { i32 derived(&Self self) { return self.number + 1; } }
         i32 read(&dyn Derived value) { return value.base() + value.derived(); }
         i32 f() { Value value = Value { number: 3 }; return read(&value); }",
    );
    assert_eq!(program.vtables[0].slots.len(), 2);
}

#[test]
fn vtable_mutations_cannot_replace_the_implementation_witness() {
    let (_, mut program) = typed(
        "trait Read { i32 read(&Self self); }
         struct Value { i32 number; }
         impl Read for Value { i32 read(&Self self) { return self.number; } }
         i32 unrelated(&Value value) { return 0; }
         void f(&Value value) { &dyn Read object = value; }",
    );
    let unrelated = program
        .functions
        .iter()
        .find(|function| {
            !program
                .implementations
                .iter()
                .flat_map(|implementation| &implementation.methods)
                .any(|method| method.implementation == function.definition)
                && function.parameters.len() == 1
                && function.result != cavo_compiler::types::TyId::VOID
        })
        .unwrap()
        .definition;
    program.vtables[0].slots[0].implementation = unrelated;
    assert!(program.validate().is_err());
}
