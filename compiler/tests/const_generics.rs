use cavo_compiler::{
    Compilation, hir,
    syntax::ast,
    types::{ConstKind, ConstTerm, ConstValue, GenericArg, GenericParamKind, Ty, TyId},
};

fn checked(source: &str) -> (Compilation, hir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("const-generics.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let program = compilation
        .check_types()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    (compilation, program)
}

#[test]
fn parser_preserves_const_function_assertions_and_mixed_argument_kinds() {
    let mut compilation = Compilation::default();
    let source = "struct Ring<'a, T, const usize N> { static_assert(N > 0); &'a T[N] data; } const usize capacity<const usize N>() { static_assert(N > 0); return N; } void f(Ring<'static, i32, 4> value) {}";
    let file = compilation
        .sources
        .add("syntax.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let ast::ItemKind::Record {
        generics,
        assertions,
        ..
    } = &compilation.ast.items[0].kind
    else {
        panic!("record");
    };
    assert!(matches!(generics[2], ast::GenericParam::Const { .. }));
    assert_eq!(assertions.len(), 1);
    assert!(
        matches!(&compilation.ast.items[1].kind, ast::ItemKind::Function(function) if function.constant)
    );
}

#[test]
fn nominal_const_arguments_have_normalized_value_identity() {
    let (_, program) = checked(
        "const usize SIZE = 4; struct Buffer<const usize N> { byte[N] data; } void f(Buffer<4> a, Buffer<0x4> b, Buffer<SIZE> c) {}",
    );
    let function = program
        .functions
        .iter()
        .find(|f| f.parameters.len() == 3)
        .unwrap();
    let values: Vec<_> = function
        .parameters
        .iter()
        .map(|id| function.locals[id].ty)
        .collect();
    assert!(values.iter().all(|ty| *ty == values[0]));
    let Ty::Named { arguments, .. } = program.types.get(values[0]) else {
        panic!("nominal type");
    };
    let GenericArg::Const(value) = arguments[0] else {
        panic!("constant kind");
    };
    assert_eq!(program.types.const_usize(value), Some(4));
}

#[test]
fn const_aliases_and_symbolic_arrays_keep_the_parameter_identity() {
    let (_, program) = checked(
        "type Bytes<const usize N> = byte[N]; Bytes<4> f(Bytes<4> value) { return value; }",
    );
    assert!(matches!(
        program.types.get(program.functions[0].result),
        Ty::Array { length: 4, .. }
    ));
    assert!(
        program
            .types
            .values()
            .iter()
            .any(|ty| matches!(ty, Ty::SymbolicArray { .. }))
    );
    assert!(
        program
            .definitions
            .iter()
            .any(|d| d.generic_parameter_kinds == [GenericParamKind::Const])
    );
}

#[test]
fn concrete_aliases_evaluate_dependent_const_calls_before_type_comparison() {
    checked(
        "const usize twice(usize value) { return value * 2; } type Bytes<const usize N> = byte[twice(N)]; byte[6] f(Bytes<3> value) { return value; }",
    );
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("alias-overflow.cavo", "const usize twice(usize value) { return value * 2; } type Bytes<const usize N> = byte[twice(N)]; void f(Bytes<18446744073709551615> value) {}".into()).unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-CONST-EVAL"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn direct_array_shapes_infer_type_and_const_arguments() {
    let (_, program) = checked(
        "T[N] identity<T, const usize N>(T[N] value) { return move value; } i32[3] f(i32[3] value) { return identity(move value); }",
    );
    let call = program.functions[1]
        .expressions
        .iter()
        .find_map(|e| match &e.kind {
            hir::ExprKind::Call { type_arguments, .. } => Some(type_arguments),
            _ => None,
        })
        .unwrap();
    assert!(matches!(call[0], GenericArg::Type(_)));
    let GenericArg::Const(value) = call[1] else {
        panic!("constant inferred");
    };
    assert_eq!(program.types.const_usize(value), Some(3));
}

#[test]
fn record_literals_infer_generic_fields_and_respect_expected_array_lengths() {
    checked(
        "struct Ring<T, const usize N> { T[N] data; } i32 f() { Ring<i32, 4> value = Ring { data: [7; 4] }; auto inferred = Ring { data: [1; 3] }; return value.data[0] + inferred.data[0]; }",
    );
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("record-count.cavo", "struct Ring<T, const usize N> { T[N] data; } void f() { Ring<i32, 4> value = Ring { data: [7; 3] }; }".into()).unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| matches!(d.code, "E-TYPE-MISMATCH" | "E-TYPE-INFER"))
    );
}

#[test]
fn generic_alias_record_literals_and_unit_variants_use_expected_types() {
    checked(
        "struct Ring<T, const usize N> { T[N] data; } type Packet<T, const usize N> = Ring<T, N>; enum Maybe<T> { None, Some(T) } void f() { Packet<i32, 4> packet = Packet { data: [1; 4] }; Maybe<i32> empty = Maybe::None; }",
    );
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add(
            "unit-inference.cavo",
            "enum Maybe<T> { None, Some(T) } void f() { auto empty = Maybe::None; }".into(),
        )
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-TYPE-INFER")
    );
}

#[test]
fn local_runtime_shadow_is_not_a_generic_constant() {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add(
            "shadow.cavo",
            "void f<const usize N>() { usize N = 4; byte[N] value; }".into(),
        )
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-CONST-CONTEXT")
    );
}

#[test]
fn const_kind_and_target_type_mismatches_do_not_become_zero() {
    for source in [
        "struct Bad<const u32 N> { byte[N] value; }",
        "const u32 SIZE = 4; type Bytes<const usize N> = byte[N]; void f(Bytes<SIZE> value) {}",
        "type Bytes<const usize N> = byte[N]; void f(Bytes<bool> value) {}",
    ] {
        let mut compilation = Compilation::default();
        let file = compilation.sources.add("kind.cavo", source.into()).unwrap();
        compilation.parse(file);
        assert!(compilation.check_types().is_none(), "{source}");
        assert!(!compilation.diagnostics.is_empty());
    }
}

#[test]
fn dependent_record_assertions_are_checked_at_concrete_use() {
    checked(
        "struct Buffer<const usize N> { static_assert(N > 0, \"empty capacity\"); byte[N] data; } void f(Buffer<4> value) {}",
    );
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("assert.cavo", "struct Buffer<const usize N> { static_assert(N > 0, \"empty capacity\"); byte[N] data; } void f(Buffer<0> value) {}".into()).unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-CONST-ASSERT" && d.message.contains("empty capacity"))
    );
}

#[test]
fn module_assertions_never_inherit_an_unrelated_generic_binder() {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add(
            "assert-scope.cavo",
            "void f<const usize N>() {} static_assert(N > 0);".into(),
        )
        .unwrap();
    compilation.parse(file);
    assert!(compilation.check_types().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-CONST-CONTEXT" || d.code == "E-NAME-UNKNOWN")
    );
}

#[test]
fn lifetime_substitution_does_not_capture_an_inner_callable_binder() {
    use cavo_compiler::types::{Region, TypeContext};
    let mut symbols = cavo_compiler::symbol::Interner::default();
    let name = symbols.intern("a");
    let owner = hir::DefId(0);
    let mut types = TypeContext::new();
    types.register_generic_parameters(owner, &[(name, GenericParamKind::Lifetime)]);
    let outer = types.intern(Ty::Reference {
        region: Region::Named { owner, name },
        mutable: false,
        inner: TyId::BOOL,
    });
    let inner = types.intern(Ty::Reference {
        region: Region::Bound { depth: 0, index: 0 },
        mutable: false,
        inner: TyId::BOOL,
    });
    let function = types.intern(Ty::Function {
        parameters: vec![inner],
        result: outer,
    });
    let template = types.intern(Ty::ForAll {
        parameters: 1,
        inner: function,
    });
    let result = types
        .substitute_generics(
            template,
            owner,
            &[GenericArg::Lifetime(Region::Bound { depth: 0, index: 0 })],
        )
        .unwrap();
    let Ty::ForAll {
        inner: function, ..
    } = *types.get(result)
    else {
        panic!("binder");
    };
    let Ty::Function { parameters, result } = types.get(function) else {
        panic!("function");
    };
    assert!(matches!(
        types.get(parameters[0]),
        Ty::Reference {
            region: Region::Bound { depth: 0, .. },
            ..
        }
    ));
    assert!(matches!(
        types.get(*result),
        Ty::Reference {
            region: Region::Bound { depth: 1, .. },
            ..
        }
    ));
}

#[test]
fn higher_ranked_aliases_keep_caller_and_inner_lifetimes_distinct() {
    use cavo_compiler::types::Region;
    let (_, program) = checked(
        "type View<'a> = for<'b> fn(&'b i32) -> &'a i32; type Outer = for<'c> fn(View<'c>) -> void;",
    );
    let Ty::ForAll { inner: outer, .. } = *program.types.get(program.definitions[1].ty) else {
        panic!("outer binder");
    };
    let Ty::Function { parameters, .. } = program.types.get(outer) else {
        panic!("outer function");
    };
    let Ty::ForAll { inner, .. } = *program.types.get(parameters[0]) else {
        panic!("inner binder");
    };
    let Ty::Function { parameters, result } = program.types.get(inner) else {
        panic!("inner function");
    };
    assert!(matches!(
        program.types.get(parameters[0]),
        Ty::Reference {
            region: Region::Bound { depth: 0, .. },
            ..
        }
    ));
    assert!(matches!(
        program.types.get(*result),
        Ty::Reference {
            region: Region::Bound { depth: 1, .. },
            ..
        }
    ));
}

#[test]
fn constant_normalization_obeys_short_circuit_before_failing_arithmetic() {
    use cavo_compiler::syntax::ast::BinaryOp;
    let mut types = cavo_compiler::types::TypeContext::new();
    let zero = types.const_value(0);
    let one = types.const_value(1);
    let ty = types.const_term(one).ty;
    let division = types
        .intern_const(ConstTerm {
            ty,
            kind: ConstKind::Binary {
                op: BinaryOp::Divide,
                left: one,
                right: zero,
            },
        })
        .unwrap();
    let comparison = types
        .intern_const(ConstTerm {
            ty: TyId::BOOL,
            kind: ConstKind::Binary {
                op: BinaryOp::Equal,
                left: division,
                right: zero,
            },
        })
        .unwrap();
    let no = types.const_bool(false);
    let root = types
        .intern_const(ConstTerm {
            ty: TyId::BOOL,
            kind: ConstKind::Binary {
                op: BinaryOp::And,
                left: no,
                right: comparison,
            },
        })
        .unwrap();
    let normalized = types.normalize_const(root).unwrap();
    assert!(matches!(
        types.const_term(normalized).kind,
        ConstKind::Value(ConstValue::Bool(false))
    ));
    assert!(types.normalize_const(division).is_err());
}
