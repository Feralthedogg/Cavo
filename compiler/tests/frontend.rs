use cavo_compiler::{
    Compilation, hir,
    source::{SourceMap, Span},
    symbol::Interner,
    syntax::{
        ast::{self, BinaryOp, ExprKind, ItemKind},
        lexer,
        token::{Keyword, TokenKind},
    },
    types::Ty,
};

fn parse(text: &str) -> Compilation {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("test.cavo", text.to_owned())
        .unwrap();
    compilation.parse(file);
    compilation
}
fn checked(text: &str) -> (Compilation, Option<hir::Program>) {
    let mut compilation = parse(text);
    let hir = compilation.check();
    (compilation, hir)
}
fn passes(text: &str) -> hir::Program {
    let (compilation, hir) = checked(text);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    hir.unwrap()
}
fn fails(text: &str, code: &str) {
    let (compilation, hir) = checked(text);
    assert!(hir.is_none());
    assert!(
        compilation.diagnostics.iter().any(|d| d.code == code),
        "expected {code}: {:#?}",
        compilation.diagnostics
    );
}

#[test]
fn utf8_spans_nested_comments_and_lifetimes() {
    let text = "/* 바깥 /* 안 */ 끝 */ &'a str label = \"한\\n글\"; char c = '\\u{1f600}';";
    let compilation = parse(text);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:?}",
        compilation.diagnostics
    );
    let mut sources = SourceMap::default();
    let file = sources.add("unicode.cavo", text.to_owned()).unwrap();
    let mut diagnostics = Vec::new();
    let mut symbols = Interner::default();
    let tokens = lexer::lex(sources.file(file), &mut symbols, &mut diagnostics);
    assert!(diagnostics.is_empty());
    assert_eq!(tokens[0].kind, TokenKind::Amp);
    assert!(matches!(tokens[1].kind, TokenKind::Lifetime(_)));
    for token in tokens {
        assert!(text.is_char_boundary(token.span.start as usize));
        assert!(text.is_char_boundary(token.span.end as usize));
        assert!(token.span.end as usize <= text.len());
    }
}

#[test]
fn source_columns_handle_unicode_crlf_and_arbitrary_byte_offsets() {
    let mut sources = SourceMap::default();
    let file = sources.add("location.cavo", "가x\r\ny\n".into()).unwrap();
    let source = sources.file(file);
    assert_eq!(source.location(3), (1, 2));
    assert_eq!(source.location(1), (1, 1));
    assert_eq!(source.location(6), (2, 1));
    assert_eq!(source.line(1), "가x");
    assert_eq!(source.location(8), (3, 1));
}

#[test]
fn malformed_utf8_escape_is_a_diagnostic_not_a_panic() {
    fails("&str text() { return \"\\한\"; }", "E-LEX-003");
    fails("char c() { return ''; }", "E-LEX-003");
    fails("char c() { return '\\u{d800}'; }", "E-LEX-003");
    fails("i32 f() { /* open", "E-LEX-002");
}

#[test]
fn lexer_uses_longest_operator_and_distinguishes_char_lifetime() {
    let mut sources = SourceMap::default();
    let file = sources
        .add("tokens", ">>= >> > <= :: -> => 'a' 'static".into())
        .unwrap();
    let mut symbols = Interner::default();
    let mut diagnostics = Vec::new();
    let tokens = lexer::lex(sources.file(file), &mut symbols, &mut diagnostics);
    let kinds: Vec<_> = tokens.iter().map(|t| t.kind).collect();
    assert_eq!(
        &kinds[..7],
        &[
            TokenKind::ShiftRightEqual,
            TokenKind::ShiftRight,
            TokenKind::Greater,
            TokenKind::LessEqual,
            TokenKind::ColonColon,
            TokenKind::Arrow,
            TokenKind::FatArrow
        ]
    );
    assert_eq!(kinds[7], TokenKind::Char);
    assert!(matches!(kinds[8], TokenKind::Lifetime(_)));
    assert!(diagnostics.is_empty());
}

#[test]
fn precedence_and_explicit_comparison_grouping_are_preserved() {
    let compilation = parse("i32 f() { return 1 + 2 * 3 << 1; }");
    assert!(compilation.diagnostics.is_empty());
    let ItemKind::Function(function) = &compilation.ast.items[0].kind else {
        panic!()
    };
    let ast::StmtKind::Return(Some(root)) = compilation
        .ast
        .stmt(function.body.as_ref().unwrap().statements[0])
        .kind
    else {
        panic!()
    };
    let ExprKind::Binary {
        op: BinaryOp::ShiftLeft,
        left,
        ..
    } = compilation.ast.expr(root).kind
    else {
        panic!()
    };
    let ExprKind::Binary {
        op: BinaryOp::Add,
        right,
        ..
    } = compilation.ast.expr(left).kind
    else {
        panic!()
    };
    assert!(matches!(
        compilation.ast.expr(right).kind,
        ExprKind::Binary {
            op: BinaryOp::Multiply,
            ..
        }
    ));
    fails(
        "bool f(i32 a, i32 b, i32 c) { return a < b < c; }",
        "E-PARSE-CHAIN",
    );
    passes("bool f(i32 a, i32 b) { return (a < b) == true; }");
}

#[test]
fn nested_generic_closers_do_not_change_shift_operators() {
    let text = "struct Wrap<T> { T value; } Wrap<Wrap<u32>> nested(Wrap<Wrap<u32>> value) { return move value; } u32 shift(u32 x) { return x >> 1; }";
    passes(text);
}

#[test]
fn parses_the_contract_concurrency_and_ffi_surface() {
    let text = r#"
        module syntax::coverage;
        import std::io;
        @repr(C) pub struct Pair<T> { pub T left; T right; }
        union Bits { u32 bits; f32 value; }
        enum Result<T, E> { Ok(T), Err(E) }
        trait Hash { u64 hash(&Self self); }
        impl Hash for Bits { u64 hash(&Self self) { return 0; } }
        contract impl Send for Bits because "owned, thread independent";
        contract NonEmpty<T>(&[T] data) { requires data.len() > 0; }
        extern "C" { @effects(ffi) usize count(ptr<const byte> p, usize n); }
        @nopreempt u32 load(ptr<const u32> p) requires Readable<u32>(p, 1) {
            contract { assume Readable<u32>(p, 1) because "owner lease"; return ptr::read(p); }
        }
        &'a T first<'a, T>(&'a [T] data) { return &data[0]; }
        void work() {
            scope requests { auto child = spawn load(null)?; defer { cleanup(); } }
            auto closure = [move value, &settings](i32 n) -> i32 { return n; };
            auto state = match (value) { Some(x) if x > 0 => x, _ => 0 };
        }
    "#;
    let compilation = parse(text);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    assert_eq!(compilation.ast.modules.len(), 1);
    assert!(
        compilation
            .ast
            .items
            .iter()
            .any(|item| matches!(item.kind, ItemKind::Contract { .. }))
    );
}

#[test]
fn spawn_question_mark_applies_to_spawn_not_child_call() {
    let compilation = parse("void f() { auto child = spawn make()?; }");
    assert!(compilation.diagnostics.is_empty());
    assert!(compilation.ast.expressions.iter().any(|e| matches!(e.kind, ExprKind::Try(inner) if matches!(compilation.ast.expr(inner).kind, ExprKind::Unary { op: ast::UnaryOp::Spawn, .. }))));
}

#[test]
fn parser_recovers_to_the_next_statement_and_function() {
    let compilation = parse("i32 bad() { i32 value = ; return 0; } i32 good() { return 2; }");
    assert!(!compilation.diagnostics.is_empty());
    assert_eq!(compilation.ast.modules[0].items.len(), 2);
    let item = compilation.ast.item(compilation.ast.modules[0].items[1]);
    assert_eq!(compilation.symbols.get(item.name.unwrap().symbol), "good");
}

#[test]
fn parser_limits_nesting_and_error_volume() {
    let source = format!(
        "i32 f() {{ return {}1{}; }}",
        "(".repeat(300),
        ")".repeat(300)
    );
    let compilation = parse(&source);
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-PARSE-DEPTH")
    );
    assert!(compilation.diagnostics.len() <= 100);
    let compilation = parse(&"💥".repeat(500));
    assert!(compilation.diagnostics.len() <= 100);
}

#[test]
fn checking_handles_forward_calls_mutation_branches_and_for_loops() {
    let hir = passes(
        "i32 main() { i32 total = add(1, 2); for (i32 i = 0; i < 5; i += 1) { total += i; } if (total > 0) { return total; } else { return 0; } } i32 add(i32 a, i32 b) { return a + b; }",
    );
    assert_eq!(hir.functions.len(), 2);
    assert_eq!(hir.stage, hir::ValidationStage::Types);
    assert!(
        hir.functions[0]
            .expressions
            .iter()
            .any(|e| matches!(e.kind, hir::ExprKind::Call { .. }))
    );
}

#[test]
fn typed_hir_records_generic_instantiation_and_move_operations() {
    let hir = passes(
        "T identity<T>(T value) { return move value; } u64 main() { return identity::<u64>(42); }",
    );
    assert!(hir.functions[0].expressions.iter().any(|e| matches!(
        e.kind,
        hir::ExprKind::Unary {
            op: ast::UnaryOp::Move,
            ..
        }
    )));
    let main = &hir.functions[1];
    assert!(main.expressions.iter().any(|expression| {
        let hir::ExprKind::Call { type_arguments, .. } = &expression.kind else {
            return false;
        };
        matches!(type_arguments.as_slice(), [cavo_compiler::types::GenericArg::Type(ty)]
            if matches!(hir.types.get(*ty), Ty::Integer { signed: false, bits: 64 }))
    }));
}

#[test]
fn array_reference_coercion_is_explicit_in_hir() {
    let hir = passes(
        "u64 first(&[u64] data) { return data[0]; } u64 main() { u64[2] values = [1, 2]; return first(&values); }",
    );
    assert!(
        hir.functions[1]
            .expressions
            .iter()
            .any(|e| matches!(e.kind, hir::ExprKind::CoerceArrayToSlice(_)))
    );
    passes(
        "u32 sum() { u32[3] data = [1, 2, 3]; u32 total = 0; for (auto value in data) { total += value; } return total; }",
    );
}

#[test]
fn records_and_enum_constructors_resolve_to_definition_ids() {
    let hir = passes(
        "struct Point { f64 x; f64 y; } f64 value() { Point p = Point { y: 2.0, x: 1.0 }; return p.x; } enum Maybe<T> { None, Some(T) } Maybe<i32> some() { return Maybe::Some::<i32>(7); }",
    );
    let fields = hir.functions[0]
        .expressions
        .iter()
        .find_map(|e| {
            if let hir::ExprKind::Record { fields, .. } = &e.kind {
                Some(fields)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(
        fields.iter().map(|(index, _)| *index).collect::<Vec<_>>(),
        [1, 0]
    );
}

#[test]
fn module_imports_and_privacy_are_checked_across_files() {
    fn multiple(public: bool) -> Compilation {
        let mut c = Compilation::default();
        let prefix = if public { "pub " } else { "" };
        let a = c
            .sources
            .add(
                "math.cavo",
                format!("module sample::math; {prefix}i32 add(i32 a, i32 b) {{ return a + b; }}"),
            )
            .unwrap();
        let b = c
            .sources
            .add(
                "app.cavo",
                "module sample::app; import sample::math; i32 main() { return math::add(2, 3); }"
                    .into(),
            )
            .unwrap();
        c.parse(a);
        c.parse(b);
        c
    }
    let mut c = multiple(true);
    assert!(c.check().is_some(), "{:?}", c.diagnostics);
    let mut c = multiple(false);
    assert!(c.check().is_none());
    assert!(c.diagnostics.iter().any(|d| d.code == "E-NAME-PRIVATE"));
}

#[test]
fn unknown_duplicate_and_wrong_kind_names_are_errors() {
    fails("i32 f() { return missing; }", "E-NAME-UNKNOWN");
    fails(
        "i32 f() { return 0; } i32 f() { return 1; }",
        "E-NAME-DUPLICATE",
    );
    fails("void f() { i32 x = 0; i32 x = 1; }", "E-NAME-DUPLICATE");
    fails("struct A {} i32 f() { return A; }", "E-TYPE-VALUE");
    fails("import absent::library; void f() {}", "E-NAME-MODULE");
}

#[test]
fn type_errors_are_not_coerced_or_silenced() {
    fails("i32 f() { return true; }", "E-TYPE-MISMATCH");
    fails("void f() { if (1) {} }", "E-TYPE-MISMATCH");
    fails(
        "i32 f(i32 x) { return x; } i32 main() { return f(); }",
        "E-CALL-ARITY",
    );
    fails("void f() { i32 x = 1; x(); }", "E-TYPE-CALL");
    fails("i32 f() { i64 x = 2; return x; }", "E-TYPE-MISMATCH");
}

#[test]
fn definite_initialization_merges_only_reachable_paths() {
    fails(
        "i32 f(bool c) { i32 value; if (c) { value = 1; } return value; }",
        "E-INIT-READ",
    );
    passes("i32 f(bool c) { i32 value; if (c) { value = 1; } else { value = 2; } return value; }");
    passes("i32 f(bool c) { i32 value; if (c) { return 1; } else { value = 2; } return value; }");
    fails(
        "i32 f() { i32 value; while (false) { value = 1; } return value; }",
        "E-INIT-READ",
    );
    fails("void f() { auto value; }", "E-TYPE-INFER");
}

#[test]
fn const_bindings_places_and_loop_controls_are_checked() {
    passes("i32 f() { const i32 x; x = 1; return x; }");
    fails("void f() { const i32 x = 0; x = 1; }", "E-ASSIGN-CONST");
    fails(
        "void f() { const i32 x; while (true) { x = 1; } }",
        "E-ASSIGN-CONST",
    );
    fails("void f() { 1 = 2; }", "E-ASSIGN-PLACE");
    fails("void f() { break; }", "E-CONTROL-LOOP");
    fails(
        "i32 f(bool condition) { if (condition) { return 1; } }",
        "E-RETURN-MISSING",
    );
    fails(
        "void f() { const i32 x = 0; auto p = &mut x; }",
        "E-BORROW-MUTABLE",
    );
}

#[test]
fn numeric_literal_ranges_and_unicode_values_are_validated() {
    passes(
        "i8 low() { return -128; } u128 high() { return 340282366920938463463374607431768211455; } char face() { return '\\u{1f600}'; } &str hello() { return \"한글\\n\"; }",
    );
    fails("i8 f() { return 128; }", "E-LITERAL-001");
    fails("u8 f() { return -1; }", "E-LITERAL-001");
    fails("i32 f() { return 1oops; }", "E-LITERAL-001");
    fails("f32 f() { return 1e100; }", "E-LITERAL-001");
    fails("u8 f() { return 0b2; }", "E-LEX-004");
}

#[test]
fn array_record_and_by_value_cycles_have_diagnostics() {
    fails(
        "i32 f() { i32[2] values = [1, 2]; return values[2]; }",
        "E-INDEX-BOUNDS",
    );
    fails(
        "struct P { i32 x; i32 y; } P f() { return P { x: 1 }; }",
        "E-FIELD-MISSING",
    );
    fails(
        "struct P { i32 x; } P f() { return P { x: 1, x: 2 }; }",
        "E-FIELD-DUPLICATE",
    );
    fails("struct Node { Node next; }", "E-TYPE-RECURSIVE");
    passes("struct Node { ptr<Node> next; }");
}

#[test]
fn contracts_are_retained_as_typed_unproven_clauses() {
    let hir = passes(
        "u32 inc(u32 value) requires value < 100 ensures result == old(value) + 1 { return value + 1; }",
    );
    assert_eq!(hir.functions[0].clauses.len(), 2);
    assert!(
        hir.functions[0]
            .expressions
            .iter()
            .any(|e| matches!(e.kind, hir::ExprKind::Old(_)))
    );
    assert_eq!(hir.stage, hir::ValidationStage::Types);
}

#[test]
fn implemented_match_and_traits_check_while_future_stage_features_fail_closed() {
    passes("void f() { scope {} }");
    passes("void f() { contract {} }");
    passes("i32 f(i32 value) { return match (value) { _ => 0 }; }");
    passes("trait T { void f(&Self self); }");
}

#[test]
fn successful_hir_has_in_bounds_types_and_original_source_spans() {
    let (compilation, hir) = checked("i64 double(i64 x) { return x + x; }");
    let hir = hir.unwrap();
    for function in &hir.functions {
        for expression in &function.expressions {
            assert!((expression.ty.0 as usize) < hir.types.values().len());
            let source = compilation.sources.file(expression.span.file);
            assert!(
                source
                    .text()
                    .is_char_boundary(expression.span.start as usize)
            );
            assert!(source.text().is_char_boundary(expression.span.end as usize));
            assert!(!source.slice(expression.span).is_empty());
        }
    }
    let file = compilation.sources.files()[0].id;
    assert_eq!(
        compilation.sources.file(file).slice(Span::new(file, 0, 3)),
        "i64"
    );
}

#[test]
fn adversarial_token_sequences_do_not_panic_or_loop_forever() {
    let fragments = [
        "}", "(", "/*", "'", "\\", "💥", "<", ">>", "@", "const", "fn", "[", "\"\\é\"",
    ];
    let mut state = 0x17a5_u64;
    for _ in 0..250 {
        let mut source = String::new();
        for _ in 0..30 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            source.push_str(fragments[(state as usize) % fragments.len()]);
            source.push(' ');
        }
        let mut compilation = parse(&source);
        compilation.check();
        assert!(compilation.diagnostics.len() <= 100);
    }
}

#[test]
fn keyword_bool_is_not_an_identifier() {
    let compilation = parse("bool f() { return true; }");
    assert!(compilation.diagnostics.is_empty());
    assert_eq!(Keyword::from_text("true"), Some(Keyword::True));
}

#[test]
fn references_function_pointers_and_return_context_type_inference() {
    passes(
        "i32 read(&i32 value) { return *value; } i32 apply(fn(i32) -> i32 operation, i32 value) { return operation(value); } i32 twice(i32 value) { return value * 2; } i32 main() { return apply(twice, 3); }",
    );
    passes("T identity<T>(T value) { return move value; } u64 main() { return identity(42); }");
    passes("i32 f() { const i32 value; (value) = 4; return value; }");
    fails(
        "void f() { f64 value = 1.0; value &= 2.0; }",
        "E-TYPE-OPERATOR",
    );
    fails("extern \"C\" { void wrong(void value); }", "E-TYPE-SIZED");
    fails(
        "bool f(bool a, i32 b, i32 c) { return a == b < c; }",
        "E-PARSE-CHAIN",
    );
}

#[test]
fn hir_validation_rejects_invalid_ids_and_cycles_at_pass_boundaries() {
    let mut hir = passes("i32 twice(i32 x) { return x + x; }");
    assert!(hir.validate().is_ok());
    let index = hir.functions[0]
        .expressions
        .iter()
        .position(|e| matches!(e.kind, hir::ExprKind::Binary { .. }))
        .unwrap();
    let hir::ExprKind::Binary { ref mut left, .. } = hir.functions[0].expressions[index].kind
    else {
        panic!()
    };
    *left = hir::ExprId(index as u32);
    assert!(
        hir.validate()
            .unwrap_err()
            .to_string()
            .contains("cyclic body")
    );
    let hir::ExprKind::Binary { ref mut left, .. } = hir.functions[0].expressions[index].kind
    else {
        panic!()
    };
    *left = hir::ExprId(u32::MAX);
    assert!(
        hir.validate()
            .unwrap_err()
            .to_string()
            .contains("invalid body child ID")
    );
}

#[test]
fn hir_validation_checks_cycles_crossing_expression_and_statement_arenas() {
    let mut program = passes("i32 f() { 1; return 2; }");
    let function = &mut program.functions[0];
    let expression = function
        .statements
        .iter()
        .find_map(|statement| match statement.kind {
            hir::StmtKind::Expression(value) => Some(value),
            _ => None,
        })
        .unwrap();
    function.expressions[expression].kind = hir::ExprKind::BlockValue {
        body: function.body.clone(),
        value: None,
    };
    assert!(
        program
            .validate()
            .unwrap_err()
            .to_string()
            .contains("cyclic body")
    );
}

#[test]
fn namespace_declarations_require_double_colons_and_recover_after_dots() {
    passes("module example::math; pub i32 value() { return 1; }");
    fails(
        "module example.math; i32 value() { return 1; }",
        "E-PARSE-PATH",
    );
    let compilation = parse("import example.math; i32 value() { return 1; }");
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-PARSE-PATH")
    );
    assert!(
        compilation
            .ast
            .items
            .iter()
            .any(|item| matches!(item.kind, ItemKind::Function(_)))
    );
}

#[test]
fn type_aliases_are_transparent_forward_resolved_and_generic() {
    let program = passes(
        r#"
        type Values<T> = T[2];
        type Numbers = Values<Number>;
        type Operation = fn(Number, Number) -> Number;
        type Number = i64;
        Number add(Number a, Number b) { return a + b; }
        Number sum(Numbers values, Operation operation) {
            return operation(values[0], values[1]);
        }
        i64 main() { Numbers values = [20, 22]; return sum(values, add); }
    "#,
    );
    assert_eq!(program.functions[0].result, program.functions[2].result);
    assert!(program.validate().is_ok());
    passes(
        "struct Wrap<T> { T value; } type Nested<T> = Wrap<Wrap<T>>; Nested<i32> keep(Nested<i32> value) { return move value; }",
    );
}

#[test]
fn alias_references_freshen_inferred_regions_and_preserve_static_regions() {
    let program = passes(
        r#"
        type View<T> = &T;
        type Slice<T> = &[T];
        type Text = &'static str;
        type Callback<T> = fn(T) -> T;
        i32 add(View<i32> left, View<i32> right) { return *left + *right; }
        i32 first(Slice<i32> values) { return values[0]; }
        Text greeting() { return "hello"; }
        void accepts(Callback<&i32> callback) {}
        i32 main() { i32[2] values = [1, 2]; return first(&values); }
    "#,
    );
    let function = &program.functions[0];
    let Ty::Reference {
        region: left,
        inner: left_inner,
        ..
    } = program.types.get(function.locals[0].ty)
    else {
        panic!()
    };
    let Ty::Reference {
        region: right,
        inner: right_inner,
        ..
    } = program.types.get(function.locals[1].ty)
    else {
        panic!()
    };
    assert_ne!(left, right);
    assert_eq!(left_inner, right_inner);
    assert!(matches!(
        program.types.get(program.functions[2].result),
        Ty::Reference {
            region: cavo_compiler::types::Region::Static,
            ..
        }
    ));
    let callback = program.functions[3].locals[0].ty;
    let Ty::ForAll { inner, .. } = program.types.get(callback) else {
        panic!("anonymous callable references must be late bound");
    };
    let Ty::Function { parameters, result } = program.types.get(*inner) else {
        panic!()
    };
    assert_eq!(
        parameters[0], *result,
        "actual argument regions must remain shared"
    );
}

#[test]
fn aliases_keep_record_field_privacy_and_non_generic_enum_constructors() {
    passes(
        "struct Pair { i32 value; } type Alias = Pair; i32 main() { Alias pair = Alias { value: 42 }; return pair.value; }",
    );
    passes(
        "enum Choice { Left, Right } type Alias = Choice; i32 main() { Alias choice = Alias::Left; return 0; }",
    );
    let mut compilation = Compilation::default();
    for (path, text) in [
        (
            "math.cavo",
            "module sample::math; pub type Number = i64; type Hidden = i32; pub struct Pair { i64 secret; } pub type Alias = Pair;",
        ),
        (
            "app.cavo",
            "module sample::app; import sample::math; math::Number read(math::Number value) { return value; }",
        ),
    ] {
        let file = compilation.sources.add(path, text.into()).unwrap();
        compilation.parse(file);
    }
    assert!(
        compilation.check().is_some(),
        "{:?}",
        compilation.diagnostics
    );
    let file = compilation.sources.add("bad.cavo", "module sample::bad; import sample::math; math::Hidden hidden() { return 0; } void main() { auto pair = math::Alias { secret: 1 }; }".into()).unwrap();
    compilation.parse(file);
    assert!(compilation.check().is_none());
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.code == "E-NAME-PRIVATE")
    );
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|d| d.message == "cannot initialize private field")
    );
}

#[test]
fn aliases_reject_cycles_bad_arity_unknown_targets_and_invalid_contexts() {
    for source in [
        "type Self = Self;",
        "type Left = ptr<Right>; type Right = Left;",
        "type Recursive<T> = Recursive<T[1]>;",
    ] {
        fails(source, "E-TYPE-ALIAS-CYCLE");
    }
    fails("type Missing = Absent;", "E-NAME-UNKNOWN");
    fails("type Value<T> = T; Value f() { return 1; }", "E-TYPE-ARITY");
    fails(
        "type Value = i32; Value<i32> f() { return 1; }",
        "E-TYPE-ARITY",
    );
    fails("type Value = i32; struct Value {}", "E-NAME-DUPLICATE");
    fails(
        "type Value = i32; i32 f() { return Value; }",
        "E-TYPE-VALUE",
    );
    fails("type Empty = void; void f(Empty value) {}", "E-TYPE-SIZED");
    fails(
        "struct Record { i32 value; } type Alias<T> = Record; void f() { auto value = Alias { value: 1 }; }",
        "E-TYPE-INFER",
    );
    passes("type View<'a, T> = &'a T;");
}

#[test]
fn alias_expansion_limits_bound_dependency_depth_and_expanded_type_work() {
    let mut source = String::new();
    for index in 0..130 {
        source.push_str(&format!("type A{index} = A{};", index + 1));
    }
    source.push_str("type A130 = i32;");
    fails(&source, "E-TYPE-DEPTH");
    fails(
        &format!("type Deep = i32{};", "[1]".repeat(1000)),
        "E-TYPE-DEPTH",
    );
    let layers = "[1]".repeat(70);
    fails(
        &format!("type Layer<T> = T{layers}; type Deep = Layer<Layer<i32>>;"),
        "E-TYPE-ALIAS-LIMIT",
    );
    fails(
        &format!("type Layer = i32{layers}; type Deep = Layer{layers};"),
        "E-TYPE-ALIAS-LIMIT",
    );
    let mut source = String::from("type A0 = &i32;");
    for index in 1..16 {
        let previous = index - 1;
        source.push_str(&format!(
            "type A{index} = fn(A{previous}, A{previous}) -> void;"
        ));
    }
    passes(&source);
    let mut source = String::from("struct Pair<L,R> { L left; R right; } type A0 = &i32;");
    for index in 1..16 {
        let previous = index - 1;
        source.push_str(&format!("type A{index} = Pair<A{previous},A{previous}>;"));
    }
    fails(&source, "E-TYPE-ALIAS-LIMIT");
}

#[test]
fn separator_diagnostics_distinguish_namespaces_from_shadowing_values() {
    for source in [
        "struct Point { i32 x; } void f() { Point.make(); }",
        "type Number = i32; void f() { Number.make(); }",
        "void f() { ptr.read(null); }",
        "struct Point { i32 x; } i32 f(Point point) { return point::x; }",
    ] {
        fails(source, "E-NAME-SEPARATOR");
    }
    passes("struct Point { i32 x; } i32 f(Point Point) { return Point.x; }");
    let mut compilation = Compilation::default();
    for (path, text) in [
        (
            "math.cavo",
            "module sample::math; pub i32 answer() { return 42; }",
        ),
        (
            "app.cavo",
            "module sample::app; import sample::math; i32 main() { return math.answer(); }",
        ),
    ] {
        let file = compilation.sources.add(path, text.into()).unwrap();
        compilation.parse(file);
    }
    assert!(compilation.check().is_none());
    let diagnostic = compilation
        .diagnostics
        .iter()
        .find(|d| d.code == "E-NAME-SEPARATOR")
        .unwrap();
    assert!(
        diagnostic
            .helps
            .iter()
            .any(|note| note.contains("math::answer"))
    );
}

#[test]
fn joined_work_errors_can_be_named_without_flattening_result_layers() {
    let compilation = parse(
        "void f() { scope { auto child = spawn work()?; auto work_result = child.join()?; (move work_result)?; } }",
    );
    assert!(
        compilation.diagnostics.is_empty(),
        "{:?}",
        compilation.diagnostics
    );
    assert_eq!(
        compilation
            .ast
            .expressions
            .iter()
            .filter(|expression| matches!(expression.kind, ExprKind::Try(_)))
            .count(),
        3
    );
    let short = parse("void f() { child.join()??; }");
    assert!(short.diagnostics.is_empty());
    assert_eq!(
        short
            .ast
            .expressions
            .iter()
            .filter(|expression| matches!(expression.kind, ExprKind::Try(_)))
            .count(),
        2
    );
}
