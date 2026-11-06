use cavo_compiler::{
    Compilation, hir, mir,
    syntax::ast::{BinaryOp, UnaryOp},
};
use std::fmt::Write as _;

fn checked(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("mir.cavo", source.into()).unwrap();
    compilation.parse(file);
    let result = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (mut hir, mir) = result.expect("MIR compilation");
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Unit,
    Integer(i128),
    Bool(bool),
    Owned(&'static str),
    Fields(Vec<Option<Value>>),
    Variant(hir::DefId, Vec<Value>),
    Address(Slot),
    Function(hir::DefId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Slot {
    local: mir::LocalId,
    fields: Vec<usize>,
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Return(Value),
    Resume(mir::ExitKind),
}

/// A bounded MIR path observer, not a language runtime. Calls use explicit test
/// results; only owned tokens produce observable Drop events. Partial moves
/// remove individual field values so duplicate cleanup cannot pass silently.
struct Path<'a> {
    compilation: &'a Compilation,
    hir: &'a hir::Program,
    body: &'a mir::Body,
    values: Vec<Option<Value>>,
    live: Vec<bool>,
    scopes: Vec<mir::ScopeId>,
    inputs: &'a [(&'a str, Value)],
    results: &'a [(&'a str, Value)],
    writes: &'a [(&'a str, usize, Value)],
    failure: Option<(&'a str, mir::ExitKind)>,
    events: Vec<String>,
}

impl<'a> Path<'a> {
    fn new(
        compilation: &'a Compilation,
        hir: &'a hir::Program,
        program: &'a mir::Program,
        name: &str,
        inputs: &'a [(&'a str, Value)],
        results: &'a [(&'a str, Value)],
    ) -> Self {
        let body = program
            .functions
            .iter()
            .find(|body| {
                compilation
                    .symbols
                    .get(hir.definitions[body.definition.0 as usize].name)
                    == name
            })
            .expect("function");
        Self {
            compilation,
            hir,
            body,
            values: vec![None; body.locals.len()],
            live: vec![false; body.locals.len()],
            scopes: Vec::new(),
            inputs,
            results,
            writes: &[],
            failure: None,
            events: Vec::new(),
        }
    }

    fn slot_mut(&mut self, slot: &Slot) -> &mut Option<Value> {
        assert!(self.live[slot.local.0 as usize], "dead storage: {slot:?}");
        let mut value = &mut self.values[slot.local.0 as usize];
        for &field in &slot.fields {
            let fields = value.get_or_insert_with(|| Value::Fields(Vec::new()));
            let Value::Fields(fields) = fields else {
                panic!("field of scalar: {slot:?}");
            };
            fields.resize_with(fields.len().max(field + 1), || None);
            value = &mut fields[field];
        }
        value
    }

    fn resolve(&mut self, place: &mir::Place) -> Slot {
        let mut slot = Slot {
            local: place.local,
            fields: Vec::new(),
        };
        for projection in &place.projection {
            match *projection {
                mir::Projection::Downcast(_) => {
                    panic!("variant projections use the pattern observer")
                }
                mir::Projection::Field(index) => slot.fields.push(index as usize),
                mir::Projection::Index(index) => {
                    let Some(Value::Integer(index)) = self.values[index.0 as usize] else {
                        panic!("index is not initialized");
                    };
                    slot.fields.push(usize::try_from(index).unwrap());
                }
                mir::Projection::Deref => {
                    let Some(Value::Address(address)) = self.slot_mut(&slot) else {
                        panic!("dereference of non-address");
                    };
                    slot = address.clone();
                }
            }
        }
        slot
    }

    fn operand(&mut self, operand: &mir::Operand) -> Value {
        match operand {
            mir::Operand::ConstTerm { .. } => {
                panic!("symbolic constants require instantiation before observation")
            }
            mir::Operand::Constant { value, .. } => match value {
                hir::Constant::Integer {
                    magnitude,
                    negative,
                } => {
                    let value = i128::try_from(*magnitude).unwrap();
                    Value::Integer(if *negative { -value } else { value })
                }
                hir::Constant::Bool(value) => Value::Bool(*value),
                _ => panic!("constant outside path observer coverage"),
            },
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let slot = self.resolve(place);
                let value = self.slot_mut(&slot);
                if matches!(operand, mir::Operand::Move(_)) {
                    value.take().expect("move of uninitialized value")
                } else {
                    value.clone().expect("read of uninitialized value")
                }
            }
            mir::Operand::Function { definition, .. } => Value::Function(*definition),
            mir::Operand::Unit => Value::Unit,
        }
    }

    fn value(&mut self, value: &mir::Rvalue) -> Value {
        match value {
            mir::Rvalue::Use(value) => self.operand(value),
            mir::Rvalue::AddressOf(place) | mir::Rvalue::Borrow { place, .. } => {
                let slot = self.resolve(place);
                if matches!(value, mir::Rvalue::AddressOf(_)) {
                    self.named_event("capture", &slot);
                }
                Value::Address(slot)
            }
            mir::Rvalue::Binary { op, left, right } => {
                let left = self.operand(left);
                let right = self.operand(right);
                match (op, left, right) {
                    (BinaryOp::Add, Value::Integer(a), Value::Integer(b)) => Value::Integer(a + b),
                    (BinaryOp::Subtract, Value::Integer(a), Value::Integer(b)) => {
                        Value::Integer(a - b)
                    }
                    (BinaryOp::Less, Value::Integer(a), Value::Integer(b)) => Value::Bool(a < b),
                    (BinaryOp::Equal, a, b) => Value::Bool(a == b),
                    (BinaryOp::NotEqual, a, b) => Value::Bool(a != b),
                    other => panic!("operation outside path observer coverage: {other:?}"),
                }
            }
            mir::Rvalue::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                let Value::Bool(value) = self.operand(operand) else {
                    panic!("not bool");
                };
                Value::Bool(!value)
            }
            mir::Rvalue::Array(values) => Value::Fields(
                values
                    .iter()
                    .map(|value| Some(self.operand(value)))
                    .collect(),
            ),
            mir::Rvalue::Record { fields, .. } => {
                let mut values = vec![None; fields.len()];
                for (index, value) in fields {
                    values[*index as usize] = Some(self.operand(value));
                }
                Value::Fields(values)
            }
            mir::Rvalue::Variant { definition, fields } => Value::Variant(
                *definition,
                fields.iter().map(|value| self.operand(value)).collect(),
            ),
            mir::Rvalue::ArrayToSlice(value) => self.operand(value),
            other => panic!("rvalue outside path observer coverage: {other:?}"),
        }
    }

    fn named_event(&mut self, event: &str, slot: &Slot) {
        if let Some(name) = self.body.local(slot.local).name {
            let name = self.compilation.symbols.get(name);
            let fields = slot
                .fields
                .iter()
                .map(|index| format!(".{index}"))
                .collect::<String>();
            self.events.push(format!("{event}:{name}{fields}"));
        }
    }

    fn assign(&mut self, destination: &mir::Place, value: Value) {
        let slot = self.resolve(destination);
        self.named_event("write", &slot);
        *self.slot_mut(&slot) = Some(value);
    }

    fn dropped(&mut self, value: Value) {
        match value {
            Value::Owned(name) => self.events.push(format!("drop:{name}")),
            Value::Fields(fields) => {
                for value in fields.into_iter().flatten() {
                    self.dropped(value);
                }
            }
            Value::Variant(_, fields) => {
                for value in fields {
                    self.dropped(value);
                }
            }
            _ => {}
        }
    }

    fn run(&mut self) -> Outcome {
        let mut next = self.body.entry;
        for _ in 0..4096 {
            let block = self.body.block(next);
            for statement in &block.statements {
                match &statement.kind {
                    mir::StatementKind::IteratorStart { .. } => {
                        panic!("owned iteration uses the pattern observer")
                    }
                    mir::StatementKind::EnterScope(scope) => self.scopes.push(*scope),
                    mir::StatementKind::ExitScope(scope) => {
                        assert_eq!(self.scopes.pop(), Some(*scope))
                    }
                    mir::StatementKind::StorageLive(local) => {
                        assert!(!self.live[local.0 as usize]);
                        self.live[local.0 as usize] = true;
                    }
                    mir::StatementKind::StorageDead(local) => {
                        assert!(self.live[local.0 as usize]);
                        self.live[local.0 as usize] = false;
                        self.values[local.0 as usize] = None;
                    }
                    mir::StatementKind::Argument(local) => {
                        let name = self
                            .compilation
                            .symbols
                            .get(self.body.local(*local).name.unwrap());
                        let value = self
                            .inputs
                            .iter()
                            .find(|(key, _)| *key == name)
                            .unwrap()
                            .1
                            .clone();
                        self.values[local.0 as usize] = Some(value);
                    }
                    mir::StatementKind::Assign { destination, value } => {
                        let value = self.value(value);
                        self.assign(destination, value);
                    }
                }
            }
            next = match &block.terminator {
                mir::Terminator::Goto(next) => *next,
                mir::Terminator::Switch { condition, yes, no } => match self.operand(condition) {
                    Value::Bool(true) => *yes,
                    Value::Bool(false) => *no,
                    other => panic!("switch condition: {other:?}"),
                },
                mir::Terminator::Call {
                    callee,
                    arguments,
                    destination,
                    normal,
                    panic,
                    cancel,
                    ..
                } => {
                    let Value::Function(definition) = self.operand(callee) else {
                        panic!("callee is not a function");
                    };
                    let name = self
                        .compilation
                        .symbols
                        .get(self.hir.definitions[definition.0 as usize].name);
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.operand(argument))
                        .collect::<Vec<_>>();
                    self.events.push(format!("call:{name}"));
                    for (callee, index, value) in self.writes {
                        if *callee == name {
                            let Value::Address(slot) = &arguments[*index] else {
                                panic!("call write needs a reference argument");
                            };
                            *self.slot_mut(slot) = Some(value.clone());
                        }
                    }
                    match self.failure.filter(|(callee, _)| *callee == name) {
                        Some((_, mir::ExitKind::Panic)) => *panic,
                        Some((_, mir::ExitKind::Cancel)) => *cancel,
                        Some((_, mir::ExitKind::Normal)) => panic!("normal is not a failure"),
                        None => {
                            let value = self
                                .results
                                .iter()
                                .find(|(key, _)| *key == name)
                                .map_or(Value::Unit, |(_, value)| value.clone());
                            self.assign(destination, value);
                            *normal
                        }
                    }
                }
                mir::Terminator::Checked {
                    value,
                    destination,
                    normal,
                    ..
                } => {
                    let value = self.value(value);
                    self.assign(destination, value);
                    *normal
                }
                mir::Terminator::Bounds { normal, .. } => *normal,
                mir::Terminator::Drop { place, next, .. } => {
                    let slot = self.resolve(place);
                    if let Some(value) = self.slot_mut(&slot).take() {
                        self.dropped(value);
                    }
                    *next
                }
                mir::Terminator::Return => {
                    assert!(self.scopes.is_empty());
                    return Outcome::Return(
                        self.values[self.body.return_local.0 as usize]
                            .take()
                            .unwrap_or(Value::Unit),
                    );
                }
                mir::Terminator::Resume(reason) => {
                    assert!(self.scopes.is_empty());
                    return Outcome::Resume(*reason);
                }
                other => panic!("unexpected terminal: {other:?}"),
            };
        }
        panic!("MIR path exceeded step budget");
    }

    fn drops(&self) -> Vec<&str> {
        self.events
            .iter()
            .filter_map(|event| event.strip_prefix("drop:"))
            .collect()
    }

    fn calls(&self) -> Vec<&str> {
        self.events
            .iter()
            .filter_map(|event| event.strip_prefix("call:"))
            .collect()
    }
}

#[test]
fn returning_a_partial_move_preserves_the_return_value_and_drops_only_its_sibling() {
    let (compilation, hir, mir) = checked(
        "struct Pair<T> { T left; T right; } T f<T>(Pair<T> pair) { T first = move pair.left; return move pair.right; }",
    );
    let inputs = [(
        "pair",
        Value::Fields(vec![
            Some(Value::Owned("left")),
            Some(Value::Owned("right")),
        ]),
    )];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &[]);
    assert_eq!(path.run(), Outcome::Return(Value::Owned("right")));
    assert_eq!(path.drops(), ["left"]);
}

#[test]
fn cleanup_reverses_locals_but_preserves_record_field_order() {
    let (compilation, hir, mir) = checked(
        "struct Pair<T> { T left; T right; } void f<T>(T a, Pair<T> pair, T b) { T first = move a; Pair<T> middle = move pair; T last = move b; }",
    );
    let inputs = [
        ("a", Value::Owned("first")),
        (
            "pair",
            Value::Fields(vec![
                Some(Value::Owned("left")),
                Some(Value::Owned("right")),
            ]),
        ),
        ("b", Value::Owned("last")),
    ];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &[]);
    assert_eq!(path.run(), Outcome::Return(Value::Unit));
    assert_eq!(path.drops(), ["last", "left", "right", "first"]);
}

#[test]
fn early_return_does_not_register_later_locals() {
    let (compilation, hir, mir) = checked(
        "void f<T>(T a, T b, bool early) { T first = move a; if (early) { return; } T later = move b; }",
    );
    for early in [true, false] {
        let inputs = [
            ("a", Value::Owned("a")),
            ("b", Value::Owned("b")),
            ("early", Value::Bool(early)),
        ];
        let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &[]);
        assert_eq!(path.run(), Outcome::Return(Value::Unit));
        assert_eq!(path.drops(), if early { ["a", "b"] } else { ["b", "a"] });
    }
}

#[test]
fn call_failure_keeps_the_old_assignment_value_and_never_initializes_its_result() {
    let (compilation, hir, mir) = checked(
        "T make<T>(T input) { return move input; } void f<T>(T old, T replacement) { old = make(move replacement); }",
    );
    let inputs = [
        ("old", Value::Owned("old")),
        ("replacement", Value::Owned("replacement")),
    ];
    let results = [("make", Value::Owned("new"))];
    for reason in [
        mir::ExitKind::Normal,
        mir::ExitKind::Panic,
        mir::ExitKind::Cancel,
    ] {
        let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &results);
        path.failure = (reason != mir::ExitKind::Normal).then_some(("make", reason));
        if reason == mir::ExitKind::Normal {
            assert_eq!(path.run(), Outcome::Return(Value::Unit));
            assert_eq!(path.drops(), ["old", "new"]);
        } else {
            assert_eq!(path.run(), Outcome::Resume(reason));
            assert_eq!(path.drops(), ["old"]);
        }
    }
}

#[test]
fn later_argument_failure_cleans_the_completed_earlier_argument() {
    let (compilation, hir, mir) = checked(
        "T first<T>(T x) { return move x; } i32 second() { return 2; } void use<T>(T x, i32 n) {} void f<T>(T input) { use(first(move input), second()); }",
    );
    let inputs = [("input", Value::Owned("input"))];
    let results = [
        ("first", Value::Owned("temporary")),
        ("second", Value::Integer(2)),
    ];
    for reason in [mir::ExitKind::Panic, mir::ExitKind::Cancel] {
        let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &results);
        path.failure = Some(("second", reason));
        assert_eq!(path.run(), Outcome::Resume(reason));
        assert_eq!(path.calls(), ["first", "second"]);
        assert_eq!(path.drops(), ["temporary"]);
    }
}

#[test]
fn short_circuit_does_not_consume_an_untaken_argument() {
    let (compilation, hir, mir) = checked(
        "bool take<T>(T value) { return true; } T f<T>(T value) { bool result = false && take(move value); return move value; }",
    );
    let inputs = [("value", Value::Owned("returned"))];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &[]);
    assert_eq!(path.run(), Outcome::Return(Value::Owned("returned")));
    assert!(path.calls().is_empty());
    assert!(path.drops().is_empty());
}

#[test]
fn record_initializers_follow_source_order_even_when_fields_are_reordered() {
    let (compilation, hir, mir) = checked(
        "struct Pair { i32 left; i32 right; } i32 first() { return 1; } i32 second() { return 2; } i32 f() { Pair pair = Pair { right: second(), left: first() }; return pair.left + pair.right; }",
    );
    let results = [("first", Value::Integer(1)), ("second", Value::Integer(2))];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &[], &results);
    assert_eq!(path.run(), Outcome::Return(Value::Integer(3)));
    assert_eq!(path.calls(), ["second", "first"]);
}

#[test]
fn indexed_assignment_captures_its_destination_once_before_the_rhs() {
    let (compilation, hir, mir) = checked(
        "usize index() { return 1; } i32 rhs() { return 7; } i32 f(i32[2] values) { values[index()] = rhs(); return values[1]; }",
    );
    let inputs = [(
        "values",
        Value::Fields(vec![Some(Value::Integer(0)), Some(Value::Integer(0))]),
    )];
    let results = [("index", Value::Integer(1)), ("rhs", Value::Integer(7))];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &results);
    assert_eq!(path.run(), Outcome::Return(Value::Integer(7)));
    assert_eq!(path.calls(), ["index", "rhs"]);
    let relevant = path
        .events
        .iter()
        .filter(|event| {
            event.starts_with("call:")
                || event.as_str() == "capture:values.1"
                || event.as_str() == "write:values.1"
        })
        .map(String::as_str)
        .collect::<Vec<_>>();
    assert_eq!(
        relevant,
        [
            "call:index",
            "capture:values.1",
            "call:rhs",
            "write:values.1"
        ]
    );
}

#[test]
fn scalar_and_compound_left_operands_are_captured_before_rhs_effects() {
    let (compilation, hir, mir) = checked(
        "i32 change(&mut i32 value) { *value = 99; return 4; } i32 sum() { i32 value = 3; return value + change(&mut value); } i32 compound() { i32 value = 3; value += change(&mut value); return value; }",
    );
    let results = [("change", Value::Integer(4))];
    let writes = [("change", 0, Value::Integer(99))];
    for function in ["sum", "compound"] {
        let mut path = Path::new(&compilation, &hir, &mir, function, &[], &results);
        path.writes = &writes;
        assert_eq!(path.run(), Outcome::Return(Value::Integer(7)));
        assert_eq!(path.calls(), ["change"]);
    }
}

#[test]
fn mutable_reference_callbacks_preserve_the_function_pointer_and_argument() {
    let (compilation, hir, mir) = checked(
        "type Callback = fn(&mut i32) -> i32; i32 update(&mut i32 value) { *value += 1; return *value; } i32 f(Callback callback) { i32 value = 3; return callback(&mut value); }",
    );
    let definition = hir
        .functions
        .iter()
        .find(|function| {
            compilation
                .symbols
                .get(hir.definitions[function.definition.0 as usize].name)
                == "update"
        })
        .unwrap()
        .definition;
    let inputs = [("callback", Value::Function(definition))];
    let results = [("update", Value::Integer(4))];
    let writes = [("update", 0, Value::Integer(4))];
    let mut path = Path::new(&compilation, &hir, &mir, "f", &inputs, &results);
    path.writes = &writes;
    assert_eq!(path.run(), Outcome::Return(Value::Integer(4)));
    assert_eq!(path.calls(), ["update"]);
}

#[test]
fn enum_payload_and_nullary_constructors_preserve_the_selected_variant() {
    let (compilation, hir, mir) = checked(
        "enum Choice { Empty, Value(i32) } Choice none() { return Choice::Empty; } Choice some() { return Choice::Value(7); }",
    );
    let mut none = Path::new(&compilation, &hir, &mir, "none", &[], &[]);
    assert_eq!(
        none.run(),
        Outcome::Return(Value::Variant(hir.enums[0].variants[0], Vec::new()))
    );
    let mut some = Path::new(&compilation, &hir, &mir, "some", &[], &[]);
    assert_eq!(
        some.run(),
        Outcome::Return(Value::Variant(
            hir.enums[0].variants[1],
            vec![Value::Integer(7)]
        ))
    );
}

#[test]
fn array_to_slice_conversion_preserves_the_referenced_storage() {
    let (compilation, hir, mir) =
        checked("i32 f() { i32[2] values = [2, 7]; &[i32] view = &values; return view[1]; }");
    assert!(
        mir.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| {
                matches!(
                    statement.kind,
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::ArrayToSlice(_),
                        ..
                    }
                )
            })
    );
    let mut path = Path::new(&compilation, &hir, &mir, "f", &[], &[]);
    assert_eq!(path.run(), Outcome::Return(Value::Integer(7)));
}

#[test]
fn arithmetic_and_bounds_traps_abort_without_promising_cleanup() {
    let (_, _, mir) = checked(
        "i32 increment(i32 value) { return value + 1; } i32 at(i32[1] values, usize index) { return values[index]; }",
    );
    let mut checked = 0;
    let mut bounds = 0;
    for body in &mir.functions {
        for block in &body.blocks {
            let trap = match block.terminator {
                mir::Terminator::Checked { trap, .. } => {
                    checked += 1;
                    trap
                }
                mir::Terminator::Bounds { trap, .. } => {
                    bounds += 1;
                    trap
                }
                _ => continue,
            };
            assert!(matches!(
                body.block(trap).terminator,
                mir::Terminator::Abort
            ));
        }
    }
    assert_eq!(checked, 1);
    assert_eq!(bounds, 1);
}

#[test]
fn for_in_has_explicit_length_and_checked_element_access() {
    let (_, _, mir) = checked("void f(i32[2] values) { for (auto value in values) {} }");
    assert!(
        mir.functions[0]
            .blocks
            .iter()
            .any(|block| { matches!(block.terminator, mir::Terminator::Bounds { .. }) })
    );
    assert!(
        mir.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| {
                matches!(
                    statement.kind,
                    mir::StatementKind::Assign {
                        value: mir::Rvalue::Length(_),
                        ..
                    }
                )
            })
    );
}

#[test]
fn continue_and_break_clean_iteration_storage_and_preserve_for_update() {
    let (compilation, hir, mir) = checked(
        "i32 f() { i32 result = 0; for (i32 index = 0; index < 3; index += 1) { i32 iteration = index; if (iteration == 0) { continue; } result += iteration; break; } return result; }",
    );
    let mut path = Path::new(&compilation, &hir, &mir, "f", &[], &[]);
    assert_eq!(path.run(), Outcome::Return(Value::Integer(1)));
    assert_eq!(
        path.events
            .iter()
            .filter(|event| event.as_str() == "write:iteration")
            .count(),
        2
    );
}

#[test]
fn verifier_rejects_invalid_targets_and_uninitialized_returns() {
    let (_, mut hir, mut mir) = checked("i32 f() { return 1; }");
    let body = &mut mir.functions[0];
    body.blocks[body.entry.0 as usize].terminator = mir::Terminator::Goto(mir::BlockId(u32::MAX));
    assert!(mir.validate(&mut hir).is_err());

    let (_, mut hir, mut mir) = checked("i32 f() { return 1; }");
    let body = &mut mir.functions[0];
    for block in &mut body.blocks {
        block.statements.retain(|statement| !matches!(
            &statement.kind,
            mir::StatementKind::Assign { destination, .. } if destination.local == body.return_local
        ));
    }
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn verifier_rejects_scope_mismatch_and_early_storage_death() {
    let (_, mut hir, mut mir) = checked("i32 f() { i32 value = 1; return value; }");
    let body = &mut mir.functions[0];
    let entry = &mut body.blocks[body.entry.0 as usize];
    entry.statements.insert(
        0,
        mir::Statement {
            kind: mir::StatementKind::ExitScope(mir::ScopeId(0)),
            span: entry.span,
        },
    );
    assert!(mir.validate(&mut hir).is_err());

    let (_, mut hir, mut mir) = checked("i32 f() { i32 value = 1; return value; }");
    let body = &mut mir.functions[0];
    let local = body
        .locals
        .iter()
        .position(|local| local.kind == mir::LocalKind::Source)
        .unwrap();
    let block = body.blocks.iter_mut().find(|block| block.statements.iter().any(|statement| {
        matches!(&statement.kind, mir::StatementKind::Assign { destination, .. } if destination.local.0 as usize == local)
    })).unwrap();
    let assignment = block.statements.iter().position(|statement| {
        matches!(&statement.kind, mir::StatementKind::Assign { destination, .. } if destination.local.0 as usize == local)
    }).unwrap();
    block.statements.insert(
        assignment,
        mir::Statement {
            kind: mir::StatementKind::StorageDead(mir::LocalId(local as u32)),
            span: block.span,
        },
    );
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn verifier_rejects_reading_a_call_result_on_its_failure_edge() {
    let (_, mut hir, mut mir) = checked("i32 value() { return 1; } i32 f() { return value(); }");
    let body = mir
        .functions
        .iter_mut()
        .find(|body| {
            body.blocks
                .iter()
                .any(|block| matches!(block.terminator, mir::Terminator::Call { .. }))
        })
        .unwrap();
    let (destination, panic) = body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            mir::Terminator::Call {
                destination, panic, ..
            } => Some((destination.clone(), *panic)),
            _ => None,
        })
        .unwrap();
    let block = &mut body.blocks[panic.0 as usize];
    block.statements.insert(
        0,
        mir::Statement {
            kind: mir::StatementKind::Assign {
                destination: mir::Place::local(body.return_local),
                value: mir::Rvalue::Use(mir::Operand::Copy(destination)),
            },
            span: block.span,
        },
    );
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn verifier_rejects_missing_bodies_and_removed_arithmetic_traps() {
    let (_, mut hir, mut mir) = checked("i32 f() { return 1; }");
    mir.functions.clear();
    assert!(mir.validate(&mut hir).is_err());

    // Even an unused owned parameter arrives initialized and must be cleaned.
    let (_, mut hir, mut mir) = checked("void discard<T>(T input) {}");
    let body = &mut mir.functions[0];
    body.blocks[body.entry.0 as usize]
        .statements
        .retain(|statement| !matches!(statement.kind, mir::StatementKind::Argument(_)));
    assert!(mir.validate(&mut hir).is_err());

    let (_, mut hir, mut mir) = checked("i32 f(i32 value) { return value + 1; }");
    let block = mir.functions[0]
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, mir::Terminator::Checked { .. }))
        .unwrap();
    let mir::Terminator::Checked {
        value,
        destination,
        normal,
        ..
    } = std::mem::replace(&mut block.terminator, mir::Terminator::Unreachable)
    else {
        unreachable!()
    };
    block.statements.push(mir::Statement {
        kind: mir::StatementKind::Assign { destination, value },
        span: block.span,
    });
    block.terminator = mir::Terminator::Goto(normal);
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn verifier_rejects_copying_an_exclusive_reference() {
    let (_, mut hir, mut mir) = checked("&mut i32 f(&mut i32 value) { return move value; }");
    let operand = mir.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.statements)
        .find_map(|statement| match &mut statement.kind {
            mir::StatementKind::Assign {
                value: mir::Rvalue::Use(operand @ mir::Operand::Move(_)),
                ..
            } => Some(operand),
            _ => None,
        })
        .unwrap();
    let mir::Operand::Move(place) = operand else {
        unreachable!()
    };
    *operand = mir::Operand::Copy(place.clone());
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn callable_operand_verification_preserves_universal_region_requirements() {
    use cavo_compiler::types::{Region, Ty};
    let (_, mut hir, mut mir) = checked(
        "&i32 identity(&i32 value) { return value; } i32 f(&i32 value) { return *identity(value); }",
    );
    let Ty::Reference { inner, .. } = *hir.types.get(hir.functions[0].result) else {
        panic!("reference-returning fixture");
    };
    let reference = hir.types.intern(Ty::Reference {
        region: Region::Static,
        mutable: false,
        inner,
    });
    let restricted = hir.types.intern(Ty::Function {
        parameters: vec![reference],
        result: reference,
    });
    let callee_type = mir
        .functions
        .iter_mut()
        .flat_map(|body| &mut body.blocks)
        .find_map(|block| match &mut block.terminator {
            mir::Terminator::Call {
                callee: mir::Operand::Function { ty, .. },
                ..
            } => Some(ty),
            _ => None,
        })
        .expect("direct call");
    *callee_type = restricted;
    assert!(mir.validate(&mut hir).is_err());
}

#[test]
fn verifier_rejects_removed_bounds_checks_and_checks_invalidated_before_use() {
    for remove_check in [true, false] {
        let (_, mut hir, mut mir) =
            checked("i32 at(i32[2] values, usize index) { return values[index]; }");
        let body = &mut mir.functions[0];
        let (checked_block, normal, index) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(id, block)| match block.terminator {
                mir::Terminator::Bounds { normal, index, .. } => Some((id, normal, index)),
                _ => None,
            })
            .unwrap();
        if remove_check {
            body.blocks[checked_block].terminator = mir::Terminator::Goto(normal);
        } else {
            let ty = body.local(index).ty;
            let block = &mut body.blocks[normal.0 as usize];
            block.statements.insert(
                0,
                mir::Statement {
                    kind: mir::StatementKind::Assign {
                        destination: mir::Place::local(index),
                        value: mir::Rvalue::Use(mir::Operand::Constant {
                            value: hir::Constant::Integer {
                                magnitude: 0,
                                negative: false,
                            },
                            ty,
                        }),
                    },
                    span: block.span,
                },
            );
        }
        assert!(mir.validate(&mut hir).is_err());
    }
}

#[test]
fn many_functions_and_repeated_calls_keep_per_function_limits_and_cleanup_growth_bounded() {
    const EMPTY_FUNCTIONS: usize = 512;
    const CALLS: usize = 256;
    let mut source = String::from("void touch() {}");
    for index in 0..EMPTY_FUNCTIONS {
        write!(source, "void empty_{index}() {{}}").unwrap();
    }
    source.push_str("void many() {");
    for _ in 0..CALLS {
        source.push_str("touch();");
    }
    source.push('}');

    let (compilation, hir, mir) = checked(&source);
    assert_eq!(mir.functions.len(), EMPTY_FUNCTIONS + 2);
    let body = mir
        .functions
        .iter()
        .find(|body| {
            compilation
                .symbols
                .get(hir.definitions[body.definition.0 as usize].name)
                == "many"
        })
        .unwrap();
    assert_eq!(
        body.blocks
            .iter()
            .filter(|block| { matches!(block.terminator, mir::Terminator::Call { .. }) })
            .count(),
        CALLS
    );
    // This is a generous structural regression bound, not a speed benchmark or
    // a requirement to preserve the current block layout.
    assert!(
        body.blocks.len() < 100 * CALLS,
        "{} blocks for {CALLS} calls",
        body.blocks.len()
    );
}
