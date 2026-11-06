use cavo_compiler::{Compilation, hir, mir, syntax::ast::BinaryOp};

fn checked(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("iteration.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let result = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (mut hir, mir) = result.unwrap();
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Integer(i128),
    Bool(bool),
    Array(Vec<Value>),
    Address(Slot),
    Unit,
}

#[derive(Clone, Debug, PartialEq)]
struct Slot {
    local: usize,
    elements: Vec<usize>,
}

enum Step {
    Next(mir::BlockId),
    Return(Value),
}

/// A bounded scalar/array path observer. It checks actual iteration results and
/// live-storage transitions, without implementing a runtime or native backend.
struct Machine<'a> {
    body: &'a mir::Body,
    values: Vec<Option<Value>>,
    live: Vec<bool>,
    scopes: Vec<mir::ScopeId>,
    calls: usize,
}

impl<'a> Machine<'a> {
    fn new(body: &'a mir::Body) -> Self {
        Self {
            body,
            values: vec![None; body.locals.len()],
            live: vec![false; body.locals.len()],
            scopes: Vec::new(),
            calls: 0,
        }
    }

    fn resolve(&self, place: &mir::Place) -> Slot {
        let mut slot = Slot {
            local: place.local.0 as usize,
            elements: Vec::new(),
        };
        for projection in &place.projection {
            match *projection {
                mir::Projection::Downcast(_) => {
                    panic!("variant projection outside array observer domain")
                }
                mir::Projection::Deref => {
                    let Value::Address(address) = self.read(&slot) else {
                        panic!("not an address");
                    };
                    slot = address.clone();
                }
                mir::Projection::Index(index) => {
                    let Some(Value::Integer(index)) = &self.values[index.0 as usize] else {
                        panic!("uninitialized index");
                    };
                    slot.elements.push(usize::try_from(*index).unwrap());
                }
                mir::Projection::Field(index) => slot.elements.push(index as usize),
            }
        }
        slot
    }

    fn read(&self, slot: &Slot) -> &Value {
        assert!(self.live[slot.local], "read from dead storage");
        let mut value = self.values[slot.local].as_ref().expect("initialized value");
        for &index in &slot.elements {
            let Value::Array(values) = value else {
                panic!("not an aggregate");
            };
            value = &values[index];
        }
        value
    }

    fn write(&mut self, place: &mir::Place, value: Value) {
        let slot = self.resolve(place);
        assert!(self.live[slot.local], "write to dead storage");
        if slot.elements.is_empty() {
            self.values[slot.local] = Some(value);
            return;
        }
        let mut destination = self.values[slot.local].as_mut().unwrap();
        for index in slot.elements {
            let Value::Array(values) = destination else {
                panic!("not an aggregate");
            };
            destination = &mut values[index];
        }
        *destination = value;
    }

    fn operand(&mut self, operand: &mir::Operand) -> Value {
        match operand {
            mir::Operand::Constant {
                value:
                    hir::Constant::Integer {
                        magnitude,
                        negative,
                    },
                ..
            } => {
                let value = i128::try_from(*magnitude).unwrap();
                Value::Integer(if *negative { -value } else { value })
            }
            mir::Operand::Constant {
                value: hir::Constant::Bool(value),
                ..
            } => Value::Bool(*value),
            mir::Operand::Copy(place) => self.read(&self.resolve(place)).clone(),
            mir::Operand::Move(place) => {
                assert!(
                    place.projection.is_empty(),
                    "observer only moves whole locals"
                );
                self.values[place.local.0 as usize].take().unwrap()
            }
            mir::Operand::Unit => Value::Unit,
            other => panic!("operand outside observer: {other:?}"),
        }
    }

    fn value(&mut self, value: &mir::Rvalue) -> Value {
        match value {
            mir::Rvalue::Use(value) | mir::Rvalue::ArrayToSlice(value) => self.operand(value),
            mir::Rvalue::Array(values) => {
                Value::Array(values.iter().map(|value| self.operand(value)).collect())
            }
            mir::Rvalue::Repeat { value, count } => {
                Value::Array(vec![self.operand(value); *count as usize])
            }
            mir::Rvalue::AddressOf(place) | mir::Rvalue::Borrow { place, .. } => {
                Value::Address(self.resolve(place))
            }
            mir::Rvalue::Length(place) => {
                let Value::Array(values) = self.read(&self.resolve(place)) else {
                    panic!("length of non-array");
                };
                Value::Integer(values.len() as i128)
            }
            mir::Rvalue::Binary { op, left, right } => {
                let left = self.operand(left);
                let right = self.operand(right);
                binary(*op, left, right)
            }
            other => panic!("rvalue outside observer: {other:?}"),
        }
    }

    fn statement(&mut self, statement: &mir::StatementKind) {
        match statement {
            mir::StatementKind::EnterScope(scope) => self.scopes.push(*scope),
            mir::StatementKind::ExitScope(scope) => assert_eq!(self.scopes.pop(), Some(*scope)),
            mir::StatementKind::StorageLive(local) => {
                let index = local.0 as usize;
                assert!(!self.live[index]);
                self.live[index] = true;
                self.values[index] = None;
            }
            mir::StatementKind::StorageDead(local) => {
                let index = local.0 as usize;
                assert!(self.live[index]);
                self.live[index] = false;
                self.values[index] = None;
            }
            mir::StatementKind::Assign { destination, value } => {
                let value = self.value(value);
                self.write(destination, value);
            }
            other => panic!("statement outside observer: {other:?}"),
        }
    }

    fn terminator(&mut self, terminator: &mir::Terminator) -> Step {
        let next = match terminator {
            mir::Terminator::Goto(next) => *next,
            mir::Terminator::Switch { condition, yes, no } => {
                let Value::Bool(condition) = self.operand(condition) else {
                    panic!("non-bool condition");
                };
                if condition { *yes } else { *no }
            }
            mir::Terminator::Checked {
                value,
                destination,
                normal,
                ..
            } => {
                let value = self.value(value);
                self.write(destination, value);
                *normal
            }
            mir::Terminator::Bounds {
                base,
                index,
                normal,
                trap,
            } => self.bounds(base, *index, *normal, *trap),
            mir::Terminator::Call {
                destination,
                normal,
                ..
            } => {
                self.array_factory(destination);
                *normal
            }
            mir::Terminator::Return => {
                return Step::Return(
                    self.values[self.body.return_local.0 as usize]
                        .take()
                        .unwrap(),
                );
            }
            other => panic!("terminator outside observer: {other:?}"),
        };
        Step::Next(next)
    }

    fn bounds(
        &self,
        base: &mir::Place,
        index: mir::LocalId,
        normal: mir::BlockId,
        trap: mir::BlockId,
    ) -> mir::BlockId {
        let Value::Array(values) = self.read(&self.resolve(base)) else {
            panic!("bounds on non-array");
        };
        let Some(Value::Integer(index)) = &self.values[index.0 as usize] else {
            panic!("invalid index");
        };
        if *index >= 0 && *index < values.len() as i128 {
            normal
        } else {
            trap
        }
    }

    fn array_factory(&mut self, destination: &mir::Place) {
        self.calls += 1;
        self.write(
            destination,
            Value::Array(vec![
                Value::Integer(1),
                Value::Integer(2),
                Value::Integer(3),
            ]),
        );
    }

    fn run(&mut self) -> Value {
        let mut block = self.body.entry;
        for _ in 0..4096 {
            let block_data = &self.body.blocks[block.0 as usize];
            for statement in &block_data.statements {
                self.statement(&statement.kind);
            }
            match self.terminator(&block_data.terminator) {
                Step::Next(next) => block = next,
                Step::Return(value) => {
                    assert!(self.scopes.is_empty());
                    assert!(
                        self.live.iter().enumerate().all(
                            |(index, live)| !live || index == self.body.return_local.0 as usize
                        )
                    );
                    return value;
                }
            }
        }
        panic!("iteration did not terminate within observer budget");
    }
}

fn binary(op: BinaryOp, left: Value, right: Value) -> Value {
    match (op, left, right) {
        (BinaryOp::Add, Value::Integer(left), Value::Integer(right)) => {
            Value::Integer(left + right)
        }
        (BinaryOp::Less, Value::Integer(left), Value::Integer(right)) => Value::Bool(left < right),
        (BinaryOp::Equal, left, right) => Value::Bool(left == right),
        (BinaryOp::NotEqual, left, right) => Value::Bool(left != right),
        other => panic!("binary operation outside observer: {other:?}"),
    }
}

fn observes(source: &str, expected: i128, expected_calls: usize) {
    let (compilation, hir, mir) = checked(source);
    let body = mir
        .functions
        .iter()
        .find(|body| {
            compilation
                .symbols
                .get(hir.definitions[body.definition].name)
                == "f"
        })
        .unwrap();
    let mut machine = Machine::new(body);
    assert_eq!(machine.run(), Value::Integer(expected));
    assert_eq!(machine.calls, expected_calls);
}

#[test]
fn array_iteration_preserves_order_and_evaluates_the_iterable_once() {
    observes(
        "i32[3] values() { return [1, 2, 3]; } i32 f() { i32 sum = 0; for (auto item in values()) { sum += item; } return sum; }",
        6,
        1,
    );
}

#[test]
fn empty_iterables_skip_the_body() {
    observes(
        "i32 f() { i32[0] values = []; i32 count = 0; for (auto item in values) { count += 1; } return count; }",
        0,
        0,
    );
}

#[test]
fn continue_advances_and_break_leaves_iteration_storage() {
    observes(
        "i32 f() { i32[4] values = [1, 2, 3, 4]; i32 sum = 0; for (auto item in values) { if (item == 1) { continue; } sum += item; if (item == 3) { break; } } return sum; }",
        5,
        0,
    );
}

#[test]
fn array_values_snapshot_while_shared_slices_keep_the_source_storage() {
    observes(
        "i32 f() { i32[3] values = [1, 2, 3]; i32 sum = 0; for (auto item in values) { values[2] = 9; sum += item; } return sum; }",
        6,
        0,
    );
    observes(
        "i32 f() { i32[3] values = [1, 2, 3]; &[i32] view = &values; i32 sum = 0; for (auto item in view) { sum += item; } return sum; }",
        6,
        0,
    );
}

#[test]
fn returning_from_iteration_keeps_the_result_and_cleans_the_loop() {
    observes(
        "i32 f() { i32[2] values = [4, 5]; for (auto item in values) { return item; } return 0; }",
        4,
        0,
    );
}
