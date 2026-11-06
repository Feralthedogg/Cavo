use cavo_compiler::{
    Compilation, hir, mir,
    syntax::ast::{BinaryOp, UnaryOp},
};
use std::collections::HashMap;

pub fn checked(source: &str) -> (Compilation, hir::Program, mir::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("patterns.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let result = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (mut hir, mir) = result.expect("checked MIR");
    mir.validate(&mut hir).unwrap();
    (compilation, hir, mir)
}

pub fn definition(compilation: &Compilation, hir: &hir::Program, name: &str) -> hir::DefId {
    let index = hir
        .definitions
        .iter()
        .position(|definition| compilation.symbols.get(definition.name) == name)
        .expect("fixture definition");
    hir::DefId(index as u32)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Unit,
    Integer(i128),
    Bool(bool),
    Char(char),
    Owned(&'static str),
    Fields(Vec<Option<Value>>),
    Variant(hir::DefId, Vec<Option<Value>>),
    Address(Slot),
    Function(hir::DefId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot {
    local: mir::LocalId,
    fields: Vec<usize>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Return(Value),
    Resume(mir::ExitKind),
    Abort,
}

/// A bounded path observer for these fixtures, not a Cavo runtime. A moved leaf
/// disappears immediately; conditional Drop visits only remaining initialized
/// leaves, exposing duplicate consumption or early guard commit in test traces.
pub struct Machine<'a> {
    compilation: &'a Compilation,
    hir: &'a hir::Program,
    body: &'a mir::Body,
    values: Vec<Option<Value>>,
    live: Vec<bool>,
    scopes: Vec<mir::ScopeId>,
    cursors: Vec<Option<usize>>,
    inputs: HashMap<&'a str, Value>,
    results: HashMap<&'a str, Value>,
    pub events: Vec<String>,
    pub failure: Option<(&'a str, mir::ExitKind)>,
}

impl<'a> Machine<'a> {
    pub fn new(
        compilation: &'a Compilation,
        hir: &'a hir::Program,
        mir: &'a mir::Program,
        function: &str,
        inputs: Vec<(&'a str, Value)>,
    ) -> Self {
        let definition = definition(compilation, hir, function);
        let body = mir
            .functions
            .iter()
            .find(|body| body.definition == definition)
            .expect("fixture MIR body");
        Self {
            compilation,
            hir,
            body,
            values: vec![None; body.locals.len()],
            live: vec![false; body.locals.len()],
            scopes: Vec::new(),
            cursors: vec![None; body.locals.len()],
            inputs: inputs.into_iter().collect(),
            results: HashMap::new(),
            events: Vec::new(),
            failure: None,
        }
    }

    pub fn stub(&mut self, function: &'a str, value: Value) {
        self.results.insert(function, value);
    }

    fn slot(&mut self, slot: &Slot) -> &mut Option<Value> {
        assert!(
            self.live[slot.local.0 as usize],
            "access to dead storage: {slot:?}"
        );
        let mut value = &mut self.values[slot.local.0 as usize];
        for &index in &slot.fields {
            let fields = match value.as_mut().expect("projected owner is initialized") {
                Value::Fields(fields) | Value::Variant(_, fields) => fields,
                other => panic!("field projection through {other:?}"),
            };
            value = fields.get_mut(index).expect("field index");
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
                mir::Projection::Deref => {
                    let Some(Value::Address(address)) = self.slot(&slot) else {
                        panic!("dereference needs an initialized address");
                    };
                    slot = address.clone();
                }
                mir::Projection::Downcast(expected) => {
                    assert!(
                        matches!(self.slot(&slot), Some(Value::Variant(actual, _)) if *actual == expected),
                        "downcast selected an inactive variant"
                    );
                }
                mir::Projection::Field(index) => slot.fields.push(index as usize),
                mir::Projection::Index(index) => {
                    let Some(Value::Integer(index)) = self.values[index.0 as usize] else {
                        panic!("index is initialized");
                    };
                    slot.fields.push(usize::try_from(index).unwrap());
                }
            }
        }
        slot
    }

    fn operand(&mut self, operand: &mir::Operand) -> Value {
        match operand {
            mir::Operand::Constant { value, .. } => constant(value),
            mir::Operand::Copy(place) => {
                let slot = self.resolve(place);
                self.slot(&slot)
                    .clone()
                    .expect("copy needs initialized value")
            }
            mir::Operand::Move(place) => {
                let slot = self.resolve(place);
                let value = self
                    .slot(&slot)
                    .take()
                    .expect("move needs initialized value");
                if let Value::Owned(name) = value {
                    self.events.push(format!("move-leaf:{name}"));
                }
                value
            }
            mir::Operand::Function { definition, .. } => Value::Function(*definition),
            mir::Operand::Unit => Value::Unit,
            other => panic!("operand outside fixture coverage: {other:?}"),
        }
    }

    fn rvalue(&mut self, value: &mir::Rvalue) -> Value {
        match value {
            mir::Rvalue::Use(value) => self.operand(value),
            mir::Rvalue::Borrow { place, .. } | mir::Rvalue::AddressOf(place) => {
                Value::Address(self.resolve(place))
            }
            mir::Rvalue::IsVariant { place, variant } => {
                let slot = self.resolve(place);
                Value::Bool(
                    matches!(self.slot(&slot), Some(Value::Variant(actual, _)) if *actual == *variant),
                )
            }
            mir::Rvalue::Variant { definition, fields } => Value::Variant(
                *definition,
                fields
                    .iter()
                    .map(|field| Some(self.operand(field)))
                    .collect(),
            ),
            mir::Rvalue::Record { fields, .. } => self.record(fields),
            mir::Rvalue::Array(values) => Value::Fields(
                values
                    .iter()
                    .map(|value| Some(self.operand(value)))
                    .collect(),
            ),
            mir::Rvalue::Binary { op, left, right } => {
                let left = self.operand(left);
                let right = self.operand(right);
                binary(*op, left, right)
            }
            mir::Rvalue::Unary { op, operand } => unary(*op, self.operand(operand)),
            mir::Rvalue::ArrayToSlice(value) => self.operand(value),
            other => panic!("rvalue outside fixture coverage: {other:?}"),
        }
    }

    fn record(&mut self, fields: &[(u32, mir::Operand)]) -> Value {
        let length = fields
            .iter()
            .map(|(field, _)| *field as usize + 1)
            .max()
            .unwrap_or(0);
        let mut values = vec![None; length];
        for (field, value) in fields {
            values[*field as usize] = Some(self.operand(value));
        }
        Value::Fields(values)
    }

    fn statement(&mut self, statement: &mir::StatementKind) {
        match statement {
            mir::StatementKind::EnterScope(scope) => self.scopes.push(*scope),
            mir::StatementKind::ExitScope(scope) => assert_eq!(self.scopes.pop(), Some(*scope)),
            mir::StatementKind::StorageLive(local) => {
                assert!(!self.live[local.0 as usize]);
                self.live[local.0 as usize] = true;
                self.values[local.0 as usize] = None;
                self.cursors[local.0 as usize] = None;
            }
            mir::StatementKind::StorageDead(local) => {
                assert!(self.live[local.0 as usize]);
                if let Some(value) = &self.values[local.0 as usize] {
                    assert!(!owns_token(value), "owned value bypassed Drop");
                }
                self.live[local.0 as usize] = false;
                self.values[local.0 as usize] = None;
            }
            mir::StatementKind::Argument(local) => {
                let name = self
                    .compilation
                    .symbols
                    .get(self.body.local(*local).name.expect("named parameter"));
                self.values[local.0 as usize] =
                    Some(self.inputs.get(name).expect("fixture argument").clone());
            }
            mir::StatementKind::IteratorStart { iterator, value } => {
                assert_eq!(
                    self.body.local(*iterator).kind,
                    mir::LocalKind::ArrayIterator
                );
                assert!(self.live[iterator.0 as usize]);
                let value = self.operand(value);
                assert!(matches!(value, Value::Fields(_)));
                self.values[iterator.0 as usize] = Some(value);
                self.cursors[iterator.0 as usize] = Some(0);
            }
            mir::StatementKind::Assign { destination, value } => {
                let slot = self.resolve(destination);
                let value = self.rvalue(value);
                *self.slot(&slot) = Some(value);
            }
        }
    }

    pub fn run(&mut self) -> Value {
        match self.run_outcome() {
            Outcome::Return(value) => value,
            other => panic!("unexpected fixture failure: {other:?}"),
        }
    }

    pub fn run_outcome(&mut self) -> Outcome {
        let body = self.body;
        let mut block = self.body.entry;
        for _ in 0..4096 {
            for statement in &body.block(block).statements {
                self.statement(&statement.kind);
            }
            if matches!(body.block(block).terminator, mir::Terminator::Return) {
                assert!(self.scopes.is_empty());
                return Outcome::Return(
                    self.values[self.body.return_local.0 as usize]
                        .take()
                        .expect("initialized return"),
                );
            }
            if let mir::Terminator::Resume(reason) = body.block(block).terminator {
                assert!(self.scopes.is_empty());
                assert!(self.live.iter().all(|live| !live));
                return Outcome::Resume(reason);
            }
            if matches!(body.block(block).terminator, mir::Terminator::Abort) {
                return Outcome::Abort;
            }
            block = self.next(&body.block(block).terminator);
        }
        panic!("MIR observer exceeded step budget");
    }

    fn next(&mut self, exit: &mir::Terminator) -> mir::BlockId {
        match exit {
            mir::Terminator::Goto(next) => *next,
            mir::Terminator::IteratorNext {
                iterator,
                destination,
                some,
                none,
            } => {
                if self.next_element(*iterator, destination) {
                    *some
                } else {
                    *none
                }
            }
            mir::Terminator::Switch { condition, yes, no } => {
                let Value::Bool(condition) = self.operand(condition) else {
                    panic!("boolean switch");
                };
                if condition { *yes } else { *no }
            }
            mir::Terminator::Checked {
                value,
                destination,
                normal,
                ..
            } => {
                let slot = self.resolve(destination);
                let value = self.rvalue(value);
                *self.slot(&slot) = Some(value);
                *normal
            }
            mir::Terminator::Call {
                callee,
                arguments,
                destination,
                normal,
                panic,
                cancel,
                ..
            } => match self.call(callee, arguments, destination) {
                Some(mir::ExitKind::Panic) => *panic,
                Some(mir::ExitKind::Cancel) => *cancel,
                None => *normal,
                Some(mir::ExitKind::Normal) => panic!("normal is not an abrupt call outcome"),
            },
            mir::Terminator::Drop { place, next, .. } => {
                let slot = self.resolve(place);
                if let Some(value) = self.slot(&slot).take() {
                    self.dropped(value);
                }
                *next
            }
            other => panic!("terminator outside fixture coverage: {other:?}"),
        }
    }

    fn call(
        &mut self,
        callee: &mir::Operand,
        arguments: &[mir::Operand],
        destination: &mir::Place,
    ) -> Option<mir::ExitKind> {
        let Value::Function(definition) = self.operand(callee) else {
            panic!("fixture function");
        };
        for argument in arguments {
            self.operand(argument);
        }
        let name = self
            .compilation
            .symbols
            .get(self.hir.definitions[definition.0 as usize].name);
        self.events.push(format!("call:{name}"));
        if let Some((_, reason)) = self.failure.filter(|(target, _)| *target == name) {
            return Some(reason);
        }
        let value = self.results.get(name).cloned().unwrap_or(Value::Unit);
        let slot = self.resolve(destination);
        *self.slot(&slot) = Some(value);
        None
    }

    fn next_element(&mut self, iterator: mir::LocalId, destination: &mir::Place) -> bool {
        let slot = iterator.0 as usize;
        assert!(self.live[slot]);
        let cursor = self.cursors[slot].expect("initialized iterator cursor");
        let Some(Value::Fields(elements)) = &mut self.values[slot] else {
            panic!("iterator owns an array");
        };
        if cursor == elements.len() {
            return false;
        }
        let value = elements[cursor]
            .take()
            .expect("unconsumed iterator element");
        self.cursors[slot] = Some(cursor + 1);
        if let Value::Owned(name) = value {
            self.events.push(format!("next-leaf:{name}"));
        }
        let destination = self.resolve(destination);
        assert!(
            self.slot(&destination).is_none(),
            "IteratorNext cannot overwrite a live element"
        );
        *self.slot(&destination) = Some(value);
        true
    }

    fn dropped(&mut self, value: Value) {
        match value {
            Value::Owned(name) => self.events.push(format!("drop:{name}")),
            Value::Fields(fields) | Value::Variant(_, fields) => {
                for value in fields.into_iter().flatten() {
                    self.dropped(value);
                }
            }
            _ => {}
        }
    }
}

fn owns_token(value: &Value) -> bool {
    match value {
        Value::Owned(_) => true,
        Value::Fields(fields) | Value::Variant(_, fields) => {
            fields.iter().flatten().any(owns_token)
        }
        _ => false,
    }
}

fn constant(value: &hir::Constant) -> Value {
    match value {
        hir::Constant::Integer {
            magnitude,
            negative,
        } => {
            let value = i128::try_from(*magnitude).unwrap();
            Value::Integer(if *negative { -value } else { value })
        }
        hir::Constant::Bool(value) => Value::Bool(*value),
        hir::Constant::Char(value) => Value::Char(*value),
        other => panic!("constant outside fixture coverage: {other:?}"),
    }
}

fn binary(op: BinaryOp, left: Value, right: Value) -> Value {
    match (op, left, right) {
        (BinaryOp::Equal, left, right) => Value::Bool(left == right),
        (BinaryOp::NotEqual, left, right) => Value::Bool(left != right),
        (BinaryOp::Add, Value::Integer(left), Value::Integer(right)) => {
            Value::Integer(left + right)
        }
        (BinaryOp::Subtract, Value::Integer(left), Value::Integer(right)) => {
            Value::Integer(left - right)
        }
        (BinaryOp::Less, Value::Integer(left), Value::Integer(right)) => Value::Bool(left < right),
        (BinaryOp::Greater, Value::Integer(left), Value::Integer(right)) => {
            Value::Bool(left > right)
        }
        values => panic!("binary operation outside fixture coverage: {values:?}"),
    }
}

fn unary(op: UnaryOp, value: Value) -> Value {
    match (op, value) {
        (UnaryOp::Not, Value::Bool(value)) => Value::Bool(!value),
        (UnaryOp::Negate, Value::Integer(value)) => Value::Integer(-value),
        (UnaryOp::Positive, value) => value,
        value => panic!("unary operation outside fixture coverage: {value:?}"),
    }
}
