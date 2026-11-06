use cavo_compiler::{Compilation, hir, mir, types::Ty};
use mir::drop::{self, ArrayLength, FlagValue, GlueKind, Instruction, Terminator};
use std::collections::HashMap;

fn checked(source: &str) -> (Compilation, hir::Program, mir::Program, drop::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("drop-flags.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let (mut hir, mir) = compilation
        .check_mir()
        .unwrap_or_else(|| panic!("{:#?}", compilation.diagnostics));
    let drop = drop::elaborate(&mir, &mut hir).unwrap();
    drop.validate(&mir, &mut hir).unwrap();
    (compilation, hir, mir, drop)
}

struct Trace<'a> {
    hir: &'a hir::Program,
    body: &'a mir::Body,
    flags: &'a drop::Body,
    glue: &'a [drop::Glue],
    values: Vec<bool>,
    tags: HashMap<mir::Place, hir::DefId>,
    booleans: HashMap<mir::Place, bool>,
    cursors: HashMap<mir::LocalId, u64>,
    input_variant: Option<hir::DefId>,
    events: Vec<String>,
}
impl<'a> Trace<'a> {
    fn new(
        compilation: &Compilation,
        hir: &'a hir::Program,
        mir: &'a mir::Program,
        drop: &'a drop::Program,
    ) -> Self {
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
        let flags = drop
            .functions
            .iter()
            .find(|flags| flags.definition == body.definition)
            .unwrap();
        Self {
            hir,
            body,
            flags,
            glue: &drop.glue,
            values: vec![false; flags.flags.len()],
            tags: HashMap::new(),
            booleans: HashMap::new(),
            cursors: HashMap::new(),
            input_variant: None,
            events: Vec::new(),
        }
    }
    fn run(&mut self) {
        let mut current = self.flags.entry;
        for _ in 0..4096 {
            let block = &self.flags.blocks[current.0 as usize];
            for instruction in &block.instructions {
                self.instruction(instruction);
            }
            current = match &block.terminator {
                Terminator::Goto(next) => *next,
                Terminator::TestFlag {
                    flag,
                    initialized,
                    clear,
                } => {
                    if self.values[flag.0 as usize] {
                        *initialized
                    } else {
                        *clear
                    }
                }
                Terminator::TestVariant {
                    place,
                    variant,
                    matches,
                    otherwise,
                } => {
                    if self.tags.get(place).expect("initialized discriminant") == variant {
                        *matches
                    } else {
                        *otherwise
                    }
                }
                Terminator::InvokeGlue {
                    place, glue, next, ..
                } => {
                    self.invoke(place, *glue);
                    *next
                }
                Terminator::Core { source, successors } => {
                    let core = &self.body.blocks[source.0 as usize].terminator;
                    if matches!(core, mir::Terminator::Return | mir::Terminator::Resume(_)) {
                        assert!(self.values.iter().all(|flag| !flag));
                        return;
                    }
                    successors[self.successor(core)]
                }
            };
        }
        panic!("flag path exceeded its work limit");
    }
    fn instruction(&mut self, instruction: &Instruction) {
        match instruction {
            Instruction::SetFlag { flag, value } => {
                self.values[flag.0 as usize] = *value == FlagValue::Set
            }
            Instruction::RecomputeFlag { flag, all } => {
                self.values[flag.0 as usize] = all.iter().all(|input| self.values[input.0 as usize])
            }
            Instruction::CoreStatement { source, statement } => self.statement(
                &self.body.blocks[source.0 as usize].statements[*statement as usize].kind,
            ),
        }
    }
    fn statement(&mut self, statement: &mir::StatementKind) {
        match statement {
            mir::StatementKind::Argument(local) => {
                if let Some(variant) = self.input_variant {
                    self.tags.insert(mir::Place::local(*local), variant);
                }
            }
            mir::StatementKind::Assign { destination, value } => self.assign(destination, value),
            mir::StatementKind::IteratorStart { iterator, .. } => {
                self.cursors.insert(*iterator, 0);
            }
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                self.tags.retain(|place, _| place.local != *local);
                self.booleans.retain(|place, _| place.local != *local);
            }
            _ => {}
        }
    }
    fn assign(&mut self, destination: &mir::Place, value: &mir::Rvalue) {
        match value {
            mir::Rvalue::Variant { definition, .. } => {
                self.tags.insert(destination.clone(), *definition);
            }
            mir::Rvalue::Use(mir::Operand::Move(source) | mir::Operand::Copy(source)) => {
                if let Some(&tag) = self.tags.get(source) {
                    self.tags.insert(destination.clone(), tag);
                }
                if let Some(&value) = self.booleans.get(source) {
                    self.booleans.insert(destination.clone(), value);
                }
            }
            mir::Rvalue::Use(mir::Operand::Constant {
                value: hir::Constant::Bool(value),
                ..
            }) => {
                self.booleans.insert(destination.clone(), *value);
            }
            mir::Rvalue::IsVariant { place, variant } => {
                self.booleans
                    .insert(destination.clone(), self.tags.get(place) == Some(variant));
            }
            _ => {}
        }
    }
    fn successor(&mut self, terminator: &mir::Terminator) -> usize {
        match terminator {
            mir::Terminator::Goto(_)
            | mir::Terminator::Checked { .. }
            | mir::Terminator::Bounds { .. } => 0,
            mir::Terminator::Switch { condition, .. } => usize::from(!self.boolean(condition)),
            mir::Terminator::IteratorNext { iterator, .. } => {
                let Ty::Array { length, .. } = self.hir.types.get(self.body.local(*iterator).ty)
                else {
                    panic!("concrete iterator count");
                };
                let cursor = self
                    .cursors
                    .get_mut(iterator)
                    .expect("initialized iterator");
                if *cursor == *length {
                    1
                } else {
                    *cursor += 1;
                    0
                }
            }
            other => panic!("unexpected test terminator: {other:?}"),
        }
    }
    fn boolean(&self, operand: &mir::Operand) -> bool {
        match operand {
            mir::Operand::Constant {
                value: hir::Constant::Bool(value),
                ..
            } => *value,
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                *self.booleans.get(place).expect("initialized bool")
            }
            _ => panic!("fixture bool"),
        }
    }
    fn invoke(&mut self, place: &mir::Place, glue: drop::GlueId) {
        let flag = self
            .flags
            .flags
            .iter()
            .position(|flag| flag.place == *place && flag.glue == glue)
            .unwrap();
        assert!(!self.values[flag], "clear before glue");
        match &self.glue[glue.0 as usize].kind {
            GlueKind::Destructor { .. } => self.events.push("user".into()),
            GlueKind::Parameter { .. } => self.events.push("value".into()),
            GlueKind::ArrayTail {
                count: ArrayLength::Concrete(count),
                ..
            } => {
                let consumed = self.cursors.get(&place.local).expect("iterator cursor");
                self.events.push(format!("tail:{}", count - consumed));
            }
            other => panic!("unexpected fixture glue {other:?}"),
        }
    }
}

#[test]
fn user_destructor_activation_requires_all_fields_and_field_overwrite_does_not_call_it() {
    for (body, count) in [
        ("Pair value; value.left = 1;", 0),
        ("Pair value; value.left = 1; value.right = 2;", 1),
        (
            "Pair value = Pair { left: 1, right: 2 }; value.left = 3;",
            1,
        ),
    ] {
        let source = format!(
            "@lang(drop) trait Drop {{ void drop(&mut Self self); }} struct Pair {{ i32 left; i32 right; }} impl Drop for Pair {{ void drop(&mut Self self) {{}} }} void f() {{ {body} }}"
        );
        let (compilation, hir, mir, drop) = checked(&source);
        let mut trace = Trace::new(&compilation, &hir, &mir, &drop);
        trace.run();
        assert_eq!(trace.events, vec!["user"; count]);
    }
}

#[test]
fn inactive_enum_payloads_are_never_read_or_dropped() {
    let (compilation, hir, mir, drop) =
        checked("enum Choice<T> { Empty, Pair(T, T) } void f<T>(Choice<T> choice) {}");
    for (variant, expected) in [(hir.enums[0].variants[0], 0), (hir.enums[0].variants[1], 2)] {
        let mut trace = Trace::new(&compilation, &hir, &mir, &drop);
        trace.input_variant = Some(variant);
        trace.run();
        assert_eq!(trace.events, vec!["value"; expected]);
    }
    assert!(
        drop.functions
            .iter()
            .flat_map(|body| &body.blocks)
            .any(|block| matches!(block.terminator, Terminator::TestVariant { .. }))
    );
}

#[test]
fn moving_selected_enum_payload_fields_drops_only_the_unreturned_binding() {
    let (compilation, hir, mir, drop) = checked(
        "enum Choice<T> { A(T, T), B(T, T) } T f<T>(Choice<T> choice) { return match (move choice) { Choice::A(first, second) => move first, Choice::B(first, second) => move first }; }",
    );
    for variant in &hir.enums[0].variants {
        let mut trace = Trace::new(&compilation, &hir, &mir, &drop);
        trace.input_variant = Some(*variant);
        trace.run();
        assert_eq!(trace.events, ["value"]);
    }
}

#[test]
fn overwriting_a_copy_array_element_preserves_the_user_owners_initialization() {
    let (compilation, hir, mir, drop) = checked(
        "@lang(drop) trait Drop { void drop(&mut Self self); } struct Frame { i32[2] values; i32 tail; } impl Drop for Frame { void drop(&mut Self self) {} } void f() { Frame value = Frame { values: [1, 2], tail: 3 }; value.values[0] = 4; }",
    );
    let mut trace = Trace::new(&compilation, &hir, &mir, &drop);
    trace.run();
    assert_eq!(trace.events, ["user"]);
}

#[test]
fn owned_iterator_drop_uses_its_remaining_tail_after_break_or_exhaustion() {
    for (body, expected) in [
        ("break;", vec!["value", "tail:2"]),
        ("continue;", vec!["value", "value", "value", "tail:0"]),
    ] {
        let source =
            format!("void f<T>(T[3] values) {{ for (auto item in move values) {{ {body} }} }}");
        let (compilation, hir, mir, drop) = checked(&source);
        let mut trace = Trace::new(&compilation, &hir, &mir, &drop);
        trace.run();
        assert_eq!(trace.events, expected);
    }
}

#[test]
fn changing_owner_recomputation_or_variant_guards_invalidates_the_artifact() {
    let (compilation, mut hir, mir, drop) = checked(
        "@lang(drop) trait Drop { void drop(&mut Self self); } struct Pair { i32 left; i32 right; } impl Drop for Pair { void drop(&mut Self self) {} } void f() { Pair value; value.left = 1; value.right = 2; }",
    );
    let mut changed = drop.clone();
    let body = changed
        .functions
        .iter_mut()
        .find(|body| {
            compilation
                .symbols
                .get(hir.definitions[body.definition].name)
                == "f"
        })
        .unwrap();
    let instruction = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find_map(|instruction| match instruction {
            Instruction::RecomputeFlag { all, .. } => Some(all),
            _ => None,
        })
        .unwrap();
    instruction.clear();
    assert!(changed.validate(&mir, &mut hir).is_err());
}
