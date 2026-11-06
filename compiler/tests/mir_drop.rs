use cavo_compiler::{Compilation, hir, mir};
use mir::drop::{self, FlagValue, GlueKind, Instruction, Terminator};
use std::fmt::Write;

fn checked(source: &str) -> (Compilation, hir::Program, mir::Program, drop::Program) {
    let mut compilation = Compilation::default();
    let file = compilation.sources.add("drop.cavo", source.into()).unwrap();
    compilation.parse(file);
    let checked = compilation.check_mir();
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    let (mut hir, core) = checked.expect("checked MIR");
    let drop = drop::elaborate(&core, &mut hir).unwrap();
    drop.validate(&core, &mut hir).unwrap();
    (compilation, hir, core, drop)
}

#[derive(Debug, PartialEq, Eq)]
enum End {
    Return,
    Resume(mir::ExitKind),
}

/// Executes the generated flag operations and branches. Core value operations
/// are retained by the artifact; calls are selected outcomes, not native code.
struct Trace<'a> {
    compilation: &'a Compilation,
    hir: &'a hir::Program,
    core: &'a mir::Body,
    drop: &'a drop::Body,
    flags: Vec<bool>,
    failure: Option<(&'a str, mir::ExitKind)>,
    dropped: Vec<String>,
    variants: std::collections::HashMap<mir::Place, hir::DefId>,
}

impl<'a> Trace<'a> {
    fn new(
        compilation: &'a Compilation,
        hir: &'a hir::Program,
        core: &'a mir::Program,
        drop: &'a drop::Program,
        name: &str,
    ) -> Self {
        let core = core
            .functions
            .iter()
            .find(|body| {
                compilation
                    .symbols
                    .get(hir.definitions[body.definition.0 as usize].name)
                    == name
            })
            .expect("named MIR body");
        let drop = drop
            .functions
            .iter()
            .find(|body| body.definition == core.definition)
            .unwrap();
        Self {
            compilation,
            hir,
            core,
            drop,
            flags: vec![false; drop.flags.len()],
            failure: None,
            dropped: Vec::new(),
            variants: std::collections::HashMap::new(),
        }
    }

    fn run(&mut self) -> End {
        let mut current = self.drop.entry;
        for _ in 0..4096 {
            let block = &self.drop.blocks[current.0 as usize];
            self.instructions(&block.instructions);
            match &block.terminator {
                Terminator::Goto(next) => current = *next,
                Terminator::TestFlag {
                    flag,
                    initialized,
                    clear,
                } => {
                    current = if self.flags[flag.0 as usize] {
                        *initialized
                    } else {
                        *clear
                    };
                }
                Terminator::InvokeGlue { place, next, .. } => {
                    self.invoke(place);
                    current = *next;
                }
                Terminator::TestVariant {
                    place,
                    variant,
                    matches,
                    otherwise,
                } => {
                    let actual = self
                        .variants
                        .get(place)
                        .expect("trace requires an initialized discriminant");
                    current = if actual == variant {
                        *matches
                    } else {
                        *otherwise
                    };
                }
                Terminator::Core { source, successors } => {
                    let core = &self.core.blocks[source.0 as usize].terminator;
                    match core {
                        mir::Terminator::Return => return self.finish(End::Return),
                        mir::Terminator::Resume(reason) => {
                            return self.finish(End::Resume(*reason));
                        }
                        _ => current = successors[self.successor(core)],
                    }
                }
            }
        }
        panic!("drop trace exceeded its step limit");
    }

    fn instructions(&mut self, instructions: &[Instruction]) {
        for instruction in instructions {
            match instruction {
                Instruction::SetFlag { flag, value } => {
                    self.flags[flag.0 as usize] = *value == FlagValue::Set
                }
                Instruction::RecomputeFlag { flag, all } => {
                    self.flags[flag.0 as usize] =
                        all.iter().all(|input| self.flags[input.0 as usize]);
                }
                Instruction::CoreStatement { source, statement } => {
                    let statement =
                        &self.core.blocks[source.0 as usize].statements[*statement as usize];
                    self.observe_tag(&statement.kind);
                }
            }
        }
    }

    fn observe_tag(&mut self, statement: &mir::StatementKind) {
        if let mir::StatementKind::Assign { destination, value } = statement {
            let variant = match value {
                mir::Rvalue::Variant { definition, .. } => Some(*definition),
                mir::Rvalue::Use(mir::Operand::Copy(source) | mir::Operand::Move(source)) => {
                    self.variants.get(source).copied()
                }
                _ => None,
            };
            if let Some(variant) = variant {
                self.variants.insert(destination.clone(), variant);
            }
        }
    }

    fn successor(&self, core: &mir::Terminator) -> usize {
        match core {
            mir::Terminator::Goto(_)
            | mir::Terminator::Checked { .. }
            | mir::Terminator::Bounds { .. } => 0,
            mir::Terminator::Call {
                callee: mir::Operand::Function { definition, .. },
                ..
            } => {
                let name = self
                    .compilation
                    .symbols
                    .get(self.hir.definitions[definition.0 as usize].name);
                match self.failure.filter(|(target, _)| *target == name) {
                    Some((_, mir::ExitKind::Panic)) => 1,
                    Some((_, mir::ExitKind::Cancel)) => 2,
                    _ => 0,
                }
            }
            other => panic!("unexpected core operation in flag trace: {other:?}"),
        }
    }

    fn invoke(&mut self, place: &mir::Place) {
        let flag = self
            .drop
            .flags
            .iter()
            .position(|flag| flag.place == *place)
            .expect("owned drop path");
        assert!(!self.flags[flag], "flag must clear before invoking glue");
        let local = &self.core.locals[place.local.0 as usize];
        let mut name = local.name.map_or_else(
            || format!("_{}", place.local.0),
            |name| self.compilation.symbols.get(name).to_owned(),
        );
        for field in &place.projection {
            let mir::Projection::Field(field) = field else {
                panic!("non-field owned path");
            };
            write!(name, ".{field}").unwrap();
        }
        self.dropped.push(name);
    }

    fn finish(&self, end: End) -> End {
        assert!(
            self.flags.iter().all(|flag| !flag),
            "ownership flags remain at terminal exit"
        );
        end
    }
}

#[test]
fn partial_moves_transfer_the_return_and_drop_only_the_remaining_owner() {
    let (compilation, hir, core, drop) = checked(
        "struct Pair<T> { T left; T right; } T f<T>(Pair<T> pair) { T first = move pair.left; return move pair.right; }",
    );
    let mut trace = Trace::new(&compilation, &hir, &core, &drop, "f");
    assert_eq!(trace.run(), End::Return);
    assert_eq!(trace.dropped, ["first"]);
}

#[test]
fn generated_flags_preserve_reverse_local_and_declaration_field_cleanup() {
    let (compilation, hir, core, drop) =
        checked("struct Pair<T> { T left; T right; } void f<T>(T a, Pair<T> pair, T b) {}");
    let mut trace = Trace::new(&compilation, &hir, &core, &drop, "f");
    assert_eq!(trace.run(), End::Return);
    assert_eq!(trace.dropped, ["b", "pair.0", "pair.1", "a"]);
}

#[test]
fn call_result_flags_are_set_only_after_normal_return() {
    let (compilation, hir, core, drop) = checked(
        "T make<T>(T input) { return move input; } void f<T>(T old, T replacement) { old = make(move replacement); }",
    );
    for reason in [
        mir::ExitKind::Normal,
        mir::ExitKind::Panic,
        mir::ExitKind::Cancel,
    ] {
        let mut trace = Trace::new(&compilation, &hir, &core, &drop, "f");
        trace.failure = (reason != mir::ExitKind::Normal).then_some(("make", reason));
        let expected = if reason == mir::ExitKind::Normal {
            End::Return
        } else {
            End::Resume(reason)
        };
        assert_eq!(trace.run(), expected);
        assert_eq!(
            trace.dropped,
            if reason == mir::ExitKind::Normal {
                vec!["old", "old"]
            } else {
                vec!["old"]
            }
        );
    }
}

#[test]
fn a_later_argument_failure_cleans_the_completed_result_temporary() {
    let (compilation, hir, core, drop) = checked(
        "T first<T>(T value) { return move value; } i32 second() { return 1; } void take<T>(T value, i32 number) {} void f<T>(T value) { take(first(move value), second()); }",
    );
    for reason in [mir::ExitKind::Panic, mir::ExitKind::Cancel] {
        let mut trace = Trace::new(&compilation, &hir, &core, &drop, "f");
        trace.failure = Some(("second", reason));
        assert_eq!(trace.run(), End::Resume(reason));
        assert_eq!(trace.dropped.len(), 1);
        assert!(trace.dropped[0].starts_with('_'));
    }
}

#[test]
fn generic_glue_retains_enum_dispatch_array_count_and_concrete_obligations() {
    let (_, _, _, drop) =
        checked("enum Choice<T> { Empty, Pair(T, T) } void f<T>(Choice<T> choice, T[3] values) {}");
    let variants = drop
        .glue
        .iter()
        .find_map(|glue| match &glue.kind {
            GlueKind::Enum(variants) => Some(variants),
            _ => None,
        })
        .unwrap();
    assert_eq!(variants.len(), 2);
    assert!(variants[0].fields.is_empty());
    assert_eq!(variants[1].fields.len(), 2);
    assert!(
        drop.glue
            .iter()
            .any(|glue| matches!(glue.kind, GlueKind::Array { count: 3, .. }))
    );
    assert!(drop.require_concrete().is_err());
}

#[test]
fn trivial_programs_need_no_flags_or_unresolved_glue() {
    let (_, _, _, drop) = checked("i32 f(i32 input) { return input + 1; }");
    assert!(drop.functions.iter().all(|body| body.flags.is_empty()));
    drop.require_concrete().unwrap();
}

#[test]
fn changed_flag_updates_branches_and_glue_are_rejected() {
    let (_, mut hir, core, drop) = checked("void f<T>(T value) {}");
    let mut missing_clear = drop.clone();
    let block = missing_clear.functions[0]
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, Terminator::InvokeGlue { .. }))
        .unwrap();
    block.instructions.clear();
    assert!(missing_clear.validate(&core, &mut hir).is_err());

    let mut skipped_drop = drop.clone();
    let term = skipped_drop.functions[0]
        .blocks
        .iter_mut()
        .find_map(|block| match &mut block.terminator {
            Terminator::TestFlag {
                initialized, clear, ..
            } => Some((initialized, clear)),
            _ => None,
        })
        .unwrap();
    *term.0 = *term.1;
    assert!(skipped_drop.validate(&core, &mut hir).is_err());

    let mut fake_glue = drop;
    fake_glue.glue[0].kind = GlueKind::Trivial;
    assert!(fake_glue.validate(&core, &mut hir).is_err());
}
