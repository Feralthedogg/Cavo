#[path = "support/reference.rs"]
mod reference;

use cavo_compiler::{Compilation, mono, native};
use reference::{Error, Limits, Machine, Outcome, Stimulus, Value};
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

fn program(source: &str) -> (Compilation, mono::Program) {
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("reference.cavo", source.into())
        .unwrap();
    compilation.parse(file);
    let program = compilation
        .check_monomorphized()
        .unwrap_or_else(|| panic!("{source}\n{:#?}", compilation.diagnostics));
    (compilation, program)
}

fn integer(value: Outcome) -> i32 {
    let Outcome::Returned(value) = value else {
        panic!("not a normal return: {value:?}");
    };
    value.unsigned().unwrap() as u32 as i32
}

#[test]
fn reference_executes_calls_branches_loops_and_concrete_generic_values() {
    for (source, expected) in [
        (
            "i32 twice(i32 n) { return n * 2; } i32 main() { i32 n = 0; for (i32 i = 0; i < 6; i += 1) { n += twice(i); } return n; }",
            30,
        ),
        (
            "T identity<T>(T n) { return move n; } i32 main() { return identity::<i32>(7); }",
            7,
        ),
        (
            "enum Choice { A(i32), B } i32 main() { auto value = Choice::A(19); return match (move value) { Choice::A(n) => n, Choice::B => 0 }; }",
            19,
        ),
        (
            "i32 main() { i32[4] values = [1, 2, 3, 4]; i32 sum = 0; for (auto n in values) { sum += n; } return sum; }",
            10,
        ),
    ] {
        let (compilation, program) = program(source);
        let mut machine = Machine::new(&program, &compilation.symbols);
        assert_eq!(integer(machine.run("main", vec![]).unwrap()), expected);
    }
}

#[test]
fn reference_executes_slices_indirect_calls_closures_dyn_and_wide_numbers() {
    for (source, expected) in [
        (
            "i32 sum(&[i32] values) { i32 total = 0; for (auto value in values) { total += value; } return total; } i32 main() { i32[3] values = [2, 3, 4]; return sum(&values); }",
            9,
        ),
        (
            "i32 twice(i32 n) { return n + n; } i32 main() { fn(i32) -> i32 f = twice; return f(9); }",
            18,
        ),
        (
            "i32 main() { i32 base = 5; auto add = [&base](i32 n) -> i32 { return base + n; }; return add(3); }",
            8,
        ),
        (
            "trait Read { i32 value(&Self self); } struct Number { i32 n; } impl Read for Number { i32 value(&Self self) { return self.n; } } i32 read(&dyn Read value) { return value.value(); } i32 main() { Number n = Number { n: 17 }; return read(&n); }",
            17,
        ),
        (
            "i32 main() { f64 a = 1.5; f64 b = 2.5; return match (a + b == 4.0) { true => 7, false => 0 }; }",
            7,
        ),
        (
            "i32 main() { u128 a = 1; u128 b = a << 100; return match (b > 0) { true => 3, false => 0 }; }",
            3,
        ),
        (
            "union Bits { i32 number; bool flag; } i32 main() { contract { Bits b = Bits { flag: true }; b.number = 23; Bits moved = move b; return moved.number; } }",
            23,
        ),
    ] {
        let (compilation, program) = program(source);
        let mut machine = Machine::new(&program, &compilation.symbols);
        assert_eq!(
            integer(
                machine
                    .run("main", vec![])
                    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            ),
            expected
        );
    }
}

#[test]
fn reference_keeps_zero_sized_array_elements_as_distinct_owned_objects() {
    let source = "@lang(drop) trait Drop { void drop(&mut Self self); } struct Empty {} impl Drop for Empty { void drop(&mut Self self) {} } i32 main() { Empty[2] values = [Empty {}, Empty {}]; for (auto value in move values) { break; } return 0; }";
    let (compilation, program) = program(source);
    let mut machine = Machine::new(&program, &compilation.symbols);
    assert_eq!(integer(machine.run("main", vec![]).unwrap()), 0);
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| matches!(event, reference::Event::Destructor(_)))
            .count(),
        2
    );
}

const HEAP: &str = r#"
@lang(copy) trait Copy {}
@intrinsic(allocate) ptr<T> allocate<T>(usize count);
@intrinsic(ptr_initialize) void initialize<T>(ptr<T> p, T value);
@intrinsic(ptr_read) T read<T: Copy>(ptr<T> p);
@intrinsic(deallocate) void release<T>(ptr<T> p);
void ignore(ptr<i32> p, i32 value) {}
void sink(ptr<i32> p) {}
i32 main() {
    contract { auto p = allocate::<i32>(1); initialize(p, 19); i32 value = read(p); release(p); sink(p); return value; }
}
"#;

#[test]
fn reference_heap_intrinsics_preserve_initialization_and_free() {
    let (compilation, program) = program(HEAP);
    let mut machine = Machine::new(&program, &compilation.symbols);
    assert_eq!(integer(machine.run("main", vec![]).unwrap()), 19);
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| matches!(event, reference::Event::Freed(_)))
            .count(),
        1
    );
}

#[test]
fn reference_detects_a_missing_initialization_and_a_repeated_heap_free() {
    for (original, replacement) in [("initialize", "ignore"), ("sink", "release")] {
        let (compilation, mut program) = program(HEAP);
        let machine = Machine::new(&program, &compilation.symbols);
        let replacement = if replacement == "release" {
            *program
                .hir
                .contracts
                .intrinsics
                .iter()
                .find(|(_, role)| **role == cavo_compiler::contracts::Intrinsic::Deallocate)
                .unwrap()
                .0
        } else {
            machine.definition(replacement)
        };
        drop(machine);
        let body = program
            .mir
            .functions
            .iter_mut()
            .find(|body| {
                compilation
                    .symbols
                    .get(program.hir.definitions[body.definition].name)
                    == "main"
            })
            .unwrap();
        let mut changed = false;
        for block in &mut body.blocks {
            if let cavo_compiler::mir::Terminator::Call {
                callee: cavo_compiler::mir::Operand::Function { definition, .. },
                ..
            } = &mut block.terminator
                && compilation
                    .symbols
                    .get(program.hir.definitions[*definition].name)
                    == original
            {
                *definition = replacement;
                changed = true;
            }
        }
        assert!(changed);
        let mut machine = Machine::new(&program, &compilation.symbols);
        assert!(
            matches!(machine.run("main", vec![]), Err(Error::Undefined(_))),
            "missed {original} -> {replacement:?}"
        );
    }
}

#[test]
fn reference_detects_use_after_move() {
    let (compilation, mut program) = program(
        "struct Packet { i32 n; } i32 main() { Packet first = Packet { n: 7 }; Packet second = move first; return second.n; }",
    );
    let body = program
        .mir
        .functions
        .iter_mut()
        .find(|body| {
            compilation
                .symbols
                .get(program.hir.definitions[body.definition].name)
                == "main"
        })
        .unwrap();
    let first = cavo_compiler::mir::LocalId(
        body.locals
            .iter()
            .position(|local| {
                local
                    .name
                    .is_some_and(|name| compilation.symbols.get(name) == "first")
            })
            .unwrap() as u32,
    );
    let second = cavo_compiler::mir::LocalId(
        body.locals
            .iter()
            .position(|local| {
                local
                    .name
                    .is_some_and(|name| compilation.symbols.get(name) == "second")
            })
            .unwrap() as u32,
    );
    let mut changed = false;
    for block in &mut body.blocks {
        for statement in &mut block.statements {
            if let cavo_compiler::mir::StatementKind::Assign {
                value: cavo_compiler::mir::Rvalue::Use(cavo_compiler::mir::Operand::Copy(place)),
                ..
            } = &mut statement.kind
                && place.local == second
                && !place.projection.is_empty()
            {
                place.local = first;
                changed = true;
            }
        }
    }
    assert!(changed);
    assert!(matches!(
        Machine::new(&program, &compilation.symbols).run("main", vec![]),
        Err(Error::Undefined(_))
    ));
}

#[test]
fn reference_detects_double_destructor_invocation() {
    let (compilation, mut program) = self::program(DROPS);
    let main = Machine::new(&program, &compilation.symbols).definition("main");
    let body = program
        .analysis
        .drops
        .functions
        .iter_mut()
        .find(|body| body.definition == main)
        .unwrap();
    for (index, block) in body.blocks.iter_mut().enumerate() {
        if let cavo_compiler::mir::drop::Terminator::InvokeGlue { glue, next, .. } =
            &mut block.terminator
            && matches!(
                program.analysis.drops.glue[glue.0 as usize].kind,
                cavo_compiler::mir::drop::GlueKind::Destructor { .. }
                    | cavo_compiler::mir::drop::GlueKind::User { .. }
            )
        {
            *next = cavo_compiler::mir::drop::BlockId(index as u32);
        }
    }
    let result = Machine::new(&program, &compilation.symbols).run("main", vec![]);
    assert!(
        matches!(result, Err(Error::Undefined("double drop"))),
        "{result:?}"
    );
}

#[test]
fn explicit_call_test_bindings_are_execution_stimuli_without_approvals() {
    let (compilation, program) =
        program("i32 provided() { return 0; } i32 main() { return provided(); }");
    let mut machine = Machine::new(&program, &compilation.symbols);
    let definition = machine.definition("provided");
    let cavo_compiler::types::Ty::Function { result, .. } = program
        .hir
        .types
        .get(program.hir.definitions[definition].ty)
    else {
        panic!();
    };
    machine
        .stimuli
        .insert(definition, Stimulus::Return(Value::integer(*result, 21)));
    assert_eq!(integer(machine.run("main", vec![]).unwrap()), 21);
}

#[test]
fn reference_models_a_deterministic_scoped_child_and_join() {
    let core = r#"
@lang(result) enum Outcome<T, E> { Ok(T), Err(E) }
@lang(task) struct Work<'scope, T> {}
@lang(spawn_error) struct Admission<F> { F capture; }
@lang(task_error) enum Fault { Cancelled, Panicked }
impl<'scope, T> Work<'scope, T> {
    @intrinsic(task_join) Outcome<T, Fault> join(Self self);
    @intrinsic(task_cancel) void cancel(&Self self);
    @intrinsic(task_ignore) void ignore_result(Self self);
}

i32 child(i32 value) { return value + value; }
i32 main() { scope { auto admission = spawn child(21); return match (move admission) { Outcome::Ok(task) => match task.join() { Outcome::Ok(n) => n, Outcome::Err(_) => 0 }, Outcome::Err(_) => 0 }; } }
"#;
    let (compilation, program) = program(core);
    let mut machine = Machine::new(&program, &compilation.symbols);
    assert_eq!(integer(machine.run("main", vec![]).unwrap()), 42);
}

#[test]
fn reference_distinguishes_defined_fatal_checks_from_undefined_memory() {
    for source in [
        "i32 main() { i32 value = 2147483647; return value + 1; }",
        "i32 main() { i32 value = 0; return 4 / value; }",
        "i32 main() { i32[2] values = [1, 2]; usize n = 2; return values[n]; }",
    ] {
        let (compilation, program) = program(source);
        let mut machine = Machine::new(&program, &compilation.symbols);
        assert_eq!(machine.run("main", vec![]).unwrap(), Outcome::Aborted);
    }
}

#[test]
fn reference_memory_tracks_generations_initialization_bounds_and_ownership() {
    let mut memory = reference::Memory::new(64, 16);
    let pointer = memory.heap(8).unwrap();
    assert!(matches!(
        memory.read_bytes(&pointer, 1),
        Err(Error::Undefined(_))
    ));
    memory
        .write_bytes(&pointer, &[1, 2, 3, 4, 5, 6, 7, 8])
        .unwrap();
    assert_eq!(
        memory.read_bytes(&pointer, 8).unwrap(),
        vec![1, 2, 3, 4, 5, 6, 7, 8]
    );
    let mut outside = pointer.clone();
    outside.offset = 8;
    assert!(matches!(
        memory.read_bytes(&outside, 1),
        Err(Error::Undefined(_))
    ));
    memory.free(&pointer).unwrap();
    assert!(matches!(
        memory.read_bytes(&pointer, 1),
        Err(Error::Undefined(_))
    ));
    assert!(matches!(memory.free(&pointer), Err(Error::Undefined(_))));
    let stack = memory.stack(4).unwrap();
    assert!(matches!(memory.free(&stack), Err(Error::Undefined(_))));
}

#[test]
fn reference_rejects_invalid_bool_char_enum_and_pointer_representations() {
    let (compilation, program) = program(
        "enum Choice { A, B } i32 main() { return 0; } bool flag(bool n) { return n; } char scalar(char c) { return c; } Choice tag(Choice c) { return move c; } ptr<i32> address(ptr<i32> p) { return p; }",
    );
    let mut machine = Machine::new(&program, &compilation.symbols);
    for (function, bits) in [("flag", 2u128), ("scalar", 0xD800)] {
        let definition = machine.definition(function);
        let cavo_compiler::types::Ty::Function { parameters, .. } = program
            .hir
            .types
            .get(program.hir.definitions[definition].ty)
        else {
            panic!();
        };
        let ty = parameters[0];
        let pointer = machine
            .memory
            .stack(program.layouts.get(ty).unwrap().size)
            .unwrap();
        machine
            .memory
            .write_bytes(
                &pointer,
                &bits.to_le_bytes()[..program.layouts.get(ty).unwrap().size as usize],
            )
            .unwrap();
        assert!(matches!(
            machine.load(&pointer, ty),
            Err(Error::Undefined(_))
        ));
    }
    for function in ["tag", "address"] {
        let definition = machine.definition(function);
        let cavo_compiler::types::Ty::Function { parameters, .. } = program
            .hir
            .types
            .get(program.hir.definitions[definition].ty)
        else {
            panic!();
        };
        let ty = parameters[0];
        let size = program.layouts.get(ty).unwrap().size;
        let pointer = machine.memory.stack(size).unwrap();
        machine
            .memory
            .write_bytes(&pointer, &vec![0xff; size as usize])
            .unwrap();
        assert!(matches!(
            machine.load(&pointer, ty),
            Err(Error::Undefined(_))
        ));
    }
}

#[test]
fn a_budget_limit_is_not_a_successful_or_undefined_execution() {
    let (compilation, program) = program("i32 main() { while (true) {} return 0; }");
    let mut machine = Machine::with_limits(
        &program,
        &compilation.symbols,
        Limits {
            steps: 100,
            ..Limits::default()
        },
    );
    assert!(matches!(machine.run("main", vec![]), Err(Error::Limit(_))));
}

const DROPS: &str = r#"
@lang(drop) trait Drop { void drop(&mut Self self); }
struct Mark<'a> { &'a mut i32 count; }
impl<'a> Drop for Mark<'a> { void drop(&mut Self self) { *self.count += 1; } }
i32 failure() { return 0; }
i32 inspect(&mut i32 count) { Mark mark = Mark { count: &mut *count }; return failure(); }
i32 main() { i32 count = 0; { Mark mark = Mark { count: &mut count }; } return count; }
"#;

#[test]
fn reference_runs_normal_panic_and_cancel_cleanup_deterministically() {
    let (compilation, program) = program(DROPS);
    for stimulus in [None, Some(Stimulus::Panic), Some(Stimulus::Cancel)] {
        let mut machine = Machine::new(&program, &compilation.symbols);
        let definition = machine.definition("inspect");
        let cavo_compiler::types::Ty::Function { parameters, .. } = program
            .hir
            .types
            .get(program.hir.definitions[definition].ty)
        else {
            panic!();
        };
        let cavo_compiler::types::Ty::Reference { inner, .. } =
            program.hir.types.get(parameters[0])
        else {
            panic!();
        };
        let mut reference = machine.cell(Value::integer(*inner, 0)).unwrap();
        reference.ty = parameters[0];
        let pointer = reference.address().unwrap();
        if let Some(stimulus) = stimulus.clone() {
            machine
                .stimuli
                .insert(machine.definition("failure"), stimulus);
        }
        let outcome = machine.run("inspect", vec![reference]).unwrap();
        assert_eq!(
            machine.load(&pointer, *inner).unwrap().unsigned().unwrap(),
            1
        );
        assert_eq!(
            machine
                .events
                .iter()
                .filter(|event| matches!(event, reference::Event::Destructor(_)))
                .count(),
            1
        );
        match stimulus {
            None => assert_eq!(integer(outcome), 0),
            Some(Stimulus::Panic) => assert_eq!(outcome, Outcome::Panicked),
            Some(Stimulus::Cancel) => assert_eq!(outcome, Outcome::Cancelled),
            _ => unreachable!(),
        }
    }
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let parent = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("target/reference-tests");
        std::fs::create_dir_all(&parent).unwrap();
        let path = parent.join(format!(
            "{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn llvm() -> Option<PathBuf> {
    let explicit = std::env::var_os("CAVO_LLVM_BIN").map(PathBuf::from);
    let required = explicit.is_some() || std::env::var_os("CAVO_NATIVE_REQUIRED").is_some();
    let path = explicit
        .or_else(|| {
            ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"]
                .into_iter()
                .map(PathBuf::from)
                .find(|path| path.join("llc").is_file())
        })
        .filter(|path| {
            Command::new(path.join(if cfg!(windows) { "llc.exe" } else { "llc" }))
                .arg("--version")
                .output()
                .is_ok_and(|output| {
                    output.status.success()
                        && String::from_utf8_lossy(&output.stdout)
                            .split_whitespace()
                            .any(|word| word == native::LLVM_VERSION)
                })
        });
    assert!(
        path.is_some() || !required,
        "reference differential tests require LLVM 23.1.2"
    );
    path
}

#[test]
fn differential_reference_matches_native_o0_and_o2_for_every_defined_fixture() {
    let Some(llvm) = llvm() else {
        return;
    };
    for source in [
        "i32 main() { i32 n = 0; for (i32 i = 0; i < 8; i += 1) { n += i; } return n; }",
        "struct Pair { i32 x; i32 y; } i32 main() { Pair p = Pair { y: 9, x: 3 }; return p.x + p.y; }",
        "enum E { Value(i32), Empty } i32 main() { auto e = E::Value(31); return match (move e) { E::Value(n) => n, E::Empty => 0 }; }",
        DROPS,
    ] {
        let (compilation, mut program) = program(source);
        let expected = integer(
            Machine::new(&program, &compilation.symbols)
                .run("main", vec![])
                .unwrap(),
        );
        for optimization in [native::Optimization::O0, native::Optimization::O2] {
            let scratch = Scratch::new();
            let executable = scratch.0.join(if cfg!(windows) {
                "program.exe"
            } else {
                "program"
            });
            let options = native::Options {
                runtime: native::Runtime::None,
                llvm_bin: Some(llvm.clone()),
                optimization,
                ..native::Options::default()
            };
            native::build(
                &mut program,
                &compilation.symbols,
                &options,
                native::OutputKind::Executable,
                &executable,
            )
            .unwrap();
            let result = Command::new(executable).output().unwrap();
            assert_eq!(
                result.status.code(),
                Some(expected),
                "{optimization:?}: {source}\n{}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
    }
}

#[test]
fn bounded_memory_also_counts_zero_sized_logical_values() {
    let (compilation, program) = program(
        "@lang(copy) trait Copy {} struct Empty {} impl Copy for Empty {} i32 main() { Empty[64] values = [Empty {}; 64]; return 0; }",
    );
    let mut machine = Machine::with_limits(
        &program,
        &compilation.symbols,
        Limits {
            objects: 32,
            ..Limits::default()
        },
    );
    assert!(matches!(machine.run("main", vec![]), Err(Error::Limit(_))));
}

#[test]
fn reference_drops_unobserved_task_results_at_the_registry_barrier() {
    let source = r#"
@lang(result) enum Outcome<T, E> { Ok(T), Err(E) }
@lang(task) struct Work<'scope, T> {}
@lang(spawn_error) struct Admission<F> { F capture; }
@lang(task_error) enum Fault { Cancelled, Panicked }
impl<'scope, T> Work<'scope, T> {
    @intrinsic(task_join) Outcome<T, Fault> join(Self self);
    @intrinsic(task_cancel) void cancel(&Self self);
    @intrinsic(task_ignore) void ignore_result(Self self);
}
@lang(drop) trait Drop { void drop(&mut Self self); }
struct Mark<'a> { &'a mut i32 count; }
impl<'a> Drop for Mark<'a> { void drop(&mut Self self) { *self.count += 1; } }
Mark<'a> child<'a>(&'a mut i32 count) { return Mark { count: move count }; }
i32 main() { i32 count = 0; scope { auto admission = spawn child(&mut count); } return count; }
"#;
    let (compilation, program) = program(source);
    let mut machine = Machine::new(&program, &compilation.symbols);
    assert_eq!(integer(machine.run("main", vec![]).unwrap()), 1);
    assert_eq!(
        machine
            .events
            .iter()
            .filter(|event| matches!(event, reference::Event::Destructor(_)))
            .count(),
        1
    );
}
