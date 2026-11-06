use cavo_compiler::{Compilation, packages};
use std::{
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let base = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("target/package-tests");
        std::fs::create_dir_all(&base).unwrap();
        let root = base.join(format!(
            "{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        Self(root)
    }
    fn put(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    fn manifest(&self) -> PathBuf {
        self.0.join("app/Cavo.toml")
    }
    fn setup(&self, visibility: &str) {
        self.put("app/Cavo.toml", "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[dependencies]\nlibrary = { path = \"../lib\" }\n");
        self.put(
            "app/src/main.cavo",
            "module app; import library::math; i32 main() { return math::value(); }",
        );
        self.put(
            "lib/Cavo.toml",
            "[package]\nname = \"library\"\nversion = \"0.1.0\"\n",
        );
        self.put(
            "lib/src/lib.cavo",
            &format!(
                "module math; @effects(bounded, pure) {visibility} i32 value() {{ return 7; }}"
            ),
        );
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn compile(graph: &packages::Graph) -> Compilation {
    let mut compilation = Compilation::default();
    for source in graph.sources().unwrap() {
        let file = compilation.sources.add(source.name, source.text).unwrap();
        compilation.parse(file);
    }
    compilation.check_mir();
    compilation
}

#[test]
fn path_packages_have_stable_namespaces_and_content_pinned_locks() {
    let project = Project::new();
    project.setup("pub");
    let first = packages::resolve(&project.manifest(), false, true).unwrap();
    let compilation = compile(&first);
    assert!(
        compilation.diagnostics.is_empty(),
        "{:#?}",
        compilation.diagnostics
    );
    first.write_lock().unwrap();
    let locked = packages::resolve(&project.manifest(), true, true).unwrap();
    assert_eq!(first.lock_text(), locked.lock_text());
    project.put(
        "lib/src/lib.cavo",
        "module math; @effects(bounded, pure) pub i32 value() { return 9; }",
    );
    assert!(
        packages::resolve(&project.manifest(), true, true)
            .unwrap_err()
            .contains("Cavo.lock")
    );
    let changed = packages::resolve(&project.manifest(), false, true).unwrap();
    assert_eq!(first.packages[0].namespace, changed.packages[0].namespace);
}

#[test]
fn package_visibility_does_not_leak_through_dependency_aliases() {
    for visibility in ["", "pub(package)"] {
        let project = Project::new();
        project.setup(visibility);
        let graph = packages::resolve(&project.manifest(), false, true).unwrap();
        let compilation = compile(&graph);
        assert!(
            compilation
                .diagnostics
                .iter()
                .any(|d| d.code == "E-NAME-PRIVATE"),
            "{:#?}",
            compilation.diagnostics
        );
    }
}

#[test]
fn cycles_escaping_sources_and_unpinned_git_are_rejected_before_checking() {
    let project = Project::new();
    project.setup("pub");
    project.put("lib/Cavo.toml", "[package]\nname = \"library\"\nversion = \"0.1.0\"\n[dependencies]\napp = { path = \"../app\" }\n");
    assert!(
        packages::resolve(&project.manifest(), false, true)
            .unwrap_err()
            .contains("cycle")
    );
    project.put("lib/Cavo.toml", "[package]\nname = \"library\"\nversion = \"0.1.0\"\nsources = [\"../app/src/main.cavo\"]\n");
    assert!(
        packages::resolve(&project.manifest(), false, true)
            .unwrap_err()
            .contains("source paths")
    );
    project.put("app/Cavo.toml", "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[dependencies]\nlib = { git = \"https://example.com/lib.git\", rev = \"main\" }\n");
    assert!(
        packages::resolve(&project.manifest(), false, true)
            .unwrap_err()
            .contains("commit ID")
    );
}

#[test]
fn offline_git_miss_does_not_create_a_partial_checkout() {
    let project = Project::new();
    project.setup("pub");
    project.put("app/Cavo.toml", "[package]\nname = \"app\"\nversion = \"0.1.0\"\n[dependencies]\nlib = { git = \"https://example.com/lib.git\", rev = \"0123456789012345678901234567890123456789\" }\n");
    let error = packages::resolve(&project.manifest(), false, true).unwrap_err();
    assert!(error.contains("offline package cache"), "{error}");
    assert!(!project.0.join("app/target/cavo/git").exists());
}

#[test]
fn a_local_copy_trait_cannot_grant_copy_to_a_dependency_type() {
    let project = Project::new();
    project.setup("pub");
    project.put(
        "lib/src/lib.cavo",
        "module math; pub struct Token { i32 value; }",
    );
    project.put("app/src/main.cavo","module app; import library::math; @lang(copy) trait Copy {} impl Copy for math::Token {} void main() {}");
    let graph = packages::resolve(&project.manifest(), false, true).unwrap();
    let compilation = compile(&graph);
    assert!(
        compilation
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E-IMPL-ORPHAN"),
        "{:#?}",
        compilation.diagnostics
    );
}

#[test]
fn cli_lock_check_and_capsule_round_trip_work_without_source_dependencies() {
    let project = Project::new();
    project.setup("pub");
    let binary = env!("CARGO_BIN_EXE_cavoite");
    let run = |args: &[&str]| {
        std::process::Command::new(binary)
            .args(args)
            .arg("--manifest-path")
            .arg(project.manifest())
            .output()
            .unwrap()
    };
    let lock = run(&["lock", "--offline"]);
    assert!(
        lock.status.success(),
        "{}",
        String::from_utf8_lossy(&lock.stderr)
    );
    let check = run(&["check", "--locked", "--offline"]);
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );
    let module = run(&["--emit=module", "--locked", "--offline"]);
    assert!(
        module.status.success(),
        "{}",
        String::from_utf8_lossy(&module.stderr)
    );
    project.put("module.cavm", &String::from_utf8(module.stdout).unwrap());
    let imported = cavo_compiler::modular::capsule::Module::decode(
        &std::fs::read_to_string(project.0.join("module.cavm")).unwrap(),
    )
    .unwrap();
    assert_eq!(imported.sources().len(), 2);
    // All proof inputs are in the capsule. Its reader never opens the original
    // package files, even after those temporary source fixtures disappear.
    std::fs::remove_dir_all(project.0.join("lib")).unwrap();
    assert!(
        cavo_compiler::modular::capsule::Module::decode(
            &std::fs::read_to_string(project.0.join("module.cavm")).unwrap()
        )
        .is_ok()
    );
}
