//! Bounded, script-free package resolution. Dependency identity is independent
//! of source bodies; lock content separately pins every resolved source input.
mod manifest;
mod namespace;
mod resolve;
use crate::modular::capsule::Source;
pub use manifest::{Dependency, Manifest};
pub use resolve::{Graph, Package};
use std::path::Path;

pub fn resolve(path: &Path, locked: bool, offline: bool) -> Result<Graph, String> {
    let graph = resolve::load(path, offline)?;
    if locked {
        let actual = resolve::read_bounded(&graph.lock_path, 1024 * 1024)
            .map_err(|e| format!("--locked requires {}: {e}", graph.lock_path.display()))?;
        if actual != graph.lock_text() {
            return Err("Cavo.lock does not match the resolved package inputs; run `cavoite lock --manifest-path ...`".into());
        }
    }
    Ok(graph)
}

impl Graph {
    pub fn sources(&self) -> Result<Vec<Source>, String> {
        namespace::sources(self)
    }
    pub fn write_lock(&self) -> Result<(), String> {
        // The deterministic lock is the requested result, never a disposable
        // cache. Do not replace a symlink or a non-file at the destination.
        if std::fs::symlink_metadata(&self.lock_path)
            .is_ok_and(|m| !m.is_file() || m.file_type().is_symlink())
        {
            return Err("lock destination must be an ordinary file".into());
        }
        std::fs::write(&self.lock_path, self.lock_text()).map_err(|e| e.to_string())
    }
}
