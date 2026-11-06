use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

pub(super) struct Scratch {
    pub path: PathBuf,
}
impl Scratch {
    pub fn new(parent: &Path) -> Result<Self, Error> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let path = parent.join(format!(
                ".cavo-native-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(failure("E-NATIVE-OUTPUT", error.to_string())),
            }
        }
        Err(failure(
            "E-NATIVE-OUTPUT",
            "could not reserve a native compilation scratch directory",
        ))
    }
    pub fn file(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }
    pub fn write(&self, name: &str, text: &str) -> Result<PathBuf, Error> {
        let path = self.file(name);
        std::fs::write(&path, text)
            .map_err(|error| failure("E-NATIVE-OUTPUT", error.to_string()))?;
        Ok(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}
