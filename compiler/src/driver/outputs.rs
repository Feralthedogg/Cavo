//! Compiler-owned output records. Names, age and ignore rules never authorize
//! deletion: clean checks an exact ordinary path and its recorded content hash.
use crate::external::{
    Digest,
    digest::sha256,
    json::{self, Json},
};
use std::{
    fs::{self, File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    path::{Component, Path, PathBuf},
};

const LOCK: &str = "cavoite-output-lock-v1\n";
pub(super) struct Store {
    pub root: PathBuf,
    _lock: File,
}
pub(super) struct Clean {
    pub removed: usize,
    pub preserved: Vec<(PathBuf, String)>,
}

impl Store {
    pub fn open(project: &Path) -> Result<Self, String> {
        let project = project.canonicalize().map_err(|error| error.to_string())?;
        let target = project.join("target");
        directory(&target)?;
        let root = target.join("cavo");
        directory(&root)?;
        let path = root.join(".cavo-lock");
        ordinary_or_missing(&path)?;
        let mut lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)
            .map_err(|error| error.to_string())?;
        lock.try_lock().map_err(|error| {
            format!(
                "another Cavo build, run or clean owns {}: {error}",
                root.display()
            )
        })?;
        let mut marker = String::new();
        (&mut lock)
            .take(128)
            .read_to_string(&mut marker)
            .map_err(|error| error.to_string())?;
        if marker.is_empty() {
            lock.seek(SeekFrom::Start(0))
                .map_err(|error| error.to_string())?;
            lock.write_all(LOCK.as_bytes())
                .map_err(|error| error.to_string())?;
        } else if marker != LOCK {
            return Err("the output lock is not owned by cavoite".into());
        }
        Ok(Self { root, _lock: lock })
    }

    pub fn output(
        &self,
        triple: &str,
        profile: &str,
        name: &str,
        extension: Option<&str>,
    ) -> Result<PathBuf, String> {
        if !safe_component(triple) || !matches!(profile, "debug" | "release") {
            return Err("invalid native output target/profile".into());
        }
        let target = self.root.join(triple);
        directory(&target)?;
        let parent = target.join(profile);
        directory(&parent)?;
        let mut file = PathBuf::from(name);
        if file.components().count() != 1
            || !matches!(file.components().next(), Some(Component::Normal(_)))
        {
            return Err("output name must be a single file name".into());
        }
        if let Some(extension) = extension {
            let mut name = file.into_os_string();
            name.push(".");
            name.push(extension);
            file = PathBuf::from(name);
        }
        let path = parent.join(file);
        ordinary_or_missing(&path)?;
        if path.exists() {
            let record = self.record_path(&path)?;
            let entry = read_record(&record).map_err(|message| {
                format!(
                    "preserved unowned output {}: {message}; choose an explicit -o path",
                    path.display()
                )
            })?;
            if entry.0 != self.relative(&path)? || entry.1 != file_hash(&path)? {
                return Err(format!(
                    "{} is unowned or modified; choose an explicit -o path",
                    path.display()
                ));
            }
        }
        Ok(path)
    }

    pub fn record(&self, path: &Path) -> Result<(), String> {
        let parent = path
            .parent()
            .ok_or("output has no parent")?
            .canonicalize()
            .map_err(|error| error.to_string())?;
        let path = parent.join(path.file_name().ok_or("output has no name")?);
        if !path.starts_with(&self.root) {
            return Ok(());
        }
        check_path(&self.root, &path)?;
        let relative = self.relative(&path)?;
        let digest = file_hash(&path)?;
        let record = self.record_path(&path)?;
        directory(record.parent().expect("ownership directory"))?;
        ordinary_or_missing(&record)?;
        let text = format!(
            "{{\"schema\":1,\"tool\":\"cavoite\",\"path\":{},\"sha256\":{}}}\n",
            json::quote(&relative),
            json::quote(&digest.to_string())
        );
        atomic_text(&record, &text)
    }

    fn relative(&self, path: &Path) -> Result<String, String> {
        let path = path
            .strip_prefix(&self.root)
            .map_err(|_| "output is outside the owned tree")?;
        let components = path
            .components()
            .map(|component| match component {
                Component::Normal(name) => name.to_str().ok_or("owned output names must be UTF-8"),
                _ => Err("invalid output path"),
            })
            .collect::<Result<Vec<_>, _>>()?;
        if components.len() != 3
            || !safe_component(components[0])
            || !matches!(components[1], "debug" | "release")
        {
            return Err("owned output path must be target/profile/file".into());
        }
        Ok(components.join("/"))
    }

    fn record_path(&self, path: &Path) -> Result<PathBuf, String> {
        let relative = self.relative(path)?;
        Ok(self.root.join(".ownership").join(format!(
            "{}.json",
            sha256(relative.as_bytes())
                .to_string()
                .trim_start_matches("sha256:")
        )))
    }

    pub fn clean(&self) -> Result<Clean, String> {
        let directory = self.root.join(".ownership");
        if !directory.exists() {
            return Ok(Clean {
                removed: 0,
                preserved: Vec::new(),
            });
        }
        ordinary_directory(&directory)?;
        let mut result = Clean {
            removed: 0,
            preserved: Vec::new(),
        };
        for (index, entry) in fs::read_dir(&directory)
            .map_err(|error| error.to_string())?
            .enumerate()
        {
            if index >= 100_000 {
                return Err("output ownership inventory exceeds its limit".into());
            }
            let entry = entry.map_err(|error| error.to_string())?;
            let path = entry.path();
            if !record_name(&path) {
                continue;
            }
            match self.clean_record(&path) {
                Ok(removed) => result.removed += usize::from(removed),
                Err(message) => result.preserved.push((path, message)),
            }
        }
        Ok(result)
    }

    fn clean_record(&self, record: &Path) -> Result<bool, String> {
        let (relative, expected) = read_record(record)?;
        let path = self.root.join(&relative);
        if self.relative(&path)? != relative || self.record_path(&path)? != record {
            return Err("ownership path/key mismatch".into());
        }
        check_path(&self.root, &path)?;
        if !path.exists() {
            // A dangling link also has exists()==false; it is still user data.
            ordinary_or_missing(&path)?;
            fs::remove_file(record).map_err(|error| error.to_string())?;
            return Ok(false);
        }
        check_path(&self.root, &path)?;
        if file_hash(&path)? != expected {
            return Err(format!("preserved modified output {}", path.display()));
        }
        fs::remove_file(&path).map_err(|error| error.to_string())?;
        fs::remove_file(record).map_err(|error| error.to_string())?;
        if let Some(parent) = path.parent() {
            let _ = fs::remove_dir(parent);
        }
        Ok(true)
    }
}

fn safe_component(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 256
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
        && value != "."
        && value != ".."
}
fn record_name(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| {
            name.len() == 69
                && name.ends_with(".json")
                && name[..64].bytes().all(|byte| byte.is_ascii_hexdigit())
        })
}
fn ordinary_or_missing(path: &Path) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(metadata) if metadata.is_file() && !metadata.file_type().is_symlink() => Ok(()),
        Ok(_) => Err(format!("{} must be an ordinary file", path.display())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.to_string()),
    }
}
fn ordinary_directory(path: &Path) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if metadata.is_dir() && !metadata.file_type().is_symlink() {
        Ok(())
    } else {
        Err(format!("{} must be an ordinary directory", path.display()))
    }
}
fn directory(path: &Path) -> Result<(), String> {
    match fs::create_dir(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => ordinary_directory(path),
        Err(error) => Err(format!("{}: {error}", path.display())),
    }
}
fn check_path(root: &Path, path: &Path) -> Result<(), String> {
    let relative = path
        .strip_prefix(root)
        .map_err(|_| "output escaped the owned root")?;
    let mut parent = root.to_path_buf();
    for component in relative.components() {
        let Component::Normal(component) = component else {
            return Err("output contains a traversal component".into());
        };
        parent.push(component);
        if parent != path {
            ordinary_directory(&parent)?;
        } else {
            ordinary_or_missing(&parent)?;
        }
    }
    Ok(())
}
fn file_hash(path: &Path) -> Result<Digest, String> {
    ordinary_or_missing(path)?;
    let file = File::open(path).map_err(|error| error.to_string())?;
    if file.metadata().map_err(|error| error.to_string())?.len() > 256 * 1024 * 1024 {
        return Err("output exceeds the 256 MiB ownership hashing limit".into());
    }
    let mut bytes = Vec::new();
    file.take(256 * 1024 * 1024 + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() > 256 * 1024 * 1024 {
        return Err("output changed beyond its ownership hashing limit".into());
    }
    Ok(sha256(&bytes))
}
fn read_record(path: &Path) -> Result<(String, Digest), String> {
    ordinary_or_missing(path)?;
    let file = File::open(path).map_err(|error| error.to_string())?;
    let mut text = String::new();
    file.take(4097)
        .read_to_string(&mut text)
        .map_err(|error| error.to_string())?;
    let Json::Object(mut record) = json::parse_bounded(&text, 4096, 16)? else {
        return Err("invalid ownership record".into());
    };
    if !matches!(record.remove("schema"), Some(Json::Number(1)))
        || !matches!(record.remove("tool"), Some(Json::String(value)) if value == "cavoite")
    {
        return Err("unrecognized ownership record".into());
    }
    let Some(Json::String(path)) = record.remove("path") else {
        return Err("missing owned path".into());
    };
    let Some(Json::String(digest)) = record.remove("sha256") else {
        return Err("missing owned hash".into());
    };
    if !record.is_empty() {
        return Err("unknown ownership record field".into());
    }
    Ok((path, Digest::parse(&digest).ok_or("invalid owned hash")?))
}

pub(super) fn atomic_text(path: &Path, text: &str) -> Result<(), String> {
    ordinary_or_missing(path)?;
    let (mut file, temporary) = reserve_text(path.parent().ok_or("output has no parent")?)?;
    let result = (|| {
        file.write_all(text.as_bytes())
            .map_err(|error| error.to_string())?;
        drop(file);
        fs::rename(&temporary, path).map_err(|error| error.to_string())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

fn reserve_text(parent: &Path) -> Result<(File, PathBuf), String> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    for _ in 0..100 {
        let path = parent.join(format!(
            ".cavo-write-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((file, path)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error.to_string()),
        }
    }
    Err("could not reserve an atomic output file".into())
}
