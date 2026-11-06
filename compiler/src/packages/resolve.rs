use super::{Dependency, Manifest, manifest};
use crate::{
    external::{digest::sha256, json},
    modular::capsule::Source,
};
use std::{
    collections::BTreeMap,
    fmt::Write,
    io::Read,
    path::{Component, Path, PathBuf},
    process::Command,
};

#[derive(Debug)]
pub struct Package {
    pub manifest: Manifest,
    pub id: String,
    pub namespace: String,
    pub digest: String,
    pub sources: Vec<Source>,
    pub dependencies: BTreeMap<String, usize>,
}
#[derive(Debug)]
pub struct Graph {
    pub packages: Vec<Package>,
    pub root: usize,
    pub lock_path: PathBuf,
}
struct Resolver {
    packages: Vec<Package>,
    visited: BTreeMap<PathBuf, usize>,
    active: Vec<PathBuf>,
    root: PathBuf,
    offline: bool,
    bytes: usize,
}

pub(super) fn load(path: &Path, offline: bool) -> Result<Graph, String> {
    let path = path
        .canonicalize()
        .map_err(|e| format!("{}: {e}", path.display()))?;
    let root = path.parent().ok_or("manifest has no parent")?.to_owned();
    let lock_path = root.join("Cavo.lock");
    let mut resolver = Resolver {
        packages: Vec::new(),
        visited: BTreeMap::new(),
        active: Vec::new(),
        root,
        offline,
        bytes: 0,
    };
    let root = resolver.visit(path, None, None)?;
    Ok(Graph {
        packages: resolver.packages,
        root,
        lock_path,
    })
}

impl Resolver {
    fn visit(
        &mut self,
        path: PathBuf,
        git_id: Option<String>,
        boundary: Option<PathBuf>,
    ) -> Result<usize, String> {
        if self.active.contains(&path) {
            return Err(format!("package dependency cycle at {}", path.display()));
        }
        if let Some(&index) = self.visited.get(&path) {
            return Ok(index);
        }
        if self.active.len() >= 64 || self.packages.len() + self.active.len() >= 1024 {
            return Err("package graph resource limit exceeded".into());
        }
        self.active.push(path.clone());
        let directory = path.parent().ok_or("manifest has no directory")?;
        let (manifest, text) = manifest::read(&path)?;
        let sources = collect_sources(directory, &manifest.sources)?;
        self.bytes = self
            .bytes
            .saturating_add(sources.iter().map(|s| s.text.len()).sum::<usize>());
        if self.bytes > 8 * 1024 * 1024 {
            return Err("package graph exceeds its source byte budget".into());
        }
        let source_id =
            git_id.unwrap_or_else(|| format!("path:{}", relative(&self.root, directory)));
        let identity = format!("{}@{}+{}", manifest.name, manifest.version, source_id);
        let namespace = format!(
            "__cavo_pkg_{}",
            &sha256(identity.as_bytes()).to_string()[7..31]
        );
        let digest = content_digest(&text, &sources);
        let mut dependencies = BTreeMap::new();
        for (alias, dependency) in &manifest.dependencies {
            let (path, id, inherited_boundary) =
                self.dependency(directory, dependency, boundary.as_deref())?;
            dependencies.insert(alias.clone(), self.visit(path, id, inherited_boundary)?);
        }
        let index = self.packages.len();
        self.packages.push(Package {
            manifest,
            id: identity,
            namespace,
            digest,
            sources,
            dependencies,
        });
        self.visited.insert(path, index);
        self.active.pop();
        Ok(index)
    }

    fn dependency(
        &self,
        directory: &Path,
        dependency: &Dependency,
        boundary: Option<&Path>,
    ) -> Result<(PathBuf, Option<String>, Option<PathBuf>), String> {
        match dependency {
            Dependency::Path(path) => {
                let path = directory
                    .join(path)
                    .join("Cavo.toml")
                    .canonicalize()
                    .map_err(|e| e.to_string())?;
                if boundary.is_some_and(|root| !path.starts_with(root)) {
                    return Err("a Git package path dependency escapes its pinned checkout".into());
                }
                Ok((path, None, boundary.map(Path::to_owned)))
            }
            Dependency::Git { url, revision } => {
                let path = git_checkout(&self.root, url, revision, self.offline)?;
                Ok((
                    path.join("Cavo.toml"),
                    Some(format!("git:{url}#{revision}")),
                    Some(path),
                ))
            }
        }
    }
}

impl Graph {
    pub fn lock_text(&self) -> String {
        let mut packages: Vec<_> = self.packages.iter().collect();
        packages.sort_by_key(|p| &p.id);
        let mut output = format!(
            "{{\"schema\":1,\"compiler\":{},\"root\":{},\"packages\":[",
            json::quote(env!("CARGO_PKG_VERSION")),
            json::quote(&self.packages[self.root].id)
        );
        for (index, package) in packages.iter().enumerate() {
            if index > 0 {
                output.push(',');
            }
            let _ = write!(
                output,
                "{{\"id\":{},\"content\":{},\"dependencies\":{{",
                json::quote(&package.id),
                json::quote(&package.digest)
            );
            for (index, (alias, dependency)) in package.dependencies.iter().enumerate() {
                if index > 0 {
                    output.push(',');
                }
                let _ = write!(
                    output,
                    "{}:{}",
                    json::quote(alias),
                    json::quote(&self.packages[*dependency].id)
                );
            }
            output.push_str("}}");
        }
        output.push_str("]}\n");
        output
    }
}

fn collect_sources(root: &Path, requested: &[String]) -> Result<Vec<Source>, String> {
    let paths = if requested.is_empty() {
        discover(&root.join("src"))?
    } else {
        requested
            .iter()
            .map(|name| {
                let path = Path::new(name);
                if path
                    .components()
                    .any(|c| !matches!(c, Component::Normal(_)))
                    || name.contains('\\')
                {
                    return Err(
                        "package source paths must stay inside the package directory".into(),
                    );
                }
                checked_source(root, &root.join(path))
            })
            .collect::<Result<Vec<_>, String>>()?
    };
    if paths.is_empty() || paths.len() > 1024 {
        return Err("package must contain 1..1024 Cavo sources".into());
    }
    let mut sources = BTreeMap::new();
    let mut bytes = 0usize;
    for path in paths {
        let path = checked_source(root, &path)?;
        let name = path
            .strip_prefix(root)
            .map_err(|e| e.to_string())?
            .to_str()
            .ok_or("source path must be UTF-8")?
            .replace('\\', "/");
        let text = read_bounded(&path, 1024 * 1024)?;
        bytes = bytes.saturating_add(text.len());
        if bytes > 8 * 1024 * 1024 {
            return Err("package exceeds its source byte budget".into());
        }
        if sources.insert(name, text).is_some() {
            return Err("duplicate package source".into());
        }
    }
    Ok(sources
        .into_iter()
        .map(|(name, text)| Source { name, text })
        .collect())
}

fn checked_source(root: &Path, path: &Path) -> Result<PathBuf, String> {
    if path.extension().and_then(|e| e.to_str()) != Some("cavo") {
        return Err("package sources must use .cavo".into());
    }
    let relative = path.strip_prefix(root).map_err(|e| e.to_string())?;
    let mut current = root.to_owned();
    for part in relative.components() {
        if !matches!(part, Component::Normal(_)) {
            return Err("source path escapes package root".into());
        }
        current.push(part);
        if std::fs::symlink_metadata(&current)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_symlink()
        {
            return Err("package sources cannot follow symlinks".into());
        }
    }
    let canonical = path.canonicalize().map_err(|e| e.to_string())?;
    if !canonical.starts_with(root) || !canonical.is_file() {
        return Err("package source is not a regular contained file".into());
    }
    Ok(canonical)
}

fn discover(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut pending = vec![(root.to_owned(), 0)];
    let mut files = Vec::new();
    let mut entries = 0;
    while let Some((directory, depth)) = pending.pop() {
        if depth > 64 {
            return Err("source directory nesting limit exceeded".into());
        }
        if std::fs::symlink_metadata(&directory)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_symlink()
        {
            return Err("source directories cannot be symlinks".into());
        }
        for entry in std::fs::read_dir(&directory).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            entries += 1;
            if entries > 16384 {
                return Err("source discovery entry limit exceeded".into());
            }
            let kind = entry.file_type().map_err(|e| e.to_string())?;
            if kind.is_dir() {
                pending.push((entry.path(), depth + 1));
            } else if entry.path().extension().and_then(|e| e.to_str()) == Some("cavo") {
                files.push(entry.path());
            }
        }
    }
    files.sort();
    Ok(files)
}

pub(super) fn read_bounded(path: &Path, limit: usize) -> Result<String, String> {
    let file = std::fs::File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut text = String::new();
    file.take(limit as u64 + 1)
        .read_to_string(&mut text)
        .map_err(|e| e.to_string())?;
    if text.len() > limit {
        return Err(format!("{} exceeds its byte limit", path.display()));
    }
    Ok(text)
}

fn content_digest(manifest: &str, sources: &[Source]) -> String {
    let mut bytes = manifest.as_bytes().to_vec();
    bytes.push(0);
    for source in sources {
        bytes.extend_from_slice(source.name.as_bytes());
        bytes.push(0);
        bytes.extend_from_slice(source.text.as_bytes());
        bytes.push(0);
    }
    sha256(&bytes).to_string()
}

fn relative(root: &Path, target: &Path) -> String {
    let left: Vec<_> = root.components().collect();
    let right: Vec<_> = target.components().collect();
    let shared = left.iter().zip(&right).take_while(|(a, b)| a == b).count();
    let mut value = PathBuf::new();
    for _ in shared..left.len() {
        value.push("..");
    }
    for part in &right[shared..] {
        value.push(part.as_os_str());
    }
    if value.as_os_str().is_empty() {
        ".".into()
    } else {
        value.to_string_lossy().replace('\\', "/")
    }
}

fn git_checkout(root: &Path, url: &str, revision: &str, offline: bool) -> Result<PathBuf, String> {
    let identity = sha256(format!("{url}#{revision}").as_bytes()).to_string();
    let path = root.join("target/cavo/git").join(&identity[7..]);
    if !path.exists() {
        if offline {
            return Err("pinned Git dependency is absent from the offline package cache".into());
        }
        std::fs::create_dir_all(&path).map_err(|e| e.to_string())?;
        git(&path, &["init", "--quiet"])?;
        git(
            &path,
            &[
                "fetch",
                "--quiet",
                "--depth=1",
                "--no-tags",
                "--",
                url,
                revision,
            ],
        )?;
        git(&path, &["checkout", "--quiet", "--detach", "FETCH_HEAD"])?;
    }
    let actual = git(&path, &["rev-parse", "HEAD"])?;
    if actual.trim() != revision
        || !git(&path, &["status", "--porcelain", "--untracked-files=all"])?
            .trim()
            .is_empty()
    {
        return Err("pinned Git cache revision/content is not clean; refusing to reuse it".into());
    }
    path.canonicalize().map_err(|e| e.to_string())
}

fn git(directory: &Path, arguments: &[&str]) -> Result<String, String> {
    let result = Command::new("git")
        .current_dir(directory)
        .args([
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "protocol.file.allow=never",
            "-c",
            "core.autocrlf=false",
        ])
        .args(arguments)
        .env(
            "GIT_CONFIG_GLOBAL",
            if cfg!(windows) { "NUL" } else { "/dev/null" },
        )
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .map_err(|e| e.to_string())?;
    if !result.status.success() {
        return Err(format!(
            "pinned Git resolution failed: {}",
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    String::from_utf8(result.stdout).map_err(|e| e.to_string())
}
