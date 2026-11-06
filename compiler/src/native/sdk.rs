use super::*;
use crate::external::{
    digest::sha256,
    json::{self, Json},
};
use std::{collections::BTreeMap, ffi::OsString, io::Read};

pub const LLAM_RELEASE: &str = "3.0.0";
pub const LLAM_REVISION: &str = "f0ea03c87be4a880b88a3b03bec48334762eb3d4";
pub const LLVM_VERSION: &str = "23.1.2";

const SOURCE_FILES: [(&str, &str, &str); 5] = [
    (
        "include/llam/runtime.h",
        "include/llam/runtime.h",
        "sha256:e80d6bdda69b51a954836c8367b596cbf14894394afbcbf2baa316f06dc69cbc",
    ),
    (
        "include/llam/managed.h",
        "include/llam/managed.h",
        "sha256:7a71b485e1546b0f29f1df3af55f5483d7478d87ded9d851f5f0491389d7e773",
    ),
    (
        "include/llam/io.h",
        "include/llam/io.h",
        "sha256:560823e0e50729256292e6b9f888c2b425a672ac33a7aef2bf4fc59b1014d5d3",
    ),
    (
        "include/llam/platform.h",
        "include/llam/platform.h",
        "sha256:3574ac17008ed65a6fa7b90e0280c10a5b600033e5327f63221994e73703cdf7",
    ),
    (
        "tools/preempt/managed_verify.py",
        "libexec/llam/managed_verify.py",
        "sha256:076b634f4e29004efff10a410eea45d10fd2c0b2d04577b192a33d9f6f8de68e",
    ),
];
const BINARY_FILES: [(&str, &str); 2] = [
    ("libllam_runtime.a", "lib/libllam_runtime.a"),
    ("llam_managed_pass.so", "lib/llam/llam_managed_pass.so"),
];

pub(super) struct Sdk {
    pub root: PathBuf,
}
impl Sdk {
    pub fn load(options: &Options) -> Result<Self, Error> {
        let root = options
            .llam_sdk
            .clone()
            .or_else(|| std::env::var_os("CAVO_LLAM_SDK").map(PathBuf::from))
            .unwrap_or_else(|| PathBuf::from("target/cavo-native-sdk/llam-3.0.0"));
        Self::at(&root)
    }
    fn at(root: &Path) -> Result<Self, Error> {
        let root=root.canonicalize().map_err(|error|failure("E-LLAM-SDK",format!("{}: {error}; prepare the pinned SDK with `cavoite sdk --llam-source ... --llam-build ... -o ...`",root.display())))?;
        let text = read(&root.join("cavo-sdk.json"), 1024 * 1024)?;
        let text = std::str::from_utf8(&text)
            .map_err(|_| failure("E-LLAM-SDK", "SDK manifest is not UTF-8"))?;
        let Json::Object(mut manifest) =
            json::parse_bounded(text, 1024 * 1024, 128).map_err(|e| failure("E-LLAM-SDK", e))?
        else {
            return Err(failure("E-LLAM-SDK", "invalid Cavo SDK manifest"));
        };
        if !matches!(manifest.remove("schema"),Some(Json::Number(1)))
            || ![("runtime",LLAM_RELEASE),("revision",LLAM_REVISION),("llvm",LLVM_VERSION)]
                .into_iter().all(|(key,expected)| matches!(manifest.remove(key),Some(Json::String(value)) if value==expected))
        {
            return Err(failure(
                "E-LLAM-SDK",
                "SDK release, revision or LLVM producer does not match the pinned profile",
            ));
        }
        let Some(Json::Object(files)) = manifest.remove("files") else {
            return Err(failure("E-LLAM-SDK", "SDK content identities are missing"));
        };
        if !manifest.is_empty() {
            return Err(failure("E-LLAM-SDK", "unknown SDK manifest field"));
        }
        validate_files(&root, &files)?;
        Ok(Self { root })
    }
    pub fn plugin(&self) -> PathBuf {
        self.root.join("lib/llam/llam_managed_pass.so")
    }
    pub fn library(&self) -> PathBuf {
        self.root.join("lib/libllam_runtime.a")
    }
    pub fn verifier(&self) -> PathBuf {
        self.root.join("libexec/llam/managed_verify.py")
    }
}

fn validate_files(root: &Path, files: &BTreeMap<String, Json>) -> Result<(), Error> {
    for (_, path, expected) in SOURCE_FILES {
        if !matches!(files.get(path),Some(Json::String(value)) if value==expected) {
            return Err(failure(
                "E-LLAM-SDK",
                format!("{path} does not name the pinned release material"),
            ));
        }
    }
    let paths = SOURCE_FILES
        .iter()
        .map(|(_, path, _)| *path)
        .chain(BINARY_FILES.iter().map(|(_, path)| *path))
        .chain(["LICENSE"]);
    for path in paths {
        let Some(Json::String(expected)) = files.get(path) else {
            return Err(failure(
                "E-LLAM-SDK",
                format!("missing SDK file identity: {path}"),
            ));
        };
        if &sha256(&read(&root.join(path), 128 * 1024 * 1024)?).to_string() != expected {
            return Err(failure(
                "E-LLAM-SDK",
                format!("SDK file changed after preparation: {path}"),
            ));
        }
    }
    if files.len() != SOURCE_FILES.len() + BINARY_FILES.len() + 1 {
        return Err(failure("E-LLAM-SDK", "unexpected SDK file identity"));
    }
    Ok(())
}

/// Prepare once from an existing qualified build of the exact release source.
/// The sibling checkout/build remain read-only; the resulting SDK is relocatable.
pub fn prepare(source: &Path, build: &Path, destination: &Path) -> Result<(), Error> {
    if destination.exists() {
        Sdk::at(destination)?;
        return Ok(());
    }
    source_identity(source, build)?;
    let parent = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    std::fs::create_dir_all(parent).map_err(|e| failure("E-LLAM-SDK", e.to_string()))?;
    let scratch = scratch::Scratch::new(parent)?;
    let mut identities = BTreeMap::new();
    for (input, output, expected) in SOURCE_FILES {
        let bytes = read(&source.join(input), 1024 * 1024)?;
        if sha256(&bytes).to_string() != expected {
            return Err(failure(
                "E-LLAM-SDK",
                format!("release source differs: {input}"),
            ));
        }
        install(&scratch.path, output, &bytes, &mut identities)?;
    }
    for (input, output) in BINARY_FILES {
        install(
            &scratch.path,
            output,
            &read(&build.join(input), 128 * 1024 * 1024)?,
            &mut identities,
        )?;
    }
    install(
        &scratch.path,
        "LICENSE",
        &read(&source.join("LICENSE"), 1024 * 1024)?,
        &mut identities,
    )?;
    let files = identities
        .iter()
        .map(|(path, digest)| format!("{}:{}", json::quote(path), json::quote(digest)))
        .collect::<Vec<_>>()
        .join(",");
    scratch.write(
        "cavo-sdk.json",
        &format!(
            "{{\"schema\":1,\"runtime\":{},\"revision\":{},\"llvm\":{},\"files\":{{{files}}}}}\n",
            json::quote(LLAM_RELEASE),
            json::quote(LLAM_REVISION),
            json::quote(LLVM_VERSION)
        ),
    )?;
    Sdk::at(&scratch.path)?;
    std::fs::rename(&scratch.path, destination).map_err(|e| failure("E-LLAM-SDK", e.to_string()))
}

fn source_identity(source: &Path, build: &Path) -> Result<(), Error> {
    let mut args = vec![
        OsString::from("-C"),
        source.as_os_str().into(),
        "diff".into(),
        "--name-only".into(),
        LLAM_REVISION.into(),
        "--".into(),
    ];
    args.extend(["include", "src", "tools/preempt", "CMakeLists.txt", "cmake"].map(OsString::from));
    if !tools::run(Path::new("git"), args, false)?.trim().is_empty() {
        return Err(failure(
            "E-LLAM-SDK",
            "LLAM source inputs differ from the pinned release; checkout changes were preserved",
        ));
    }
    let cache = read(&build.join("CMakeCache.txt"), 1024 * 1024)?;
    let cache = std::str::from_utf8(&cache)
        .map_err(|_| failure("E-LLAM-SDK", "build configuration is not UTF-8"))?;
    let source = source
        .canonicalize()
        .map_err(|e| failure("E-LLAM-SDK", e.to_string()))?;
    let from = cache
        .lines()
        .find_map(|line| line.strip_prefix("CMAKE_HOME_DIRECTORY:INTERNAL="))
        .map(PathBuf::from)
        .and_then(|path| path.canonicalize().ok());
    if from.as_deref() != Some(source.as_path())
        || !cache
            .lines()
            .any(|line| line == "LLAM_MANAGED_TOOLING:STRING=required")
        || !cache
            .lines()
            .any(|line| line == "LLAM_EXPERIMENTAL_ASYNC_PREEMPT:BOOL=ON")
    {
        return Err(failure(
            "E-LLAM-SDK",
            "the existing LLAM build must use this source, required managed tooling and async preemption",
        ));
    }
    Ok(())
}

fn install(
    root: &Path,
    name: &str,
    bytes: &[u8],
    identities: &mut BTreeMap<String, String>,
) -> Result<(), Error> {
    let path = root.join(name);
    std::fs::create_dir_all(path.parent().expect("SDK file parent"))
        .map_err(|e| failure("E-LLAM-SDK", e.to_string()))?;
    std::fs::write(path, bytes).map_err(|e| failure("E-LLAM-SDK", e.to_string()))?;
    identities.insert(name.into(), sha256(bytes).to_string());
    Ok(())
}

fn read(path: &Path, limit: usize) -> Result<Vec<u8>, Error> {
    let file = std::fs::File::open(path)
        .map_err(|e| failure("E-LLAM-SDK", format!("{}: {e}", path.display())))?;
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| failure("E-LLAM-SDK", e.to_string()))?;
    if bytes.len() > limit {
        return Err(failure(
            "E-LLAM-SDK",
            "SDK material exceeds its file budget",
        ));
    }
    Ok(bytes)
}
