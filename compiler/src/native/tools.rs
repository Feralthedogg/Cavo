use super::*;
use std::{
    ffi::{OsStr, OsString},
    process::Command,
};

pub(super) struct Tools {
    pub bin: PathBuf,
    pub target: String,
    pub system_flags: Vec<OsString>,
}

impl Tools {
    pub fn discover(options: &Options) -> Result<Self, Error> {
        let bin = options
            .llvm_bin
            .clone()
            .or_else(|| std::env::var_os("CAVO_LLVM_BIN").map(PathBuf::from))
            .or_else(|| std::env::var_os("LLAM_LLVM_BIN").map(PathBuf::from))
            .or_else(default_bin)
            .ok_or_else(|| {
                failure(
                    "E-LLVM-TOOLS",
                    "LLVM 23.1.2 tools are missing; pass --llvm-bin /path/to/llvm/bin",
                )
            })?;
        for name in ["clang", "opt", "llc", "llvm-objdump"] {
            let output = run(
                &bin.join(executable(name)),
                [OsString::from("--version")],
                false,
            )?;
            if !output
                .split(|c: char| !(c.is_ascii_alphanumeric() || c == '.'))
                .any(|word| word == LLVM_VERSION)
            {
                return Err(failure(
                    "E-LLVM-VERSION",
                    format!(
                        "{} must belong to LLVM {LLVM_VERSION}",
                        bin.join(name).display()
                    ),
                ));
            }
        }
        let target = run(
            &bin.join(executable("clang")),
            [OsString::from("-dumpmachine")],
            false,
        )?
        .trim()
        .to_owned();
        let mut system_flags = Vec::new();
        if target.contains("apple") {
            let sdk = run(
                Path::new("xcrun"),
                [OsString::from("--show-sdk-path")],
                false,
            )?;
            system_flags.extend([OsString::from("-isysroot"), OsString::from(sdk.trim())]);
        }
        Ok(Self {
            bin,
            target,
            system_flags,
        })
    }
    pub fn path(&self, name: &str) -> PathBuf {
        self.bin.join(executable(name))
    }
    pub fn invoke(
        &self,
        name: &str,
        arguments: Vec<OsString>,
        managed: bool,
    ) -> Result<String, Error> {
        run(&self.path(name), arguments, managed)
    }
}

fn default_bin() -> Option<PathBuf> {
    let known = ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"];
    known
        .into_iter()
        .map(PathBuf::from)
        .chain(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ))
        .find(|directory| {
            directory.join(executable("clang")).is_file()
                && directory.join(executable("llc")).is_file()
        })
}

fn executable(name: &str) -> OsString {
    if cfg!(windows) {
        format!("{name}.exe").into()
    } else {
        name.into()
    }
}

pub(super) fn run(
    program: &Path,
    arguments: impl IntoIterator<Item = OsString>,
    managed: bool,
) -> Result<String, Error> {
    let mut command = Command::new(program);
    command
        .args(arguments)
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .env_remove("LLAM_MANAGED_REQUIRED");
    if managed {
        command.env("LLAM_MANAGED_REQUIRED", "1");
    }
    let output = command
        .output()
        .map_err(|error| failure("E-LLVM-TOOL", format!("{}: {error}", program.display())))?;
    if output.stdout.len().saturating_add(output.stderr.len()) > 4 * 1024 * 1024 {
        return Err(failure(
            "E-LLVM-TOOL",
            "native tool diagnostic output exceeded 4 MiB",
        ));
    }
    if !output.status.success() {
        return Err(failure(
            "E-LLVM-TOOL",
            format!(
                "{} failed ({}):\n{}",
                program
                    .file_name()
                    .unwrap_or(OsStr::new("native tool"))
                    .to_string_lossy(),
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| failure("E-LLVM-TOOL", "native tool returned non-UTF-8 output"))
}
