use super::*;
use crate::Compilation;
use std::process::Command;

pub struct Doctor {
    pub rust: String,
    pub llvm_bin: PathBuf,
    pub target: String,
    pub sysroot: String,
    pub sdk: Option<PathBuf>,
    pub producer: Option<String>,
    pub verifier: Option<String>,
    pub effective_policy: &'static str,
    pub probed: bool,
}

/// Tool/SDK checks are read-only. The optional admission probe creates only a
/// uniquely owned scratch directory and removes it after the child has exited.
pub fn diagnose(options: &Options, root: &Path, probe: bool) -> Result<Doctor, Error> {
    let tools = Tools::discover(options)?;
    let sdk = if options.runtime == Runtime::Llam {
        Some(sdk::Sdk::load(options)?)
    } else {
        None
    };
    let effective_policy = match (options.runtime, probe) {
        (Runtime::None, _) => "runtime disabled (explicit native diagnostics mode)",
        (Runtime::Llam, false) => "not measured (--no-probe)",
        (Runtime::Llam, true) => {
            admission_probe(
                &tools,
                sdk.as_ref().expect("managed SDK"),
                options.optimization,
                root,
            )?;
            "async-required (managed admission probe passed)"
        }
    };
    let sysroot = tools
        .system_flags
        .windows(2)
        .find(|pair| pair[0] == "-isysroot")
        .map(|pair| pair[1].to_string_lossy().into_owned())
        .unwrap_or_else(|| "compiler default (native target)".into());
    let rust = Command::new("rustc")
        .arg("--version")
        .output()
        .ok()
        .filter(|result| result.status.success())
        .map(|result| String::from_utf8_lossy(&result.stdout).trim().to_owned())
        .unwrap_or_else(|| "not installed; the prebuilt compiler remains usable".into());
    Ok(Doctor {
        rust,
        llvm_bin: tools.bin,
        target: tools.target,
        sysroot,
        sdk: sdk.as_ref().map(|sdk| sdk.root.clone()),
        producer: sdk
            .as_ref()
            .and_then(|sdk| sdk.identities.get("lib/llam/llam_managed_pass.so").cloned()),
        verifier: sdk.as_ref().and_then(|sdk| {
            sdk.identities
                .get("libexec/llam/managed_verify.py")
                .cloned()
        }),
        effective_policy,
        probed: probe && options.runtime == Runtime::Llam,
    })
}

fn admission_probe(
    tools: &Tools,
    sdk: &sdk::Sdk,
    optimization: Optimization,
    root: &Path,
) -> Result<(), Error> {
    let scratch = scratch::Scratch::new(root)?;
    let mut compilation = Compilation::default();
    let file = compilation
        .sources
        .add("doctor-probe.cavo", "i32 main() { return 0; }".into())
        .map_err(|message| failure("E-DOCTOR-PROBE", message))?;
    compilation.parse(file);
    let mut program = compilation.check_executable().ok_or_else(|| {
        failure(
            "E-DOCTOR-PROBE",
            "the compiler rejected its admission probe",
        )
    })?;
    managed_frames(&mut program, &compilation.symbols)?;
    let artifact = codegen::emit(&mut program, &compilation.symbols, &tools.target)?;
    let executable = scratch.file(if cfg!(windows) { "probe.exe" } else { "probe" });
    pipeline::build(
        tools,
        Some(sdk),
        artifact,
        OutputKind::Executable,
        &executable,
        optimization,
    )?;
    let result = Command::new(executable)
        .output()
        .map_err(|error| failure("E-DOCTOR-PROBE", error.to_string()))?;
    if !result.status.success() {
        return Err(failure(
            "E-DOCTOR-PROBE",
            format!(
                "required asynchronous runtime admission failed ({}): {}",
                result.status,
                String::from_utf8_lossy(&result.stderr)
            ),
        ));
    }
    Ok(())
}
