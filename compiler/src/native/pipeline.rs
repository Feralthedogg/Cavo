use super::*;
use std::ffi::OsString;

pub(super) fn build(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    artifact: codegen::Artifact,
    kind: OutputKind,
    output: &Path,
) -> Result<(), Error> {
    if std::fs::symlink_metadata(output)
        .is_ok_and(|metadata| !metadata.is_file() || metadata.file_type().is_symlink())
    {
        return Err(failure(
            "E-NATIVE-OUTPUT",
            "native output must be an ordinary file, not a symlink or directory",
        ));
    }
    let parent = output
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let parent = parent
        .canonicalize()
        .map_err(|error| failure("E-NATIVE-OUTPUT", error.to_string()))?;
    let name = output
        .file_name()
        .ok_or_else(|| failure("E-NATIVE-OUTPUT", "native output needs a file name"))?;
    let output = parent.join(name);
    let scratch = scratch::Scratch::new(&parent)?;
    let input = scratch.write("program.ll", &artifact.llvm_ir)?;
    let optimized = scratch.file("optimized.ll");
    optimize(tools, sdk, &input, &optimized)?;
    let object = scratch.file("program.o");
    object_file(tools, sdk, &scratch, &optimized, &object)?;
    let result = if kind == OutputKind::Object {
        object
    } else {
        let result = scratch.file(if cfg!(windows) {
            "program.exe"
        } else {
            "program"
        });
        link(tools, sdk, &scratch, &object, &result)?;
        if let Some(sdk) = sdk {
            verify(tools, sdk, &result)?;
        }
        result
    };
    std::fs::rename(&result, &output).map_err(|error| {
        failure(
            "E-NATIVE-OUTPUT",
            format!(
                "{}: {error}; previous output was preserved",
                output.display()
            ),
        )
    })
}

fn optimize(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    input: &Path,
    output: &Path,
) -> Result<(), Error> {
    let mut args = Vec::new();
    if let Some(sdk) = sdk {
        args.push(format!("-load-pass-plugin={}", sdk.plugin().display()).into());
    }
    // The plugin installs itself at OptimizerLast. Adding its named pass too
    // would lower an already-qualified module twice and invalidate its ABI.
    args.extend(["-passes=default<O2>,verify", "-S"].map(OsString::from));
    args.extend([
        input.as_os_str().into(),
        "-o".into(),
        output.as_os_str().into(),
    ]);
    tools.invoke("opt", args, sdk.is_some())?;
    Ok(())
}

fn object_file(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    scratch: &scratch::Scratch,
    input: &Path,
    output: &Path,
) -> Result<(), Error> {
    let common = ["--enable-new-pm=0", "-relocation-model=pic"];
    if let Some(sdk) = sdk {
        let machine = scratch.file("program.mir");
        let labelled = scratch.file("labelled.mir");
        let mut args = common.map(OsString::from).to_vec();
        args.extend([
            "-O2".into(),
            "-stop-after=unpack-mi-bundles".into(),
            input.as_os_str().into(),
            "-o".into(),
            machine.as_os_str().into(),
        ]);
        tools.invoke("llc", args, true)?;
        let mut args = common.map(OsString::from).to_vec();
        args.extend([
            format!("-load={}", sdk.plugin().display()).into(),
            "-run-pass=llam-managed-machine".into(),
            "-verify-machineinstrs".into(),
            machine.into_os_string(),
            "-o".into(),
            labelled.as_os_str().into(),
        ]);
        tools.invoke("llc", args, true)?;
        let mut args = common.map(OsString::from).to_vec();
        args.extend([
            "-start-after=unpack-mi-bundles".into(),
            "-verify-machineinstrs".into(),
            "-filetype=obj".into(),
            labelled.into_os_string(),
            "-o".into(),
            output.as_os_str().into(),
        ]);
        tools.invoke("llc", args, true)?;
    } else {
        let mut args = common.map(OsString::from).to_vec();
        args.extend([
            "-O2".into(),
            "-filetype=obj".into(),
            input.as_os_str().into(),
            "-o".into(),
            output.as_os_str().into(),
        ]);
        tools.invoke("llc", args, false)?;
    }
    Ok(())
}

fn link(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    scratch: &scratch::Scratch,
    object: &Path,
    output: &Path,
) -> Result<(), Error> {
    scratch.write("cavo.h", include_str!("../../runtime/cavo.h"))?;
    let support = scratch.write("support.c", include_str!("../../runtime/support.c"))?;
    let host = scratch.write("host.c", include_str!("../../runtime/host.c"))?;
    let mut args = vec![
        "-std=c11".into(),
        "-O2".into(),
        "-Wall".into(),
        "-Wextra".into(),
        "-Werror".into(),
        "-fno-crash-diagnostics".into(),
    ];
    args.extend(tools.system_flags.iter().cloned());
    if let Some(sdk) = sdk {
        args.extend([
            "-DCAVO_WITH_LLAM".into(),
            "-I".into(),
            sdk.root.join("include").into_os_string(),
        ]);
    }
    args.extend([
        support.into_os_string(),
        host.into_os_string(),
        object.as_os_str().into(),
    ]);
    if let Some(sdk) = sdk {
        args.push(sdk.library().into_os_string());
        args.extend(platform_link_flags(&tools.target));
    }
    args.extend(["-o".into(), output.as_os_str().into()]);
    tools.invoke("clang", args, false)?;
    Ok(())
}

fn platform_link_flags(target: &str) -> Vec<OsString> {
    if target.contains("apple") {
        vec!["-pthread".into(), "-Wl,-export_dynamic".into()]
    } else if target.contains("linux") {
        [
            "-pthread",
            "-luring",
            "-ldl",
            "-Wl,--build-id=uuid",
            "-Wl,-z,separate-code,-z,relro,-z,now",
            "-Wl,--export-dynamic-symbol=__llam_managed_anchor_*",
        ]
        .map(OsString::from)
        .to_vec()
    } else {
        vec!["-Wl,--build-id".into()]
    }
}

fn verify(tools: &Tools, sdk: &sdk::Sdk, image: &Path) -> Result<(), Error> {
    let args = vec![
        sdk.verifier().into_os_string(),
        image.as_os_str().into(),
        "--objdump".into(),
        tools.path("llvm-objdump").into_os_string(),
    ];
    let mut seal = args.clone();
    seal.push("--seal".into());
    let report = tools::run(Path::new("python3"), seal, false)?;
    let crate::external::json::Json::Object(report) =
        crate::external::json::parse_bounded(&report, 1024 * 1024, 128)
            .map_err(|error| failure("E-LLAM-VERIFY", error))?
    else {
        return Err(failure(
            "E-LLAM-VERIFY",
            "invalid final-image verification report",
        ));
    };
    if !matches!(report.get("managed_entries"),Some(crate::external::json::Json::Number(count)) if *count>0)
    {
        return Err(failure(
            "E-LLAM-VERIFY",
            "the final image contains no admitted managed entries",
        ));
    }
    if tools.target.contains("apple") {
        tools::run(
            Path::new("/usr/bin/codesign"),
            [
                "--force".into(),
                "--sign".into(),
                "-".into(),
                image.as_os_str().into(),
            ],
            false,
        )?;
    }
    tools::run(Path::new("python3"), args, false)?;
    Ok(())
}
