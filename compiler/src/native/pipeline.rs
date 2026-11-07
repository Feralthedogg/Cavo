use super::*;
use std::ffi::OsString;

pub(super) fn build(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    artifact: codegen::Artifact,
    kind: OutputKind,
    output: &Path,
    optimization: Optimization,
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
    optimize(tools, sdk, &input, &optimized, optimization)?;
    let object = scratch.file("program.o");
    object_file(tools, sdk, &scratch, &optimized, &object, optimization)?;
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
    optimization: Optimization,
) -> Result<(), Error> {
    let optimized = if sdk.is_some() {
        output.with_extension("pre.ll")
    } else {
        output.into()
    };
    let args = vec![
        format!("-passes=verify,default<{}>,verify", optimization.llvm()).into(),
        "-S".into(),
        input.as_os_str().into(),
        "-o".into(),
        optimized.as_os_str().into(),
    ];
    tools.invoke("opt", args, false)?;
    if let Some(sdk) = sdk {
        // Loading the plugin only for its named pass avoids the automatic
        // OptimizerLast hook and qualifies the module exactly once at O0/O2.
        tools.invoke(
            "opt",
            vec![
                format!("-load-pass-plugin={}", sdk.plugin().display()).into(),
                // Normalize unreachable guard-leave tails produced for fatal
                // foreign calls. O0 codegen otherwise retains those tails and
                // violates the SDK's noreturn-boundary certificate shape.
                "-passes=llam-managed,simplifycfg,verify".into(),
                "-S".into(),
                optimized.into_os_string(),
                "-o".into(),
                output.as_os_str().into(),
            ],
            true,
        )?;
    }
    Ok(())
}

fn object_file(
    tools: &Tools,
    sdk: Option<&sdk::Sdk>,
    scratch: &scratch::Scratch,
    input: &Path,
    output: &Path,
    optimization: Optimization,
) -> Result<(), Error> {
    if let Some(sdk) = sdk {
        let machine = scratch.file("program.mir");
        let labelled = scratch.file("labelled.mir");
        let mut args = machine_arguments(input, &machine);
        args.extend([
            format!("-{}", optimization.llvm()).into(),
            "-stop-after=unpack-mi-bundles".into(),
        ]);
        tools.invoke("llc", args, true)?;
        let mut args = machine_arguments(&machine, &labelled);
        args.extend([
            format!("-load={}", sdk.plugin().display()).into(),
            format!("-{}", optimization.llvm()).into(),
            "-run-pass=llam-managed-machine".into(),
            "-verify-machineinstrs".into(),
        ]);
        tools.invoke("llc", args, true)?;
        let mut args = machine_arguments(&labelled, output);
        args.extend([
            "-start-after=unpack-mi-bundles".into(),
            format!("-{}", optimization.llvm()).into(),
            "-verify-machineinstrs".into(),
            "-filetype=obj".into(),
        ]);
        tools.invoke("llc", args, true)?;
    } else {
        let mut args = machine_arguments(input, output);
        args.extend([
            format!("-{}", optimization.llvm()).into(),
            "-filetype=obj".into(),
        ]);
        tools.invoke("llc", args, false)?;
    }
    Ok(())
}

fn machine_arguments(input: &Path, output: &Path) -> Vec<OsString> {
    // The SDK proves register provenance for immutable guard bindings, not
    // arbitrary spill memory. Keep its selector/allocator profile explicit
    // while retaining the selected O0/O2 IR and machine optimization levels.
    let mut arguments = [
        "--enable-new-pm=0",
        "-relocation-model=pic",
        "-fast-isel=false",
        "-global-isel=false",
        "-optimize-regalloc=true",
        "-regalloc=greedy",
    ]
    .map(OsString::from)
    .to_vec();
    arguments.extend([
        input.as_os_str().into(),
        "-o".into(),
        output.as_os_str().into(),
    ]);
    arguments
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
    let mut seal = verifier_arguments(tools, sdk, image);
    seal.push("--seal".into());
    let report = tools::run(Path::new("python3"), seal, false)?;
    managed_entry_count(&report)?;
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
    check_image(tools, sdk, image)?;
    Ok(())
}

fn verifier_arguments(tools: &Tools, sdk: &sdk::Sdk, image: &Path) -> Vec<OsString> {
    vec![
        sdk.verifier().into_os_string(),
        image.as_os_str().into(),
        "--objdump".into(),
        tools.path("llvm-objdump").into_os_string(),
    ]
}

pub(super) fn check_image(tools: &Tools, sdk: &sdk::Sdk, image: &Path) -> Result<u64, Error> {
    let report = tools::run(
        Path::new("python3"),
        verifier_arguments(tools, sdk, image),
        false,
    )
    .map_err(|error| failure("E-LLAM-VERIFY", error.message))?;
    managed_entry_count(&report)
}

fn managed_entry_count(report: &str) -> Result<u64, Error> {
    let crate::external::json::Json::Object(report) =
        crate::external::json::parse_bounded(report, 1024 * 1024, 128)
            .map_err(|error| failure("E-LLAM-VERIFY", error))?
    else {
        return Err(failure(
            "E-LLAM-VERIFY",
            "invalid final-image verification report",
        ));
    };
    let count = report
        .get("managed_entries")
        .and_then(|count| match count {
            crate::external::json::Json::Number(count) => Some(*count),
            _ => None,
        })
        .filter(|&count| count > 0);
    count.ok_or_else(|| {
        failure(
            "E-LLAM-VERIFY",
            "the final image contains no admitted managed entries",
        )
    })
}
