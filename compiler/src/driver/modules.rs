use crate::{Compilation, modular::capsule::Module, packages::Graph};
use std::{
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

pub(super) fn load(
    compilation: &mut Compilation,
    paths: &[PathBuf],
    error: &mut dyn Write,
) -> io::Result<bool> {
    for path in paths {
        let result = read(path)
            .and_then(|text| Module::decode(&text))
            .and_then(|module| module.load_into(compilation));
        if let Err(message) = result {
            writeln!(error, "cavoite: {}: {message}", path.display())?;
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn load_package(
    compilation: &mut Compilation,
    graph: &Graph,
    error: &mut dyn Write,
) -> io::Result<Option<usize>> {
    let sources = match graph.sources() {
        Ok(sources) => sources,
        Err(message) => {
            writeln!(error, "cavoite: {message}")?;
            return Ok(None);
        }
    };
    let count = sources.len();
    for source in sources {
        let id = compilation
            .sources
            .add(&source.name, source.text)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        compilation.parse(id);
    }
    Ok(Some(count))
}

pub(super) fn emit(
    compilation: &mut Compilation,
    output: &mut dyn Write,
    error: &mut dyn Write,
) -> io::Result<u8> {
    match crate::modular::capsule::export(compilation) {
        Ok(module) => {
            output.write_all(module.encode().as_bytes())?;
            Ok(0)
        }
        Err(message) => {
            writeln!(error, "cavoite: {message}")?;
            Ok(1)
        }
    }
}

fn read(path: &Path) -> Result<String, String> {
    let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
    let mut text = String::new();
    file.take(16 * 1024 * 1024 + 1)
        .read_to_string(&mut text)
        .map_err(|e| e.to_string())?;
    if text.len() > 16 * 1024 * 1024 {
        return Err("module capsule exceeds 16 MiB".into());
    }
    Ok(text)
}
