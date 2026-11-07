//! Deterministic front-end modules. A capsule carries a recheckable source
//! witness and a separate interface hash. It is not a native object or a trust bit.
use crate::contracts::Trust;
use crate::{
    Compilation,
    external::{
        Digest,
        digest::sha256,
        json::{self, Json},
    },
    hir,
    source::FileId,
    syntax::{
        ast::{GenericParam, ItemKind, Visibility},
        lexer,
    },
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
    path::{Component, Path},
};

const MAX_BYTES: usize = 16 * 1024 * 1024;
const SCHEMA: u64 = 1;
const TARGET: &str = "cavo-portable-mir-lp64";

#[derive(Clone, Debug)]
pub struct Source {
    pub name: String,
    pub text: String,
}

#[derive(Debug)]
pub struct Module {
    interface: Digest,
    implementation: Digest,
    sources: Vec<Source>,
    headers: Vec<Header>,
    trust: BTreeSet<Trust>,
}

#[derive(Clone, Debug)]
pub(crate) struct VerifiedImport {
    pub certified_offsets: BTreeSet<u32>,
    pub identity: Digest,
    pub assumptions: BTreeSet<Trust>,
}

#[derive(Debug)]
struct Header {
    source: Source,
    certified_offsets: BTreeSet<u32>,
}

pub fn build(sources: Vec<Source>) -> Result<Module, String> {
    validate_sources(&sources)?;
    let mut compilation = parse_sources(&sources)?;
    let (mut hir, mir) = compilation
        .check_mir()
        .ok_or_else(|| errors(&compilation))?;
    let frames = crate::tasks::independent_frames(
        &mir,
        &mut hir,
        &compilation.symbols,
        &compilation
            .mir_analysis
            .as_ref()
            .expect("checked MIR analysis")
            .effects
            .functions,
    )?;
    let headers = headers(&compilation, &hir, &frames.established)?;
    let mut trust: BTreeSet<_> = compilation
        .mir_analysis
        .as_ref()
        .expect("checked MIR analysis")
        .contracts
        .dependencies
        .values()
        .flatten()
        .cloned()
        .collect();
    for definition in frames.assumptions {
        let span = hir.definitions[definition].span;
        trust.insert(Trust::TrustedImpl {
            file: span.file.0,
            start: span.start,
            reason: hir.tasks.trusted[&definition].clone(),
        });
    }
    Ok(Module {
        interface: fingerprint(headers.iter().map(|header| &header.source), true)?,
        implementation: fingerprint(&sources, false)?,
        sources,
        headers,
        trust,
    })
}

impl Module {
    pub fn interface(&self) -> Digest {
        self.interface
    }
    pub fn implementation(&self) -> Digest {
        self.implementation
    }
    pub fn sources(&self) -> &[Source] {
        &self.sources
    }
    pub fn encode(&self) -> String {
        let mut output = format!(
            "{{\"format\":\"cavo-module\",\"schema\":{SCHEMA},\"compiler\":{},\"target\":{},\"interface\":{},\"implementation\":{},\"sources\":[",
            json::quote(env!("CARGO_PKG_VERSION")),
            json::quote(TARGET),
            json::quote(&self.interface.to_string()),
            json::quote(&self.implementation.to_string())
        );
        for (index, source) in self.sources.iter().enumerate() {
            if index > 0 {
                output.push(',');
            }
            let _ = write!(
                output,
                "{{\"name\":{},\"text\":{}}}",
                json::quote(&source.name),
                json::quote(&source.text)
            );
        }
        output.push_str("]}\n");
        output
    }

    pub fn decode(text: &str) -> Result<Self, String> {
        let Json::Object(mut object) = json::parse_bounded(text, MAX_BYTES, 8192)? else {
            return Err("module capsule must be an object".into());
        };
        if take_string(&mut object, "format")? != "cavo-module"
            || !matches!(object.remove("schema"), Some(Json::Number(SCHEMA)))
            || take_string(&mut object, "compiler")? != env!("CARGO_PKG_VERSION")
            || take_string(&mut object, "target")? != TARGET
        {
            return Err("incompatible module format, compiler or target".into());
        }
        let interface = take_string(&mut object, "interface")?;
        let implementation = take_string(&mut object, "implementation")?;
        let sources = decode_sources(object.remove("sources"))?;
        if !object.is_empty() {
            return Err("unknown module capsule member".into());
        }
        let module = build(sources)?;
        if module.interface.to_string() != interface
            || module.implementation.to_string() != implementation
        {
            return Err("module capsule content or interface fingerprint mismatch".into());
        }
        Ok(module)
    }

    pub fn load_into(&self, compilation: &mut Compilation) -> Result<(), String> {
        let assumptions = self.imported_assumptions();
        for header in &self.headers {
            let id = compilation
                .sources
                .add(&header.source.name, header.source.text.clone())
                .map_err(str::to_owned)?;
            compilation.verified_modules.insert(
                id,
                VerifiedImport {
                    certified_offsets: header.certified_offsets.clone(),
                    identity: self.implementation,
                    assumptions: assumptions.clone(),
                },
            );
            compilation.parse(id);
        }
        if !compilation.diagnostics.is_empty() {
            return Err(errors(compilation));
        }
        Ok(())
    }

    fn imported_assumptions(&self) -> BTreeSet<Trust> {
        self.trust
            .iter()
            .map(|trust| match trust {
                Trust::Source {
                    file,
                    start,
                    reason,
                }
                | Trust::TrustedImpl {
                    file,
                    start,
                    reason,
                } => Trust::Module {
                    digest: self.implementation,
                    source: self
                        .sources
                        .get(*file as usize)
                        .map_or("<module>".into(), |source| source.name.as_str().into()),
                    start: *start,
                    reason: reason.clone(),
                },
                other => other.clone(),
            })
            .collect()
    }
}

pub fn export(compilation: &mut Compilation) -> Result<Module, String> {
    let files: BTreeSet<_> = compilation
        .ast
        .modules
        .iter()
        .map(|module| module.file)
        .collect();
    if !compilation.verified_modules.is_empty() {
        return Err(
            "export the package source graph rather than flattening imported headers".into(),
        );
    }
    let mut sources = Vec::new();
    for file in files {
        let source = compilation.sources.file(file);
        let path = if source.path.is_absolute() {
            source
                .path
                .file_name()
                .map(Path::new)
                .ok_or("module source has no file name")?
        } else {
            &source.path
        };
        let name = path
            .to_str()
            .ok_or("module source requires a UTF-8 file name")?;
        sources.push(Source {
            name: name.into(),
            text: source.text().into(),
        });
    }
    sources.sort_by(|a, b| a.name.cmp(&b.name));
    build(sources)
}

fn parse_sources(sources: &[Source]) -> Result<Compilation, String> {
    let mut compilation = Compilation::default();
    for source in sources {
        let file = compilation
            .sources
            .add(&source.name, source.text.clone())
            .map_err(str::to_owned)?;
        compilation.parse(file);
    }
    if !compilation.diagnostics.is_empty() {
        return Err(errors(&compilation));
    }
    Ok(compilation)
}

fn validate_sources(sources: &[Source]) -> Result<(), String> {
    if sources.is_empty() || sources.len() > 1024 {
        return Err("module source count must be 1..1024".into());
    }
    let mut names = BTreeSet::new();
    let mut bytes = 0usize;
    for source in sources {
        bytes = bytes
            .checked_add(source.text.len().saturating_add(source.name.len()))
            .ok_or("module byte count overflow")?;
        let path = Path::new(&source.name);
        if source.name.is_empty()
            || source.name.len() > 4096
            || path.components().count() > 64
            || path
                .components()
                .any(|c| !matches!(c, Component::Normal(_)))
            || source.name.contains('\\')
            || !names.insert(&source.name)
            || bytes > MAX_BYTES / 2
        {
            return Err(
                "module sources must have unique relative names and fit the source byte budget"
                    .into(),
            );
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct RemovedBody {
    span: crate::source::Span,
    name: u32,
}

fn headers(
    compilation: &Compilation,
    hir: &hir::Program,
    frames: &BTreeSet<hir::DefId>,
) -> Result<Vec<Header>, String> {
    let removals = header_removals(compilation, hir, frames)?;
    compilation
        .sources
        .files()
        .iter()
        .map(|source| {
            render_header(
                source,
                removals.get(&source.id).map(Vec::as_slice).unwrap_or(&[]),
            )
        })
        .collect()
}

fn header_removals(
    compilation: &Compilation,
    hir: &hir::Program,
    frames: &BTreeSet<hir::DefId>,
) -> Result<BTreeMap<FileId, Vec<RemovedBody>>, String> {
    let methods: BTreeSet<_> = compilation
        .ast
        .items
        .iter()
        .filter_map(|item| match &item.kind {
            ItemKind::Trait { methods, .. } => Some(methods.as_slice()),
            _ => None,
        })
        .flatten()
        .map(|id| id.0)
        .collect();
    let public: std::collections::HashMap<_, _> = hir
        .definitions
        .iter()
        .enumerate()
        .filter(|(_, definition)| {
            definition.kind == hir::DefinitionKind::Function
                && definition.visibility == Visibility::Public
                && definition
                    .generic_parameter_kinds
                    .iter()
                    .all(|kind| *kind == crate::types::GenericParamKind::Lifetime)
        })
        .map(|(index, definition)| (definition.span, hir::DefId(index as u32)))
        .collect();
    let analysis = compilation
        .mir_analysis
        .as_ref()
        .ok_or("module export requires MIR analysis")?;
    let complete: BTreeSet<_> = analysis
        .borrows
        .summaries
        .iter()
        .filter(|summary| summary.complete && !summary.limited)
        .map(|summary| summary.definition)
        .collect();
    let mut removals: BTreeMap<FileId, Vec<RemovedBody>> = BTreeMap::new();
    for (index, item) in compilation.ast.items.iter().enumerate() {
        let Some((definition, removed)) = header_candidate(index, item, &public, &methods) else {
            continue;
        };
        // Keep a body whose worker-frame properties depend on the eventual
        // task context. Importing it must repeat those checks in the caller.
        if !frames.contains(&definition) {
            continue;
        }
        let span = crate::source::Span {
            start: removed.name,
            end: removed.name,
            ..removed.span
        };
        if let Some(problem) =
            export_contract_failure(hir, definition, complete.contains(&definition), span)
        {
            return Err(problem.render(&compilation.sources));
        }
        removals.entry(removed.span.file).or_default().push(removed);
    }
    Ok(removals)
}

fn export_contract_failure(
    hir: &hir::Program,
    definition: hir::DefId,
    complete: bool,
    span: crate::source::Span,
) -> Option<crate::diagnostic::Diagnostic> {
    use crate::diagnostic::Diagnostic;
    if !complete {
        return Some(Diagnostic::error("E-MODULE-COVERAGE",
            "cannot export an interface with incomplete ownership or region coverage", span)
            .note("the implementation must establish its signature guarantees before its body can be hidden"));
    }
    if hir
        .modular
        .functions
        .get(&definition)
        .is_none_or(|contract| !contract.explicit)
    {
        return Some(
            Diagnostic::error(
                "E-MODULE-CONTRACT",
                "hiding a public implementation requires an explicit effect contract",
                span,
            )
            .help("declare @effects(...) with the effect and memory bounds callers may rely on"),
        );
    }
    None
}

fn header_candidate(
    index: usize,
    item: &crate::syntax::ast::Item,
    public: &std::collections::HashMap<crate::source::Span, hir::DefId>,
    methods: &BTreeSet<u32>,
) -> Option<(hir::DefId, RemovedBody)> {
    let ItemKind::Function(function) = &item.kind else {
        return None;
    };
    let (Some(name), Some(body)) = (item.name, &function.body) else {
        return None;
    };
    let &definition = public.get(&name.span)?;
    if function.constant
        || function
            .generics
            .iter()
            .any(|g| !matches!(g, GenericParam::Lifetime(_)))
        || methods.contains(&(index as u32))
    {
        return None;
    }
    Some((
        definition,
        RemovedBody {
            span: body.span,
            name: name.span.start,
        },
    ))
}

fn render_header(
    source: &crate::source::SourceFile,
    removals: &[RemovedBody],
) -> Result<Header, String> {
    let mut removals = removals.to_vec();
    removals.sort_by_key(|body| body.span.start);
    let mut removed = 0;
    let mut certified_offsets = BTreeSet::new();
    for body in &removals {
        certified_offsets.insert(body.name - removed);
        removed += body.span.end - body.span.start - 1;
    }
    let mut text = source.text().to_owned();
    for body in removals.iter().rev() {
        text.replace_range(body.span.start as usize..body.span.end as usize, ";");
    }
    let name = source
        .path
        .to_str()
        .ok_or("module path is not UTF-8")?
        .to_owned();
    Ok(Header {
        source: Source { name, text },
        certified_offsets,
    })
}

fn fingerprint<'a>(
    sources: impl IntoIterator<Item = &'a Source>,
    tokens: bool,
) -> Result<Digest, String> {
    let mut bytes = Vec::new();
    for source in sources {
        bytes.extend_from_slice(&(source.name.len() as u64).to_le_bytes());
        bytes.extend_from_slice(source.name.as_bytes());
        let text = if tokens {
            normalized(&source.text)?
        } else {
            source.text.clone()
        };
        bytes.extend_from_slice(&(text.len() as u64).to_le_bytes());
        bytes.extend_from_slice(text.as_bytes());
    }
    Ok(sha256(&bytes))
}

fn normalized(text: &str) -> Result<String, String> {
    let mut compilation = Compilation::default();
    let id = compilation
        .sources
        .add("interface", text.into())
        .map_err(str::to_owned)?;
    let source = compilation.sources.file(id);
    let tokens = lexer::lex(
        source,
        &mut compilation.symbols,
        &mut compilation.diagnostics,
    );
    if !compilation.diagnostics.is_empty() {
        return Err(errors(&compilation));
    }
    let mut output = String::new();
    for token in tokens {
        output.push_str(source.slice(token.span));
        output.push('\0');
    }
    Ok(output)
}

fn decode_sources(value: Option<Json>) -> Result<Vec<Source>, String> {
    let Some(Json::Array(values)) = value else {
        return Err("module sources must be an array".into());
    };
    values
        .into_iter()
        .map(|value| {
            let Json::Object(mut value) = value else {
                return Err("module source must be an object".into());
            };
            let name = take_string(&mut value, "name")?;
            let text = take_string(&mut value, "text")?;
            if !value.is_empty() {
                return Err("unknown module source member".into());
            }
            Ok(Source { name, text })
        })
        .collect()
}

fn take_string(object: &mut BTreeMap<String, Json>, name: &str) -> Result<String, String> {
    match object.remove(name) {
        Some(Json::String(value)) => Ok(value),
        _ => Err(format!("module member `{name}` must be a string")),
    }
}

fn errors(compilation: &Compilation) -> String {
    compilation
        .diagnostics
        .iter()
        .map(|d| d.render(&compilation.sources))
        .collect::<Vec<_>>()
        .join("\n")
}
