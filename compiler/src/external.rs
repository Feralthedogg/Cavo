//! Versioned external assumptions. Loading a document never grants it trust.
pub mod digest;
pub mod interface;
pub(crate) mod json;
mod memory;

use crate::{
    diagnostic::{Diagnostic, report},
    hir,
    local::{RegionContract, RegionStep},
    source::{SourceMap, Span},
    symbol::Interner,
    types::{Ty, TyId},
};
pub use digest::Digest;
use json::Json;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssumptionId(pub u32);
#[derive(Clone, Debug)]
pub struct Effects {
    pub no_retain: Option<bool>,
    pub no_free: Option<bool>,
    pub no_callback: Option<bool>,
    pub no_unwind: Option<bool>,
    pub no_suspend: Option<bool>,
    pub no_block: Option<bool>,
    pub no_allocate: Option<bool>,
    pub preserves_validity: Option<bool>,
    pub reads: Option<Vec<u32>>,
    pub writes: Option<Vec<u32>>,
    pub stores: Option<Vec<ReferenceStore>>,
}
#[derive(Clone, Debug)]
pub struct ReferenceStore {
    pub target: String,
    pub sources: Vec<String>,
    pub definite: bool,
}
#[derive(Debug)]
struct FunctionSummary {
    name: String,
    abi: String,
    signature: Digest,
    effects: Effects,
    returns: Vec<String>,
}
#[derive(Debug)]
struct Summary {
    schema: u8,
    id: String,
    version: String,
    artifact: Digest,
    digest: Digest,
    functions: Vec<FunctionSummary>,
    span: Span,
}
#[derive(Debug, Default)]
pub struct Summaries {
    documents: Vec<Summary>,
    trusted: BTreeSet<Digest>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SummaryStatus {
    Untrusted,
    Unsupported,
    Assumed,
}
#[derive(Clone, Debug)]
pub struct SummaryReport {
    pub schema: u8,
    pub assumption: AssumptionId,
    pub id: String,
    pub version: String,
    pub digest: Digest,
    /// Declared by the author. This frontend does not measure a native artifact.
    pub declared_artifact: Digest,
    pub function: hir::DefId,
    pub signature: Digest,
    pub source: Span,
    pub effects: Effects,
    /// Validated return-origin syntax retained for downstream MIR adaptation.
    pub returns: Vec<String>,
    pub status: SummaryStatus,
    pub not_established: Vec<String>,
}
#[derive(Debug)]
pub(crate) struct Binding {
    pub assumption: AssumptionId,
    pub returns: Vec<usize>,
    pub static_result: bool,
    pub memory: Option<crate::local::MemorySummary>,
}
#[derive(Debug, Default)]
pub(crate) struct Bindings {
    pub functions: Vec<Option<Binding>>,
    pub reports: Vec<SummaryReport>,
}

impl Summaries {
    pub fn add(
        &mut self,
        path: impl AsRef<Path>,
        text: String,
        sources: &mut SourceMap,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Option<Digest> {
        if self.documents.len() >= 64 || text.len() > 262_144 {
            if let Ok(file) = sources.add(path, String::new()) {
                report(
                    diagnostics,
                    Diagnostic::error(
                        "E-SUMMARY-SCHEMA",
                        "external summaries exceed the 64-document or 256 KiB document limit",
                        Span::new(file, 0, 0),
                    ),
                );
            }
            return None;
        }
        let digest = digest::sha256(text.as_bytes());
        let file = match sources.add(path, text) {
            Ok(file) => file,
            Err(_) => return None,
        };
        let span = Span::new(file, 0, 0);
        match decode(sources.file(file).text(), span, digest) {
            Ok(summary) => {
                self.documents.push(summary);
                Some(digest)
            }
            Err(message) => {
                report(
                    diagnostics,
                    Diagnostic::error("E-SUMMARY-SCHEMA", message, span),
                );
                None
            }
        }
    }
    pub fn trust(&mut self, digest: Digest) {
        self.trusted.insert(digest);
    }
    pub fn digest(text: &str) -> Digest {
        digest::sha256(text.as_bytes())
    }

    pub(crate) fn bind(
        &self,
        program: &hir::Program,
        symbols: &Interner,
        sources: &SourceMap,
        diagnostics: &mut Vec<Diagnostic>,
    ) -> Bindings {
        let mut result = Bindings {
            functions: (0..program.definitions.len()).map(|_| None).collect(),
            reports: Vec::new(),
        };
        let mut seen = HashSet::new();
        let internal = program.internal_definitions();
        let names: HashMap<_, _> = program
            .definitions
            .iter()
            .enumerate()
            .filter(|(index, d)| {
                d.kind == hir::DefinitionKind::Function
                    && !internal.contains(&hir::DefId(*index as u32))
            })
            .map(|(i, _)| {
                let id = hir::DefId(i as u32);
                (interface::qualified(program, symbols, id), id)
            })
            .collect();
        for summary in &self.documents {
            for function in &summary.functions {
                let Some(&id) = names.get(&function.name) else {
                    report(
                        diagnostics,
                        Diagnostic::error(
                            "E-SUMMARY-BIND",
                            format!("summary names unknown function `{}`", function.name),
                            summary.span,
                        ),
                    );
                    continue;
                };
                let def = &program.definitions[id];
                let expected = interface::fingerprint(program, symbols, sources, id);
                if program.functions.iter().any(|f| f.definition == id)
                    || !seen.insert(id)
                    || interface::abi(def) != function.abi
                    || expected != Some(function.signature)
                {
                    let mut d = Diagnostic::error(
                        "E-SUMMARY-BIND",
                        "external summary does not match a unique declaration without a body",
                        summary.span,
                    )
                    .label(def.span, "declaration being matched");
                    if let Some(expected) = expected {
                        d = d.note(format!(
                            "expected ABI `{}` and signature {expected}",
                            interface::abi(def)
                        ));
                    }
                    report(diagnostics, d);
                    continue;
                }
                let assumption = AssumptionId(result.reports.len() as u32);
                let trusted = self.trusted.contains(&summary.digest);
                result.reports.push(SummaryReport {
                    schema: summary.schema,
                    assumption,
                    id: summary.id.clone(),
                    version: summary.version.clone(),
                    digest: summary.digest,
                    declared_artifact: summary.artifact,
                    function: id,
                    signature: function.signature,
                    source: summary.span,
                    effects: function.effects.clone(),
                    returns: function.returns.clone(),
                    status: if trusted {
                        SummaryStatus::Unsupported
                    } else {
                        SummaryStatus::Untrusted
                    },
                    not_established: Vec::new(),
                });
                if trusted {
                    result.functions[id.0 as usize] = Some(Binding {
                        assumption,
                        returns: Vec::new(),
                        static_result: false,
                        memory: None,
                    });
                }
            }
        }
        result
    }
}

impl Bindings {
    pub(crate) fn apply(
        &mut self,
        contracts: &mut [Option<RegionContract>],
        program: &hir::Program,
        diagnostics: &mut Vec<Diagnostic>,
        summaries: &Summaries,
    ) {
        for record in &mut self.reports {
            let id = record.function;
            let Some(binding) = &mut self.functions[id.0 as usize] else {
                continue;
            };
            let document = summaries
                .documents
                .iter()
                .find(|s| s.digest == record.digest)
                .expect("bound document");
            // The identity match was already checked at binding. Resolve by the
            // unique signature, which includes the qualified function name.
            let summary = document
                .functions
                .iter()
                .find(|f| f.signature == record.signature)
                .expect("bound function");
            let contract = contracts[id.0 as usize]
                .as_mut()
                .expect("function region contract");
            let Ty::Function { parameters, result } = program.types.get(program.definitions[id].ty)
            else {
                continue;
            };
            let effects = &record.effects;
            for (name, value) in [
                ("no_retain", effects.no_retain),
                ("no_free", effects.no_free),
                ("no_callback", effects.no_callback),
                ("no_unwind", effects.no_unwind),
                ("no_suspend", effects.no_suspend),
                ("no_block", effects.no_block),
                ("no_allocate", effects.no_allocate),
                ("preserves_validity", effects.preserves_validity),
            ] {
                match value {
                    None => record
                        .not_established
                        .push(format!("`{name}` was not specified")),
                    Some(false) => record
                        .not_established
                        .push(format!("`{name}` is not guaranteed by this summary")),
                    Some(true) => {}
                }
            }
            if effects.reads.is_none() {
                record
                    .not_established
                    .push("memory read effects are unknown".into());
            }
            if effects.writes.is_none() {
                record
                    .not_established
                    .push("memory write effects are unknown".into());
            }
            if effects.stores.is_none() {
                record
                    .not_established
                    .push("reference-store effects are unknown".into());
            }
            if !program.definitions[id].declaration_clauses.is_empty() {
                record.not_established.push(
                    "declared requires/ensures clauses need a conditional effect proof".into(),
                );
            }
            let mut valid = contract.valid && record.not_established.is_empty();
            valid &= program.definitions[id]
                .generic_parameter_kinds
                .iter()
                .all(|kind| *kind == crate::types::GenericParamKind::Lifetime);
            valid &= effects.reads.is_some() && effects.writes.is_some();
            for &index in effects.reads.iter().chain(&effects.writes).flatten() {
                valid &= parameters
                    .get(index as usize)
                    .is_some_and(|&ty| matches!(program.types.get(ty), Ty::Reference { .. }));
            }
            for &index in effects.writes.iter().flatten() {
                valid &= parameters.get(index as usize).is_some_and(|&ty|matches!(program.types.get(ty),Ty::Reference{mutable:true,inner,..} if scalar_memory(program,*inner) || record.schema==2 && effects.stores.is_some()));
            }
            // Callback ABI, opaque generic validity and borrowed-value writes
            // need their own effect model; a sidecar cannot bypass that gap.
            valid &= parameters.iter().all(|&ty| supported_type(program, ty))
                && supported_type(program, *result);
            binding.returns.clear();
            for path in &summary.returns {
                if path == "static" {
                    valid &= contract.reference_result
                        && contract.inputs.is_empty()
                        && !matches!(
                            program.types.get(*result),
                            Ty::Reference { mutable: true, .. }
                        );
                    binding.static_result = true;
                    continue;
                }
                let Some((parameter, path)) = input_path(path) else {
                    valid = false;
                    continue;
                };
                let Some(index) = contract
                    .inputs
                    .iter()
                    .position(|i| i.parameter == parameter && i.path == path && i.region.is_some())
                else {
                    valid = false;
                    continue;
                };
                valid &= contract.reference_result && contract.return_inputs.contains(&index);
                let input = &contract.inputs[index];
                valid &= input
                    .pointee
                    .zip(contract.result_pointee)
                    .is_some_and(|(a, b)| program.types.compatible(a, b));
                let mutable = matches!(
                    program.types.get(*result),
                    Ty::Reference { mutable: true, .. }
                );
                if mutable {
                    valid &= input
                        .pointee
                        .zip(contract.result_pointee)
                        .is_some_and(|(a, b)| program.types.region_invariant(a, b));
                }
                valid &= !mutable
                    || path_type(program, parameters[parameter as usize], &path).is_some_and(
                        |ty| matches!(program.types.get(ty), Ty::Reference { mutable: true, .. }),
                    );
                if path.contains(&RegionStep::Deref) {
                    valid &= effects
                        .reads
                        .as_ref()
                        .is_some_and(|reads| reads.contains(&parameter));
                }
                if mutable {
                    let mut current = parameters[parameter as usize];
                    for (position, step) in path.iter().enumerate() {
                        if *step == RegionStep::Deref {
                            valid &= matches!(
                                program.types.get(current),
                                Ty::Reference { mutable: true, .. }
                            );
                        }
                        if let Some(next) =
                            path_type(program, parameters[parameter as usize], &path[..=position])
                        {
                            current = next;
                        } else {
                            valid = false;
                            break;
                        }
                    }
                }
                binding.returns.push(index);
            }
            binding.returns.sort_unstable();
            binding.returns.dedup();
            valid &=
                !contract.reference_result || !binding.returns.is_empty() || binding.static_result;
            valid &= contract.reference_result
                || summary.returns.is_empty() && !contains_references(program, *result);
            binding.memory = memory::build(
                program,
                contract,
                parameters,
                *result,
                &record.effects,
                binding,
            );
            valid &= binding.memory.is_some();
            if valid {
                contract.return_inputs = binding.returns.clone();
                contract.static_result = binding.static_result;
                record.status = SummaryStatus::Assumed;
            } else {
                self.functions[id.0 as usize] = None;
                if record.not_established.is_empty() {
                    record.not_established.push("memory access, signature validity, or return paths require an unsupported contract".into());
                }
                let mut diagnostic=Diagnostic::error("E-SUMMARY-EFFECT","external summary contains an unknown or unsupported effect or return contract",record.source)
                    .label(program.definitions[id].span,"no external safety result was approved for this declaration")
                    .note("this stage models no-retain/no-free/no-callback calls, read access, scalar writes preserving validity, and input-tied reference returns");
                diagnostic
                    .notes
                    .extend(record.not_established.iter().cloned());
                report(diagnostics, diagnostic);
            }
        }
    }

    /// Conservative dependency closure includes function values as well as
    /// calls. Violations retain the same assumptions as successful checks.
    pub(crate) fn dependencies(&self, program: &hir::Program) -> Option<Vec<Vec<AssumptionId>>> {
        let mut supports: Vec<BTreeSet<_>> = self
            .functions
            .iter()
            .map(|b| {
                b.as_ref()
                    .map(|b| BTreeSet::from([b.assumption]))
                    .unwrap_or_default()
            })
            .collect();
        let mut edges = vec![Vec::new(); program.definitions.len()];
        for function in &program.functions {
            edges[function.definition.0 as usize] = function
                .expressions
                .iter()
                .filter_map(|e| {
                    if let hir::ExprKind::Definition(id) = e.kind {
                        Some(id.0 as usize)
                    } else {
                        None
                    }
                })
                .collect();
            edges[function.definition.0 as usize].sort_unstable();
            edges[function.definition.0 as usize].dedup();
        }
        for component in crate::graph::components(&edges) {
            let mut joined = BTreeSet::new();
            for &definition in &component {
                joined.extend(&supports[definition]);
                for &dependency in &edges[definition] {
                    joined.extend(&supports[dependency]);
                }
                if joined.len() > 128 {
                    return None;
                }
            }
            // Every member of an SCC reaches the same external assumptions.
            // Its outgoing components were already closed in dependency order.
            for definition in component {
                supports[definition] = joined.clone();
            }
        }
        Some(
            supports
                .into_iter()
                .map(|s| s.into_iter().collect())
                .collect(),
        )
    }
}

fn scalar_memory(program: &hir::Program, ty: TyId) -> bool {
    matches!(
        program.types.get(ty),
        Ty::Bool | Ty::Char | Ty::Integer { .. } | Ty::Float { .. }
    )
}
fn supported_type(program: &hir::Program, root: TyId) -> bool {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) {
            continue;
        }
        if seen.len() > 4096 {
            return false;
        }
        match program.types.get(ty) {
            Ty::Parameter { .. } | Ty::Function { .. } | Ty::ForAll { .. } | Ty::Error => {
                return false;
            }
            Ty::Reference { inner, .. }
            | Ty::Pointer { inner, .. }
            | Ty::Array { inner, .. }
            | Ty::Slice(inner) => pending.push(*inner),
            Ty::Named {
                definition,
                arguments,
            } => {
                if !arguments.is_empty() {
                    return false;
                }
                let Some(record) = program.records.iter().find(|r| r.definition == *definition)
                else {
                    return false;
                };
                pending.extend(record.fields.iter().map(|f| f.ty));
            }
            _ => {}
        }
    }
    true
}
fn contains_references(program: &hir::Program, ty: TyId) -> bool {
    match program.types.get(ty) {
        Ty::Reference { .. } => true,
        Ty::Array { inner, .. } | Ty::Slice(inner) => contains_references(program, *inner),
        // Aggregate returns require a field-by-field summary, not a guessed
        // union of all argument origins.
        Ty::Named { .. } | Ty::Parameter { .. } => true,
        _ => false,
    }
}
fn path_type(program: &hir::Program, mut ty: TyId, path: &[RegionStep]) -> Option<TyId> {
    for step in path {
        ty = match (step, program.types.get(ty)) {
            (RegionStep::Deref, Ty::Reference { inner, .. }) => *inner,
            (
                RegionStep::Field(index),
                Ty::Named {
                    definition,
                    arguments,
                },
            ) if arguments.is_empty() => {
                program
                    .records
                    .iter()
                    .find(|r| r.definition == *definition)?
                    .fields
                    .get(*index as usize)?
                    .ty
            }
            _ => return None,
        };
    }
    Some(ty)
}
fn input_path(text: &str) -> Option<(u32, Vec<RegionStep>)> {
    let mut parts = text.split('.');
    let parameter = parts.next()?.parse().ok()?;
    let mut path = Vec::new();
    for part in parts {
        if path.len() >= 128 {
            return None;
        }
        path.push(if part == "*" {
            RegionStep::Deref
        } else {
            RegionStep::Field(part.parse().ok()?)
        });
    }
    Some((parameter, path))
}

fn object(value: Json) -> Result<BTreeMap<String, Json>, String> {
    if let Json::Object(v) = value {
        Ok(v)
    } else {
        Err("expected a JSON object".into())
    }
}
fn take(map: &mut BTreeMap<String, Json>, name: &str) -> Result<Json, String> {
    map.remove(name)
        .ok_or_else(|| format!("missing member `{name}`"))
}
fn string(value: Json) -> Result<String, String> {
    if let Json::String(v) = value {
        if v.is_empty() || v.len() > 1024 {
            Err("invalid summary string length".into())
        } else {
            Ok(v)
        }
    } else {
        Err("expected a string".into())
    }
}
fn array(value: Json) -> Result<Vec<Json>, String> {
    if let Json::Array(v) = value {
        Ok(v)
    } else {
        Err("expected an array".into())
    }
}
fn no_unknown(map: &BTreeMap<String, Json>) -> Result<(), String> {
    if let Some(key) = map.keys().next() {
        Err(format!("unknown member `{key}`"))
    } else {
        Ok(())
    }
}
fn boolean(map: &mut BTreeMap<String, Json>, name: &str) -> Result<Option<bool>, String> {
    match map.remove(name) {
        None | Some(Json::Null) => Ok(None),
        Some(Json::Bool(b)) => Ok(Some(b)),
        _ => Err(format!("`{name}` must be a boolean or null")),
    }
}
fn indices(map: &mut BTreeMap<String, Json>, name: &str) -> Result<Option<Vec<u32>>, String> {
    match map.remove(name) {
        None | Some(Json::Null) => Ok(None),
        Some(value) => {
            let values = array(value)?
                .into_iter()
                .map(|v| {
                    if let Json::Number(n) = v {
                        u32::try_from(n).map_err(|_| "parameter index overflow".into())
                    } else {
                        Err("expected parameter index".into())
                    }
                })
                .collect::<Result<Vec<_>, String>>()?;
            if values.len() > 128 || values.windows(2).any(|p| p[0] >= p[1]) {
                return Err(
                    "effect indices must be sorted, unique, and at most 128 entries".into(),
                );
            }
            Ok(Some(values))
        }
    }
}
fn decode(text: &str, span: Span, digest: Digest) -> Result<Summary, String> {
    let mut root = object(json::parse(text)?)?;
    let schema = match take(&mut root, "schema")? {
        Json::Number(1) => 1,
        Json::Number(2) => 2,
        _ => return Err("unsupported external summary schema; expected 1 or 2".into()),
    };
    let id = string(take(&mut root, "id")?)?;
    let version = string(take(&mut root, "version")?)?;
    let artifact = Digest::parse(&string(take(&mut root, "artifact")?)?)
        .ok_or("artifact must be a lowercase SHA-256 identity")?;
    let mut functions = Vec::new();
    let mut names = HashSet::new();
    for entry in array(take(&mut root, "functions")?)? {
        if functions.len() >= 128 {
            return Err("summary exceeds 128 functions".into());
        }
        let mut f = object(entry)?;
        let name = string(take(&mut f, "name")?)?;
        if !names.insert(name.clone()) {
            return Err("duplicate function in summary".into());
        }
        let abi = string(take(&mut f, "abi")?)?;
        let signature = Digest::parse(&string(take(&mut f, "signature")?)?)
            .ok_or("invalid signature digest")?;
        let returns = array(take(&mut f, "returns")?)?
            .into_iter()
            .map(string)
            .collect::<Result<Vec<_>, _>>()?;
        if returns.len() > 128 {
            return Err("too many return paths".into());
        }
        let mut e = object(take(&mut f, "effects")?)?;
        let effects = Effects {
            no_retain: boolean(&mut e, "no_retain")?,
            no_free: boolean(&mut e, "no_free")?,
            no_callback: boolean(&mut e, "no_callback")?,
            no_unwind: boolean(&mut e, "no_unwind")?,
            no_suspend: boolean(&mut e, "no_suspend")?,
            no_block: boolean(&mut e, "no_block")?,
            no_allocate: boolean(&mut e, "no_allocate")?,
            preserves_validity: boolean(&mut e, "preserves_validity")?,
            reads: indices(&mut e, "reads")?,
            writes: indices(&mut e, "writes")?,
            stores: if schema == 1 {
                Some(Vec::new())
            } else {
                decode_stores(e.remove("stores"))?
            },
        };
        no_unknown(&e)?;
        no_unknown(&f)?;
        functions.push(FunctionSummary {
            name,
            abi,
            signature,
            effects,
            returns,
        });
    }
    no_unknown(&root)?;
    Ok(Summary {
        schema,
        id,
        version,
        artifact,
        digest,
        functions,
        span,
    })
}

fn decode_stores(value: Option<Json>) -> Result<Option<Vec<ReferenceStore>>, String> {
    let Some(value) = value else {
        return Ok(None);
    };
    if matches!(value, Json::Null) {
        return Ok(None);
    }
    let mut stores = Vec::new();
    let mut targets = HashSet::new();
    for value in array(value)? {
        if stores.len() >= 128 {
            return Err("summary exceeds 128 reference stores".into());
        }
        let mut item = object(value)?;
        let target = string(take(&mut item, "target")?)?;
        if !targets.insert(target.clone()) {
            return Err("duplicate reference store target".into());
        }
        let sources = array(take(&mut item, "sources")?)?
            .into_iter()
            .map(string)
            .collect::<Result<Vec<_>, _>>()?;
        if sources.is_empty() || sources.len() > 64 {
            return Err("reference store needs 1 to 64 entry sources".into());
        }
        let definite = match string(take(&mut item, "when")?)?.as_str() {
            "always" => true,
            "maybe" => false,
            _ => return Err("reference store `when` must be `always` or `maybe`".into()),
        };
        no_unknown(&item)?;
        stores.push(ReferenceStore {
            target,
            sources,
            definite,
        });
    }
    Ok(Some(stores))
}
