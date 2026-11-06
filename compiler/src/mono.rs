//! HIR specialization before MIR optimization. Concrete bodies are lowered
//! afresh, so this API never silently discards an optimized MIR input.

mod function;
mod glue;
mod intrinsics;
mod types;

use crate::{
    ctfe,
    external::SummaryReport,
    hir, layout, mir,
    source::{SourceMap, Span},
    symbol::Interner,
    types::{GenericArg, GenericParamKind, Region, TyId},
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    fmt::Write,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InstanceKey {
    pub definition: hir::DefId,
    pub arguments: Vec<GenericArg>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstanceId(pub u32);
#[derive(Clone, Debug)]
pub struct Instance {
    pub key: InstanceKey,
    pub definition: hir::DefId,
}
#[derive(Clone, Debug)]
pub struct DropInstance {
    pub ty: TyId,
    pub instance: InstanceId,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub instances: usize,
    pub instances_per_definition: usize,
    pub instructions: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            instances: 100_000,
            instances_per_definition: 1024,
            instructions: 1_000_000,
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub target: layout::TargetLayout,
    pub constants: ctfe::Limits,
    pub limits: Limits,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            target: layout::TargetLayout::LP64,
            constants: ctfe::Limits::default(),
            limits: Limits::default(),
        }
    }
}
pub struct Context<'a> {
    pub symbols: &'a Interner,
    pub sources: &'a SourceMap,
    pub external: &'a [SummaryReport],
}
#[derive(Debug)]
pub struct Program {
    pub hir: hir::Program,
    pub mir: mir::Program,
    pub instances: Vec<Instance>,
    pub roots: Vec<InstanceId>,
    pub drop_instances: Vec<DropInstance>,
    pub layouts: layout::Table,
    pub analysis: mir::Analysis,
}
#[derive(Clone, Debug)]
pub struct Error {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}
impl fmt::Display for Error {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        output.write_str(&self.message)
    }
}
impl std::error::Error for Error {}

/// All source bodies without type/constant parameters are useful default roots.
/// Lifetime binders remain universal; they do not create machine-code instances.
pub fn default_roots(program: &hir::Program) -> Vec<InstanceKey> {
    program
        .functions
        .iter()
        .filter_map(|function| {
            let definition = &program.definitions[function.definition];
            if definition
                .generic_parameter_kinds
                .iter()
                .any(|kind| *kind != GenericParamKind::Lifetime)
            {
                return None;
            }
            let arguments = program
                .types
                .generic_parameters(function.definition)
                .iter()
                .map(|(name, _)| {
                    GenericArg::Lifetime(Region::Named {
                        owner: function.definition,
                        name: *name,
                    })
                })
                .collect();
            Some(InstanceKey {
                definition: function.definition,
                arguments,
            })
        })
        .collect()
}

pub fn instantiate(
    source: &hir::Program,
    roots: &[InstanceKey],
    context: Context<'_>,
    options: Options,
) -> Result<Program, Error> {
    let span = fallback(source);
    source
        .validate()
        .map_err(|error| problem(span, "E-MONO-INPUT", error.to_string()))?;
    if options.constants.pointer_bits != options.target.pointer_bits {
        return Err(problem(
            span,
            "E-MONO-TARGET",
            "constant evaluation and layout targets disagree",
        ));
    }
    let mut builder = Builder::new(source, options);
    let roots = roots
        .iter()
        .cloned()
        .map(|key| builder.enqueue(key))
        .collect::<Result<_, _>>()?;
    builder.expand()?;
    finish(builder, roots, context)
}

fn finish(
    builder: Builder<'_>,
    roots: Vec<InstanceId>,
    context: Context<'_>,
) -> Result<Program, Error> {
    let Builder {
        program: mut hir,
        instances,
        drop_instances,
        options,
        ..
    } = builder;
    let span = fallback(&hir);
    hir.validate()
        .map_err(|error| problem(span, "E-MONO-VERIFY", error.to_string()))?;
    let mir =
        mir::lower(&mut hir).map_err(|error| problem(error.span, "E-MONO-LOWER", error.message))?;
    mir.validate(&mut hir)
        .map_err(|error| problem(span, "E-MONO-VERIFY", error.to_string()))?;
    let layout_roots = storage_types(&mir, &hir)?;
    let layouts = layout::compute(
        &mut hir,
        options.target,
        context.symbols,
        context.sources,
        &layout_roots,
    )
    .map_err(|error| problem(error.span.unwrap_or(span), "E-LAYOUT", error.message))?;
    let analysis = mir::analyze(
        &mir,
        &mut hir,
        context.symbols,
        context.external,
        context.sources,
    )
    .map_err(|error| problem(span, error.code, error.message))?;
    let mut diagnostics = Vec::new();
    analysis.diagnostics(&mut diagnostics);
    if let Some(error) = diagnostics.into_iter().next() {
        return Err(problem(error.primary, error.code, error.message));
    }
    analysis
        .drops
        .require_concrete()
        .map_err(|error| problem(span, "E-MONO-DROP", error.to_string()))?;
    Ok(Program {
        hir,
        mir,
        instances,
        roots,
        drop_instances,
        layouts,
        analysis,
    })
}

fn storage_types(program: &mir::Program, hir: &hir::Program) -> Result<Vec<TyId>, Error> {
    let mut seen = HashSet::new();
    let mut roots = Vec::new();
    for body in &program.functions {
        for local in &body.locals {
            types::require_concrete(&hir.types, local.ty)
                .map_err(|message| problem(local.span, "E-MONO-TYPE", message))?;
            if local.kind != mir::LocalKind::Address && seen.insert(local.ty) {
                roots.push(local.ty);
            }
        }
    }
    Ok(roots)
}

struct Builder<'a> {
    source: &'a hir::Program,
    program: hir::Program,
    options: Options,
    source_bodies: Vec<Option<usize>>,
    record_indices: Vec<Option<usize>>,
    enum_indices: Vec<Option<usize>>,
    instances: Vec<Instance>,
    indices: HashMap<InstanceKey, InstanceId>,
    intrinsic_instances: HashMap<InstanceKey, hir::DefId>,
    counts: Vec<usize>,
    mappings: Vec<types::Mapping>,
    drop_types: HashSet<TyId>,
    drop_instances: Vec<DropInstance>,
    remaining: usize,
}
impl<'a> Builder<'a> {
    fn new(source: &'a hir::Program, options: Options) -> Self {
        let mut source_bodies = vec![None; source.definitions.len()];
        for (index, function) in source.functions.iter().enumerate() {
            source_bodies[function.definition.0 as usize] = Some(index);
        }
        let mut record_indices = vec![None; source.definitions.len()];
        let mut enum_indices = vec![None; source.definitions.len()];
        for (index, record) in source.records.iter().enumerate() {
            record_indices[record.definition.0 as usize] = Some(index);
        }
        for (index, enumeration) in source.enums.iter().enumerate() {
            enum_indices[enumeration.definition.0 as usize] = Some(index);
        }
        // This is the owned output snapshot. Every instantiated body subsequently
        // moves into it once; fixed-point iterations do not clone source graphs.
        let mut program = source.clone();
        program.functions.clear();
        Self {
            source,
            program,
            options,
            source_bodies,
            record_indices,
            enum_indices,
            instances: Vec::new(),
            indices: HashMap::new(),
            intrinsic_instances: HashMap::new(),
            counts: vec![0; source.definitions.len()],
            mappings: Vec::new(),
            drop_types: HashSet::new(),
            drop_instances: Vec::new(),
            remaining: options.limits.instructions,
        }
    }
    fn enqueue(&mut self, mut key: InstanceKey) -> Result<InstanceId, Error> {
        let source = self
            .source
            .definitions
            .get(key.definition.0 as usize)
            .ok_or_else(|| {
                problem(
                    fallback(self.source),
                    "E-MONO-ROOT",
                    "instance names an invalid definition",
                )
            })?;
        if self.source_bodies[key.definition.0 as usize].is_none() {
            return Err(problem(
                source.span,
                "E-MONO-ROOT",
                "instance has no source function body",
            ));
        }
        self.normalize_key(&mut key)?;
        if let Some(&id) = self.indices.get(&key) {
            return Ok(id);
        }
        self.check_budget(&key)?;
        let (definition, mapping) = self.create_definition(&key)?;
        let id = InstanceId(self.instances.len() as u32);
        self.counts[key.definition.0 as usize] += 1;
        self.indices.insert(key.clone(), id);
        self.instances.push(Instance { key, definition });
        self.mappings.push(mapping);
        Ok(id)
    }
    fn normalize_key(&mut self, key: &mut InstanceKey) -> Result<(), Error> {
        let source = &self.source.definitions[key.definition];
        if source.generic_parameter_kinds.len() != key.arguments.len() {
            return Err(problem(
                source.span,
                "E-MONO-ARGUMENT",
                "generic instance argument count mismatch",
            ));
        }
        self.normalize_arguments(key)?;
        if source
            .generic_parameter_kinds
            .iter()
            .all(|kind| *kind == GenericParamKind::Lifetime)
        {
            key.arguments = self
                .source
                .types
                .generic_parameters(key.definition)
                .iter()
                .map(|(name, _)| {
                    GenericArg::Lifetime(Region::Named {
                        owner: key.definition,
                        name: *name,
                    })
                })
                .collect();
        }
        hir::traits::validate_arguments(&mut self.program, key.definition, &key.arguments)
            .map_err(|error| problem(source.span, "E-MONO-BOUND", error.to_string()))?;
        ctfe::check_assertions(
            &mut self.program,
            key.definition,
            &key.arguments,
            self.options.constants,
        )
        .map_err(|error| problem(error.span, error.code, error.message))
    }
    fn normalize_arguments(&mut self, key: &mut InstanceKey) -> Result<(), Error> {
        let source = &self.source.definitions[key.definition];
        let mut mapping = types::Mapping::default();
        let substitution = types::Substitution {
            owner: key.definition,
            arguments: &[],
            destination: key.definition,
        };
        let mut mapper = types::Mapper::new(
            &mut self.program,
            substitution,
            self.options.constants,
            &mut mapping,
        );
        for (argument, kind) in key
            .arguments
            .iter_mut()
            .zip(&source.generic_parameter_kinds)
        {
            if !types::kind_matches(*argument, *kind) {
                return Err(problem(
                    source.span,
                    "E-MONO-ARGUMENT",
                    "generic instance argument kind mismatch",
                ));
            }
            *argument = mapper
                .normalize_argument(*argument)
                .map_err(|message| problem(source.span, "E-MONO-ARGUMENT", message))?;
        }
        Ok(())
    }
    fn check_budget(&mut self, key: &InstanceKey) -> Result<(), Error> {
        let definition = &self.source.definitions[key.definition];
        if self.instances.len() >= self.options.limits.instances
            || self.counts[key.definition.0 as usize]
                >= self.options.limits.instances_per_definition
        {
            return Err(problem(
                definition.span,
                "E-MONO-LIMIT",
                "generic instantiation count limit exceeded",
            ));
        }
        let function =
            &self.source.functions[self.source_bodies[key.definition.0 as usize].unwrap()];
        let cost = function
            .expressions
            .len()
            .saturating_add(function.statements.len())
            .saturating_add(function.locals.len())
            .saturating_add(1);
        self.remaining = self.remaining.checked_sub(cost).ok_or_else(|| {
            problem(
                definition.span,
                "E-MONO-LIMIT",
                "monomorphized instruction budget exceeded",
            )
        })?;
        Ok(())
    }
    fn create_definition(
        &mut self,
        key: &InstanceKey,
    ) -> Result<(hir::DefId, types::Mapping), Error> {
        let mut declaration = self.source.definitions[key.definition].clone();
        let specialized = declaration
            .generic_parameter_kinds
            .iter()
            .any(|kind| *kind != GenericParamKind::Lifetime);
        let id = if specialized {
            hir::DefId(self.program.definitions.len() as u32)
        } else {
            key.definition
        };
        if specialized {
            self.program.definitions.push(declaration.clone());
        }
        let mut mapping = types::Mapping::default();
        let substitution = types::Substitution {
            owner: key.definition,
            arguments: &key.arguments,
            destination: id,
        };
        let mut mapper = types::Mapper::new(
            &mut self.program,
            substitution,
            self.options.constants,
            &mut mapping,
        );
        declaration.ty = mapper
            .ty(declaration.ty)
            .map_err(|message| problem(declaration.span, "E-MONO-TYPE", message))?;
        declaration
            .generic_parameter_kinds
            .retain(|kind| *kind == GenericParamKind::Lifetime);
        declaration.type_parameter_count = 0;
        declaration.bounds.clear();
        self.program.definitions[id] = declaration;
        let parameters: Vec<_> = self
            .source
            .types
            .generic_parameters(key.definition)
            .iter()
            .copied()
            .filter(|(_, kind)| *kind == GenericParamKind::Lifetime)
            .collect();
        self.program
            .types
            .register_generic_parameters(id, &parameters);
        if specialized {
            let module = self.program.definitions[id].module;
            self.program.modules[module].definitions.push(id);
        }
        Ok((id, mapping))
    }
    fn expand(&mut self) -> Result<(), Error> {
        let mut index = 0;
        while index < self.instances.len() {
            let instance = self.instances[index].clone();
            let source_index =
                self.source_bodies[instance.key.definition.0 as usize].expect("queued source body");
            let source = self.source;
            let mut mapping = std::mem::take(&mut self.mappings[index]);
            let function = self.instantiate_function(
                &source.functions[source_index],
                &instance,
                &mut mapping,
            )?;
            self.mappings[index] = mapping;
            self.enqueue_drop_glue(&function)?;
            self.program.functions.push(function);
            index += 1;
        }
        Ok(())
    }
}

impl Program {
    pub fn dump(&self, symbols: &Interner) -> String {
        let mut output = String::from("cavoite monomorphized HIR/MIR / no native code generated\n");
        for (index, instance) in self.instances.iter().enumerate() {
            let _ = writeln!(
                output,
                "  instance i{index}: source #{} {:?} -> definition #{}",
                instance.key.definition.0, instance.key.arguments, instance.definition.0
            );
        }
        for layout in &self.layouts.entries {
            let ty = self
                .hir
                .types
                .display(layout.ty, symbols, &self.hir.definitions);
            let _ = writeln!(
                output,
                "  layout {ty}: size={} align={} {:?}",
                layout.size, layout.alignment, layout.kind
            );
        }
        for drop in &self.drop_instances {
            let _ = writeln!(
                output,
                "  user Drop ty{} -> instance i{}",
                drop.ty.0, drop.instance.0
            );
        }
        output.push_str(&self.mir.dump(&self.hir, symbols));
        output.push_str(&self.analysis.dump());
        output
    }
}

fn fallback(program: &hir::Program) -> Span {
    program
        .definitions
        .first()
        .map_or(Span::new(crate::source::FileId(0), 0, 0), |definition| {
            definition.span
        })
}
fn problem(span: Span, code: &'static str, message: impl Into<String>) -> Error {
    Error {
        code,
        span,
        message: message.into(),
    }
}
