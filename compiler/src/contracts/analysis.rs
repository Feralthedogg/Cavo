use super::{memory::*, *};
use crate::{
    hir, layout,
    local::properties::Properties,
    mir::*,
    source::SourceMap,
    symbol::Interner,
    types::{Ty, TyId},
};
use std::collections::{BTreeSet, HashMap, VecDeque};

mod flow;
mod obligations;
mod operations;

pub(crate) fn analyze(
    mir: &Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
    external: &[crate::external::SummaryReport],
) -> Result<Report, String> {
    let mut report = if needs_memory_analysis(hir) {
        memory_findings(mir, hir, symbols, sources, external)?
    } else {
        Report::default()
    };
    super::checks::collect(mir, hir, symbols, &mut report)?;
    report.artifact = Some(source::artifact_key(mir, hir));
    report.validate()?;
    Ok(report)
}

fn needs_memory_analysis(hir: &hir::Program) -> bool {
    !(hir.contracts.predicates.is_empty()
        && hir.contracts.intrinsics.is_empty()
        && !hir
            .definitions
            .iter()
            .any(|d| d.kind == hir::DefinitionKind::Union)
        && !hir
            .contracts
            .signatures
            .values()
            .any(|signature| !signature.clauses.is_empty())
        && !hir
            .types
            .values()
            .iter()
            .any(|ty| matches!(ty, Ty::Pointer { .. }))
        && !hir.functions.iter().any(|body| {
            body.statements
                .iter()
                .any(|s| matches!(s.kind, hir::StmtKind::Assume(_)))
        }))
}

fn memory_findings(
    mir: &Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
    external: &[crate::external::SummaryReport],
) -> Result<Report, String> {
    let properties = Properties::compute(hir);
    let dependencies = super::trust_dependencies(mir, hir, external, &properties)?;
    let layouts = memory_layouts(mir, hir, symbols, sources);
    let mut report = Report::default();
    for body in &mir.functions {
        let liveness = crate::mir::borrow::live::Liveness::compute(body, &properties)
            .ok_or("contract liveness budget exceeded")?;
        let mut offset = 0u64;
        let events: Vec<_> = body
            .blocks
            .iter()
            .map(|block| {
                let start = offset;
                offset += block.statements.len() as u64 + 1;
                start
            })
            .collect();
        let context = Context {
            body,
            hir,
            symbols,
            properties: &properties,
            layouts: &layouts,
            events: &events,
            liveness: &liveness,
            dependencies: &dependencies,
        };
        let inputs = solve(&context)?;
        collect(&context, &inputs, &mut report)?;
    }
    report.dependencies = dependencies;
    Ok(report)
}

#[derive(Clone, Copy)]
struct Size {
    bytes: u64,
    alignment: u64,
}

struct Context<'a> {
    dependencies: &'a std::collections::BTreeMap<hir::DefId, BTreeSet<Trust>>,
    liveness: &'a crate::mir::borrow::live::Liveness,
    body: &'a Body,
    hir: &'a hir::Program,
    symbols: &'a Interner,
    properties: &'a Properties,
    layouts: &'a HashMap<TyId, Size>,
    events: &'a [u64],
}

fn memory_layouts(
    mir: &Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
) -> HashMap<TyId, Size> {
    let mut types = std::collections::HashSet::new();
    for body in &mir.functions {
        for local in &body.locals {
            types.insert(local.ty);
            if let Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } = hir.types.get(local.ty)
            {
                types.insert(*inner);
            }
        }
    }
    let mut layouts = HashMap::new();
    for ty in types {
        if let Ok(table) = layout::compute(hir, layout::TargetLayout::LP64, symbols, sources, &[ty])
            && let Some(layout) = table.get(ty)
        {
            layouts.insert(
                ty,
                Size {
                    bytes: layout.size,
                    alignment: layout.alignment,
                },
            );
        }
    }
    layouts
}

struct Engine<'a> {
    context: &'a Context<'a>,
    block: usize,
    statement: usize,
}

fn solve(context: &Context<'_>) -> Result<Vec<Option<State>>, String> {
    if context
        .body
        .locals
        .len()
        .saturating_mul(context.body.blocks.len())
        > 2_000_000
    {
        return Err("contract state budget exceeded".into());
    }
    let mut inputs = vec![None; context.body.blocks.len()];
    inputs[context.body.entry.0 as usize] = Some(State::new(context.body.locals.len()));
    let mut queue = VecDeque::from([context.body.entry.0 as usize]);
    let mut queued = vec![false; inputs.len()];
    queued[context.body.entry.0 as usize] = true;
    let mut budget = 2_000_000usize;
    while let Some(block) = queue.pop_front() {
        queued[block] = false;
        let mut state = inputs[block].clone().expect("queued contract block");
        let data = &context.body.blocks[block];
        budget = budget
            .checked_sub(data.statements.len() + 1)
            .ok_or("contract analysis work budget exceeded")?;
        let mut engine = Engine {
            context,
            block,
            statement: 0,
        };
        for (index, statement) in data.statements.iter().enumerate() {
            engine.statement = index;
            engine.statement(&statement.kind, statement.span, &mut state);
        }
        engine.statement = data.statements.len();
        for (successor, state) in engine.edges(&data.terminator, state) {
            let target = successor.0 as usize;
            let changed = match &mut inputs[target] {
                Some(input) => input.merge(&state),
                slot => {
                    *slot = Some(state);
                    true
                }
            };
            if changed && !queued[target] {
                queued[target] = true;
                queue.push_back(target);
            }
        }
    }
    Ok(inputs)
}

fn collect(
    context: &Context<'_>,
    inputs: &[Option<State>],
    report: &mut Report,
) -> Result<(), String> {
    for (block, input) in inputs.iter().enumerate() {
        let Some(mut state) = input.clone() else {
            continue;
        };
        let mut engine = Engine {
            context,
            block,
            statement: 0,
        };
        for (index, statement) in context.body.blocks[block].statements.iter().enumerate() {
            engine.statement = index;
            engine.statement_obligations(&statement.kind, statement.span, &state, report)?;
            engine.statement(&statement.kind, statement.span, &mut state);
        }
        engine.statement = context.body.blocks[block].statements.len();
        engine.exit_obligations(
            &context.body.blocks[block].terminator,
            context.body.blocks[block].span,
            &state,
            report,
        )?;
    }
    Ok(())
}

impl Engine<'_> {
    fn basis(&self, span: Span) -> Basis {
        Basis {
            event: EventId(
                (u64::from(self.context.body.definition.0) << 32)
                    | (self.context.events[self.block] + self.statement as u64),
            ),
            span,
            trust: BTreeSet::new(),
        }
    }

    fn size(&self, ty: TyId) -> Option<Size> {
        self.context.layouts.get(&ty).copied()
    }

    fn operand_type(&self, operand: &Operand) -> TyId {
        match operand {
            Operand::Constant { ty, .. }
            | Operand::ConstTerm { ty, .. }
            | Operand::Function { ty, .. } => *ty,
            Operand::Copy(place) | Operand::Move(place) => self.place_type(place),
            Operand::Unit => TyId::VOID,
        }
    }

    fn place_type(&self, place: &Place) -> TyId {
        let local = self.context.body.local(place.local);
        let mut ty = local.ty;
        let mut variant = None;
        for (index, projection) in place.projection.iter().enumerate() {
            ty = match projection {
                Projection::Deref if local.kind == LocalKind::Address && index == 0 => ty,
                Projection::Deref => match self.context.hir.types.get(ty) {
                    Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                    _ => return TyId::ERROR,
                },
                Projection::Downcast(value) => {
                    variant = Some(*value);
                    ty
                }
                Projection::Field(field) => {
                    let fields = if let Some(variant) = variant.take() {
                        self.context.properties.variant_fields(ty, variant)
                    } else {
                        self.context.properties.fields(ty)
                    };
                    fields
                        .and_then(|fields| fields.get(*field as usize))
                        .copied()
                        .unwrap_or(TyId::ERROR)
                }
                Projection::Index(_) => match self.context.hir.types.get(ty) {
                    Ty::Array { inner, .. }
                    | Ty::SymbolicArray { inner, .. }
                    | Ty::Slice(inner) => *inner,
                    _ => return TyId::ERROR,
                },
            };
        }
        ty
    }
}
