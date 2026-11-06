use super::*;
use crate::local::{
    MemoryLoan, MemoryOrigin, MemoryPlace, MemorySummary, MemoryValue, MemoryWrite,
};

pub(super) fn build(
    program: &hir::Program,
    contract: &RegionContract,
    parameters: &[TyId],
    result: TyId,
    effects: &Effects,
    binding: &Binding,
) -> Option<MemorySummary> {
    let mut summary = MemorySummary {
        normal_return: true,
        ..MemorySummary::default()
    };
    let mut moved = BTreeSet::new();
    let mut remaining = 4096usize;
    for &parameter in effects.writes.as_ref()? {
        let Ty::Reference {
            inner,
            mutable: true,
            ..
        } = *program.types.get(*parameters.get(parameter as usize)?)
        else {
            return None;
        };
        let input = contract
            .inputs
            .iter()
            .position(|i| i.parameter == parameter && i.path.is_empty())?;
        let mut frame = Vec::new();
        scalar_frame(program, inner, &mut Vec::new(), &mut frame, &mut remaining)?;
        for fields in frame {
            summary.writes.push(MemoryWrite {
                target: MemoryPlace { input, fields },
                value: MemoryValue::default(),
                definite: false,
            });
        }
    }
    for store in effects.stores.as_ref()? {
        let (parameter, path) = input_path(&store.target)?;
        if !effects.writes.as_ref()?.contains(&parameter) {
            return None;
        }
        let deref = path.iter().rposition(|s| *s == RegionStep::Deref)?;
        let pointer = contract
            .inputs
            .iter()
            .position(|i| i.parameter == parameter && i.path == path[..deref])?;
        let cell = contract
            .inputs
            .iter()
            .position(|i| i.parameter == parameter && i.path == path)?;
        let target_ty = path_type(program, *parameters.get(parameter as usize)?, &path)?;
        let Ty::Reference { mutable, inner, .. } = *program.types.get(target_ty) else {
            return None;
        };
        if !writable(program, parameters[parameter as usize], &path) {
            return None;
        }
        if path.iter().filter(|s| **s == RegionStep::Deref).count() > 1
            && !effects.reads.as_ref()?.contains(&parameter)
        {
            return None;
        }
        let fields = path[deref + 1..]
            .iter()
            .map(|s| {
                if let RegionStep::Field(i) = s {
                    Some(*i)
                } else {
                    None
                }
            })
            .collect::<Option<Vec<_>>>()?;
        let mut origins = Vec::new();
        for source in &store.sources {
            if source == "static" {
                if mutable {
                    return None;
                }
                origins.push(MemoryOrigin::Static);
                continue;
            }
            let (source_parameter, source_path) = input_path(source)?;
            let input = contract.inputs.iter().position(|i| {
                i.parameter == source_parameter && i.path == source_path && i.region.is_some()
            })?;
            let source_ty = path_type(
                program,
                *parameters.get(source_parameter as usize)?,
                &source_path,
            )?;
            if !program.types.compatible(source_ty, target_ty)
                || !contract.outlives(contract.inputs[input].term, contract.inputs[cell].term)
            {
                return None;
            }
            if mutable {
                if source_path.contains(&RegionStep::Deref) || !moved.insert(input) {
                    return None;
                }
                let Ty::Reference {
                    inner: source_inner,
                    ..
                } = *program.types.get(source_ty)
                else {
                    return None;
                };
                if !program.types.region_invariant(source_inner, inner) {
                    return None;
                }
            }
            if source_path.contains(&RegionStep::Deref)
                && !effects.reads.as_ref()?.contains(&source_parameter)
            {
                return None;
            }
            origins.push(MemoryOrigin::Reference {
                place: MemoryPlace {
                    input,
                    fields: Vec::new(),
                },
                precise: true,
                mutable,
                loan: MemoryLoan::Input(input),
            });
        }
        origins.sort();
        origins.dedup();
        summary.writes.push(MemoryWrite {
            target: MemoryPlace {
                input: pointer,
                fields,
            },
            value: MemoryValue {
                origins,
                ..MemoryValue::default()
            },
            definite: store.definite,
        });
    }
    let mutable = matches!(
        program.types.get(result),
        Ty::Reference { mutable: true, .. }
    );
    for &input in &binding.returns {
        if mutable && moved.contains(&input) {
            return None;
        }
        let source = &contract.inputs[input];
        let reborrow =
            source.mutable == Some(true) && (!mutable || source.path.contains(&RegionStep::Deref));
        let loan = if reborrow {
            let index = summary.loans.len() as u32;
            summary.loans.push(vec![MemoryLoan::Input(input)]);
            MemoryLoan::Fresh(index)
        } else {
            MemoryLoan::Input(input)
        };
        summary.returned.origins.push(MemoryOrigin::Reference {
            place: MemoryPlace {
                input,
                fields: Vec::new(),
            },
            precise: true,
            mutable,
            loan,
        });
    }
    if binding.static_result {
        summary.returned.origins.push(MemoryOrigin::Static);
    }
    summary.writes.sort_by(|a, b| a.target.cmp(&b.target));
    if summary.writes.len() > 1024
        || summary
            .writes
            .windows(2)
            .any(|p| p[0].target == p[1].target)
    {
        return None;
    }
    Some(summary)
}

fn scalar_frame(
    program: &hir::Program,
    ty: TyId,
    path: &mut Vec<u32>,
    frame: &mut Vec<Vec<u32>>,
    remaining: &mut usize,
) -> Option<()> {
    *remaining = remaining.checked_sub(1)?;
    if path.len() > 128 || frame.len() > 1024 {
        return None;
    }
    match program.types.get(ty) {
        Ty::Reference { .. } => {}
        Ty::Named {
            definition,
            arguments,
        } if arguments.is_empty() => {
            let record = program
                .records
                .iter()
                .find(|r| r.definition == *definition)?;
            for (index, field) in record.fields.iter().enumerate() {
                path.push(index as u32);
                scalar_frame(program, field.ty, path, frame, remaining)?;
                path.pop();
            }
        }
        Ty::Array { inner, .. } | Ty::Slice(inner) => {
            if !plain_data(program, *inner, remaining, 0)? {
                return None;
            }
            frame.push(path.clone());
        }
        Ty::Void
        | Ty::Bool
        | Ty::Char
        | Ty::Integer { .. }
        | Ty::Float { .. }
        | Ty::Pointer { .. } => frame.push(path.clone()),
        _ => return None,
    }
    Some(())
}
fn plain_data(
    program: &hir::Program,
    ty: TyId,
    remaining: &mut usize,
    depth: usize,
) -> Option<bool> {
    if depth >= 128 {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    Some(match program.types.get(ty) {
        Ty::Void
        | Ty::Bool
        | Ty::Char
        | Ty::Integer { .. }
        | Ty::Float { .. }
        | Ty::Pointer { .. } => true,
        Ty::Array { inner, .. } | Ty::Slice(inner) => {
            plain_data(program, *inner, remaining, depth + 1)?
        }
        Ty::Named {
            definition,
            arguments,
        } if arguments.is_empty() => {
            let record = program
                .records
                .iter()
                .find(|r| r.definition == *definition)?;
            let mut plain = true;
            for field in &record.fields {
                plain &= plain_data(program, field.ty, remaining, depth + 1)?;
            }
            plain
        }
        _ => false,
    })
}

fn writable(program: &hir::Program, mut ty: TyId, path: &[RegionStep]) -> bool {
    for step in path {
        match (step, program.types.get(ty)) {
            (
                RegionStep::Deref,
                Ty::Reference {
                    mutable: true,
                    inner,
                    ..
                },
            ) => ty = *inner,
            (
                RegionStep::Field(index),
                Ty::Named {
                    definition,
                    arguments,
                },
            ) if arguments.is_empty() => {
                let Some(field) = program
                    .records
                    .iter()
                    .find(|r| r.definition == *definition)
                    .and_then(|r| r.fields.get(*index as usize))
                else {
                    return false;
                };
                ty = field.ty;
            }
            _ => return false,
        }
    }
    true
}
