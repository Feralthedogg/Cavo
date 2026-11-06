use super::*;

pub(crate) fn path(text: &str) -> Option<(u32, Vec<Step>)> {
    let mut parts = text.split('.');
    let parameter = parts.next()?.parse().ok()?;
    let mut path = Vec::new();
    for part in parts {
        if path.len() >= 128 {
            return None;
        }
        path.push(match part {
            "*" => Step::Deref,
            "[]" => Step::Element,
            _ => Step::Field(part.parse().ok()?),
        });
    }
    Some((parameter, path))
}

pub(crate) fn footprint(text: &str, frame: &Frame) -> Option<Footprint> {
    let (parameter, path) = path(text)?;
    frame
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(index, input)| {
            if input.parameter != parameter {
                return None;
            }
            let suffix = path.strip_prefix(input.path.as_slice())?;
            if suffix.is_empty() && path.is_empty() {
                return Some((
                    input.path.len(),
                    Footprint {
                        input: index as u32,
                        path: Vec::new(),
                    },
                ));
            }
            let [Step::Deref, rest @ ..] = suffix else {
                return None;
            };
            Some((
                input.path.len(),
                Footprint {
                    input: index as u32,
                    path: rest.to_vec(),
                },
            ))
        })
        .max_by_key(|(length, _)| *length)
        .map(|(_, footprint)| footprint)
}

pub(crate) fn declared(
    definition: hir::DefId,
    contract: &crate::modular::Contract,
    frame: &Frame,
    hir: &hir::Program,
) -> Option<FunctionSummary> {
    let Ty::Function { parameters, result } = hir.types.get(hir.definitions[definition].ty) else {
        return None;
    };
    // A plain raw address is not a reference capability. The memory contract
    // pass handles it, while this domain conservatively retains argument origins.
    if parameters
        .iter()
        .any(|&ty| matches!(hir.types.get(ty), Ty::Pointer { .. }))
    {
        return None;
    }
    let mut summary = FunctionSummary::bottom(definition);
    summary.complete = frame.complete;
    accesses(&mut summary, contract, frame)?;
    let mut normal = Outcome::default();
    returns(&mut normal.returned, contract, frame, *result, hir)?;
    normal.writes = writes(&contract.normal, contract, frame)?;
    summary.normal = Some(normal);
    if contract
        .upper
        .contains(&super::super::effects::Effect::Panic)
    {
        summary.panic = Some(Outcome {
            writes: writes(&contract.panic, contract, frame)?,
            ..Outcome::default()
        });
    }
    if contract
        .upper
        .contains(&super::super::effects::Effect::Cancel)
    {
        summary.cancel = Some(Outcome {
            writes: writes(&contract.cancel, contract, frame)?,
            ..Outcome::default()
        });
    }
    Some(summary)
}

fn accesses(
    summary: &mut FunctionSummary,
    contract: &crate::modular::Contract,
    frame: &Frame,
) -> Option<()> {
    for write in [false, true] {
        let paths = if write {
            &contract.writes
        } else {
            &contract.reads
        };
        if let Some(paths) = paths {
            for path in paths {
                let target = footprint(path, frame)?;
                if write {
                    external::writable(target.input, frame)?;
                }
                summary.accesses.insert(Access { target, write });
            }
        } else {
            for (index, _) in frame.inputs.iter().enumerate() {
                if !write || external::writable(index as u32, frame).is_some() {
                    summary.accesses.insert(Access {
                        target: Footprint {
                            input: index as u32,
                            path: Vec::new(),
                        },
                        write,
                    });
                }
            }
        }
    }
    Some(())
}

fn returns(
    output: &mut Value,
    contract: &crate::modular::Contract,
    frame: &Frame,
    result: TyId,
    hir: &hir::Program,
) -> Option<()> {
    if let Some(paths) = &contract.returns {
        for source in paths {
            if let Some(origin) = external::origin(source, frame) {
                if frame.result.is_empty() {
                    output.fields.entry(Vec::new()).or_default().insert(origin);
                }
                for requirement in &frame.result {
                    output
                        .fields
                        .entry(requirement.path.clone())
                        .or_default()
                        .insert(origin);
                }
            } else {
                let (parameter, path) = path(source)?;
                output
                    .parameters
                    .entry(Vec::new())
                    .or_default()
                    .insert(ParameterOrigin { parameter, path });
            }
        }
    } else {
        for requirement in &frame.result {
            if requirement.path.contains(&Step::Deref) {
                continue;
            }
            let origins = output.fields.entry(requirement.path.clone()).or_default();
            for (index, _) in frame.inputs.iter().enumerate() {
                if frame.outlives(index as u32, requirement.region) {
                    origins.insert(Origin::Input(index as u32));
                }
            }
            if !requirement.invariant {
                origins.insert(Origin::Static);
            }
        }
        if matches!(
            hir.types.get(result),
            Ty::Parameter { .. } | Ty::Named { .. }
        ) && !frame.complete
        {
            output.unknown = true;
        }
    }
    Some(())
}

fn writes(
    stores: &[crate::external::ReferenceStore],
    contract: &crate::modular::Contract,
    frame: &Frame,
) -> Option<Vec<Write>> {
    let mut result = Vec::new();
    let specified: BTreeSet<_> = stores
        .iter()
        .filter_map(|store| footprint(&store.target, frame))
        .collect();
    for store in stores {
        result.push(declared_write(store, frame)?);
    }
    for (index, input) in frame.inputs.iter().enumerate() {
        let Storage::Pointee {
            input: parent,
            path,
        } = &input.storage
        else {
            continue;
        };
        if external::writable(*parent, frame).is_none() {
            continue;
        }
        let target = Footprint {
            input: *parent,
            path: path.clone(),
        };
        if specified.contains(&target) {
            continue;
        }
        let allowed = contract.writes.as_ref().is_none_or(|paths| {
            paths
                .iter()
                .filter_map(|path| footprint(path, frame))
                .any(|frame| frame.input == target.input && target.path.starts_with(&frame.path))
        });
        if !allowed {
            continue;
        }
        let mut value = Value::default();
        for (source, _) in frame.inputs.iter().enumerate() {
            if frame.outlives(source as u32, input.region) {
                value
                    .fields
                    .entry(Vec::new())
                    .or_default()
                    .insert(Origin::Input(source as u32));
            }
        }
        value
            .fields
            .entry(Vec::new())
            .or_default()
            .insert(Origin::Input(index as u32));
        result.push(Write {
            target,
            value,
            definite: false,
        });
    }
    havoc_pointees(&mut result, contract, frame);
    Some(result)
}

fn havoc_pointees(result: &mut Vec<Write>, contract: &crate::modular::Contract, frame: &Frame) {
    // Writable scalar/opaque pointees must also be killed. Leaving their entry
    // value intact would preserve stale function targets or hidden references.
    for (index, input) in frame.inputs.iter().enumerate() {
        if external::writable(index as u32, frame).is_none() {
            continue;
        }
        let target = Footprint {
            input: index as u32,
            path: Vec::new(),
        };
        if result.iter().any(|write| write.target == target) {
            continue;
        }
        let allowed = contract.writes.as_ref().is_none_or(|paths| {
            paths
                .iter()
                .filter_map(|path| footprint(path, frame))
                .any(|p| p.input == target.input && p.path.is_empty())
        });
        if allowed {
            result.push(Write {
                target,
                value: Value {
                    unknown: true,
                    ..Value::default()
                },
                definite: false,
            });
        }
        let _ = input;
    }
}

fn declared_write(store: &crate::external::ReferenceStore, frame: &Frame) -> Option<Write> {
    if let Some(write) = external::write(store, frame) {
        return Some(write);
    }
    let target = footprint(&store.target, frame)?;
    external::writable(target.input, frame)?;
    let mut value = Value::default();
    for source in &store.sources {
        let (parameter, path) = path(source)?;
        value
            .parameters
            .entry(Vec::new())
            .or_default()
            .insert(ParameterOrigin { parameter, path });
    }
    Some(Write {
        target,
        value,
        definite: store.definite,
    })
}
