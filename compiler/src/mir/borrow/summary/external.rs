use super::*;
use crate::external::SummaryStatus;

pub(super) fn adapt(
    record: &SummaryReport,
    frame: &Frame,
    hir: &hir::Program,
) -> Option<FunctionSummary> {
    let effects = &record.effects;
    if record.status != SummaryStatus::Assumed
        || !frame.complete
        || [
            effects.no_retain,
            effects.no_free,
            effects.no_callback,
            effects.preserves_validity,
        ]
        .contains(&None)
        || ![
            effects.no_retain,
            effects.no_free,
            effects.no_callback,
            effects.preserves_validity,
        ]
        .iter()
        .all(|effect| *effect == Some(true))
    {
        return None;
    }
    let mut summary = FunctionSummary::bottom(record.function);
    summary.assumptions.insert(record.assumption);
    let mut normal = Outcome::default();
    let Ty::Function { result, .. } = hir
        .types
        .get(hir.definitions[record.function.0 as usize].ty)
    else {
        return None;
    };
    let mutable = matches!(hir.types.get(*result), Ty::Reference { mutable: true, .. });
    for source in &record.returns {
        let origin = return_origin(source, frame, mutable, &mut normal)?;
        normal
            .returned
            .fields
            .entry(Vec::new())
            .or_default()
            .insert(origin);
    }
    for &parameter in effects.reads.as_ref()? {
        add_access(&mut summary, frame, parameter, false)?;
    }
    for &parameter in effects.writes.as_ref()? {
        add_access(&mut summary, frame, parameter, true)?;
    }
    for store in effects.stores.as_ref()? {
        let write = write(store, frame)?;
        summary.accesses.insert(Access {
            target: write.target.clone(),
            write: true,
        });
        normal.writes.push(write);
    }
    // Schema 1/2 describes normal postconditions. Cancellation does not promise
    // those writes completed; retaining an unknown weak post-state is honest.
    let failure = failure(&normal);
    summary.panic = (effects.no_unwind != Some(true)).then(|| failure.clone());
    summary.cancel = Some(failure);
    summary.normal = Some(normal);
    Some(summary)
}

fn return_origin(text: &str, frame: &Frame, mutable: bool, normal: &mut Outcome) -> Option<Origin> {
    let origin = origin(text, frame)?;
    match origin {
        Origin::Static if mutable => None,
        Origin::Input(input) => {
            let source = &frame.inputs[input as usize];
            if mutable {
                writable(input, frame)?;
            }
            if source.mutable && (!mutable || source.path.contains(&Step::Deref)) {
                let id = normal.loans.len() as u32;
                normal.loans.push(FreshLoan {
                    targets: vec![Footprint {
                        input,
                        path: Vec::new(),
                    }],
                    parents: BTreeSet::from([origin]),
                    mutable,
                    unknown: false,
                });
                Some(Origin::Fresh(id))
            } else {
                Some(origin)
            }
        }
        _ => Some(origin),
    }
}

fn add_access(
    summary: &mut FunctionSummary,
    frame: &Frame,
    parameter: u32,
    write: bool,
) -> Option<()> {
    let input = frame.syntax_input(parameter, &[])?;
    if write && !frame.inputs[input].mutable {
        return None;
    }
    for (index, component) in frame.inputs.iter().enumerate() {
        if component.parameter == parameter && (!write || index == input) {
            summary.accesses.insert(Access {
                target: Footprint {
                    input: index as u32,
                    path: Vec::new(),
                },
                write,
            });
        }
    }
    Some(())
}

fn origin(text: &str, frame: &Frame) -> Option<Origin> {
    if text == "static" {
        return Some(Origin::Static);
    }
    let (parameter, path) = path(text)?;
    Some(Origin::Input(frame.syntax_input(parameter, &path)? as u32))
}

fn write(store: &crate::external::ReferenceStore, frame: &Frame) -> Option<Write> {
    let (parameter, syntax) = path(&store.target)?;
    let target_input = frame.syntax_input(parameter, &syntax)?;
    let target_ref = &frame.inputs[target_input];
    let Storage::Pointee { input, path } = &target_ref.storage else {
        return None;
    };
    writable(*input, frame)?;
    let mut value = Value::default();
    for source in &store.sources {
        let origin = origin(source, frame)?;
        if let Origin::Input(input) = origin
            && !frame.outlives(input, target_ref.region)
        {
            return None;
        }
        if origin == Origin::Static && target_ref.mutable {
            return None;
        }
        value.fields.entry(Vec::new()).or_default().insert(origin);
    }
    Some(Write {
        target: Footprint {
            input: *input,
            path: path.clone(),
        },
        value,
        definite: store.definite,
    })
}

fn writable(mut input: u32, frame: &Frame) -> Option<()> {
    loop {
        let reference = frame.inputs.get(input as usize)?;
        if !reference.mutable {
            return None;
        }
        match reference.storage {
            Storage::Pointee { input: parent, .. } => input = parent,
            Storage::Parameter { .. } => return Some(()),
        }
    }
}

fn failure(normal: &Outcome) -> Outcome {
    let writes = normal
        .writes
        .iter()
        .map(|write| Write {
            target: write.target.clone(),
            value: Value {
                unknown: true,
                ..Value::default()
            },
            definite: false,
        })
        .collect();
    Outcome {
        writes,
        unmodeled: !normal.writes.is_empty(),
        ..Outcome::default()
    }
}

fn path(text: &str) -> Option<(u32, Vec<Step>)> {
    let mut parts = text.split('.');
    let parameter = parts.next()?.parse().ok()?;
    let mut path = Vec::new();
    for part in parts {
        if path.len() >= 128 {
            return None;
        }
        path.push(if part == "*" {
            Step::Deref
        } else {
            Step::Field(part.parse().ok()?)
        });
    }
    Some((parameter, path))
}
