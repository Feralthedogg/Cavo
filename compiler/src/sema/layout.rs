//! By-value dependencies, including enum payloads and generic arguments that
//! actually contribute to representation. No concrete target layout is emitted.
use super::*;
use std::collections::{BTreeSet, VecDeque};

pub(super) fn check(context: &mut Context<'_>) {
    let program = &context.program;
    let count = program.definitions.len();
    let mut fields = vec![None; count];
    for record in &program.records {
        fields[record.definition.0 as usize] =
            Some(record.fields.iter().map(|f| f.ty).collect::<Vec<_>>());
    }
    for enumeration in &program.enums {
        let payloads = enumeration
            .variants
            .iter()
            .flat_map(|id| match program.types.get(program.definitions[id].ty) {
                Ty::Function { parameters, .. } => parameters.clone(),
                _ => Vec::new(),
            })
            .collect();
        fields[enumeration.definition.0 as usize] = Some(payloads);
    }
    let nominals: Vec<_> = fields
        .iter()
        .enumerate()
        .filter_map(|(i, f)| f.is_some().then_some(i))
        .collect();
    if nominals.is_empty() {
        return;
    }
    let mut reverse = vec![BTreeSet::new(); count];
    for &owner in &nominals {
        let mut pending = fields[owner].as_ref().unwrap().clone();
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match program.types.get(ty) {
                Ty::Named {
                    definition,
                    arguments,
                } => {
                    reverse[definition.0 as usize].insert(owner);
                    pending.extend(arguments.iter().filter_map(|argument| argument.ty()));
                }
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    pending.push(*inner)
                }
                _ => {}
            }
        }
    }
    let mut required = vec![BTreeSet::new(); count];
    let mut queue: VecDeque<_> = nominals.iter().copied().collect();
    let mut queued = vec![false; count];
    for &n in &nominals {
        queued[n] = true;
    }
    let size =
        program.types.values().len() + count + fields.iter().flatten().map(Vec::len).sum::<usize>();
    let parameters = program
        .definitions
        .iter()
        .map(|d| d.type_parameter_count as usize)
        .max()
        .unwrap_or(0)
        + 1;
    let mut fuel = 1_000_000usize.max(size.saturating_mul(parameters).saturating_mul(16));
    while let Some(owner) = queue.pop_front() {
        queued[owner] = false;
        let Some((parameters, _)) = dependencies(
            owner,
            fields[owner].as_ref().unwrap(),
            &required,
            program,
            &mut fuel,
        ) else {
            context.error(
                "E-TYPE-LIMIT",
                "by-value type dependencies exceed their size-scaled analysis budget",
                context.program.definitions[owner].span,
            );
            return;
        };
        let before = required[owner].len();
        required[owner].extend(parameters);
        if before != required[owner].len() {
            for &parent in &reverse[owner] {
                if !queued[parent] {
                    queued[parent] = true;
                    queue.push_back(parent);
                }
            }
        }
    }
    let mut edges = vec![Vec::new(); count];
    for &owner in &nominals {
        let Some((_, children)) = dependencies(
            owner,
            fields[owner].as_ref().unwrap(),
            &required,
            program,
            &mut fuel,
        ) else {
            context.error(
                "E-TYPE-LIMIT",
                "by-value type dependencies exceed their size-scaled analysis budget",
                context.program.definitions[owner].span,
            );
            return;
        };
        edges[owner] = children.into_iter().collect();
    }
    for component in crate::graph::components(&edges) {
        if component.len() > 1
            || component
                .first()
                .is_some_and(|&node| edges[node].contains(&node))
        {
            let first = component[0];
            let mut diagnostic = Diagnostic::error(
                "E-TYPE-RECURSIVE",
                "value type has an infinite by-value representation",
                context.program.definitions[first].span,
            )
            .help("break a recursive value dependency with a reference or pointer");
            for &member in component.iter().skip(1).take(4) {
                diagnostic = diagnostic.label(
                    context.program.definitions[member].span,
                    "part of this by-value dependency cycle",
                );
            }
            report(context.diagnostics, diagnostic);
        }
    }
}

fn dependencies(
    owner: usize,
    fields: &[TyId],
    required: &[BTreeSet<u32>],
    program: &hir::Program,
    fuel: &mut usize,
) -> Option<(BTreeSet<u32>, BTreeSet<usize>)> {
    let mut parameters = BTreeSet::new();
    let mut children = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut pending = fields.to_vec();
    while let Some(ty) = pending.pop() {
        *fuel = fuel.checked_sub(1)?;
        if !seen.insert(ty) {
            continue;
        }
        match program.types.get(ty) {
            Ty::Parameter {
                owner: definition,
                index,
            } if definition.0 as usize == owner => {
                parameters.insert(*index);
            }
            Ty::Named {
                definition,
                arguments,
            } => {
                let child = definition.0 as usize;
                children.insert(child);
                for &parameter in &required[child] {
                    pending.push(arguments.get(parameter as usize)?.ty()?);
                }
            }
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                pending.push(*inner)
            }
            // References, raw pointers and callable values have indirection.
            _ => {}
        }
    }
    Some((parameters, children))
}
