//! Normal-return memory transformers. All paths are relative to entry inputs;
//! they are not allocation identities, native addresses or persistent IDs.
use super::{RegionContract, cfg, flow, properties::Properties};
use crate::{
    diagnostic::{Diagnostic, report},
    external::Bindings,
    hir,
};
use std::collections::{BTreeSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryPlace {
    pub input: usize,
    pub fields: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemoryLoan {
    Input(usize),
    Fresh(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MemoryOrigin {
    Reference {
        place: MemoryPlace,
        precise: bool,
        mutable: bool,
        loan: MemoryLoan,
    },
    Opaque(usize),
    Static,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryValue {
    pub origins: Vec<MemoryOrigin>,
    pub fields: Option<Vec<MemoryValue>>,
    pub functions: Vec<hir::DefId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryWrite {
    pub target: MemoryPlace,
    pub value: MemoryValue,
    pub definite: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemorySummary {
    pub normal_return: bool,
    pub writes: Vec<MemoryWrite>,
    pub returned: MemoryValue,
    /// Transitive ancestry of each fresh, exported loan. Internal loans that
    /// cannot outlive the call are removed; entry and other exported loans stay.
    pub loans: Vec<Vec<MemoryLoan>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Inferred {
    Unknown,
    Ready(MemorySummary),
}

#[derive(Clone, Copy)]
pub(super) struct Calls<'a> {
    pub regions: &'a [Option<RegionContract>],
    pub external: &'a Bindings,
    pub memory: &'a [Inferred],
}

pub(super) fn infer(
    program: &hir::Program,
    properties: &Properties,
    regions: &[Option<RegionContract>],
    external: &Bindings,
    graphs: &[Option<cfg::Graph>],
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Vec<Inferred>> {
    let mut summaries = vec![Inferred::Unknown; program.definitions.len()];
    let mut callers = vec![BTreeSet::new(); program.definitions.len()];
    for (index, function) in program.functions.iter().enumerate() {
        if graphs[index].is_some() {
            summaries[function.definition.0 as usize] = Inferred::Ready(MemorySummary::default());
        }
        for expression in &function.expressions {
            if let hir::ExprKind::Definition(id) = expression.kind {
                callers[id.0 as usize].insert(index);
            }
        }
    }
    let mut function_indices = vec![None; program.definitions.len()];
    for (index, function) in program.functions.iter().enumerate() {
        function_indices[function.definition.0 as usize] = Some(index);
    }
    let mut edges = vec![Vec::new(); program.functions.len()];
    for (target, users) in callers.iter().enumerate() {
        if let Some(dependency) = function_indices[target] {
            for &caller in users {
                edges[caller].push(dependency);
            }
        }
    }
    let groups = crate::graph::components(&edges);
    let mut component = vec![0; program.functions.len()];
    for (group, members) in groups.iter().enumerate() {
        for &index in members {
            component[index] = group;
        }
    }
    let mut queued = vec![false; program.functions.len()];
    for (group, members) in groups.iter().enumerate() {
        // Acyclic components run once. Only a recursive component consumes a
        // convergence budget; unrelated functions cannot exhaust it.
        let estimated: usize = members
            .iter()
            .map(|&i| {
                program.functions[i].expressions.len()
                    + program.functions[i].statements.len()
                    + graphs[i].as_ref().map_or(0, |g| g.blocks.len())
            })
            .sum();
        let mut fuel = 8_000_000usize.max(estimated.saturating_mul(256));
        let run_limit = 4096usize.max(members.len().saturating_mul(128));
        let mut runs = 0usize;
        let mut queue: VecDeque<_> = members.iter().copied().collect();
        for &index in members {
            queued[index] = true;
        }
        while let Some(index) = queue.pop_front() {
            queued[index] = false;
            let Some(graph) = &graphs[index] else {
                continue;
            };
            let calls = Calls {
                regions,
                external,
                memory: &summaries,
            };
            let result =
                flow::summarize(&program.functions[index], graph, program, properties, calls);
            runs += 1;
            let Some(remaining) = fuel.checked_sub(result.work.max(1)) else {
                report(
                    diagnostics,
                    Diagnostic::error(
                        "E-MEMORY-LIMIT",
                        "recursive memory component exceeds its size-scaled work budget",
                        program.functions[index].body.span,
                    )
                    .note("the limit applies to this dependency component, not the whole program"),
                );
                return None;
            };
            fuel = remaining;
            if runs > run_limit {
                report(
                    diagnostics,
                    Diagnostic::error(
                        "E-MEMORY-LIMIT",
                        "recursive memory component did not converge within its budget",
                        program.functions[index].body.span,
                    ),
                );
                return None;
            }
            let definition = program.functions[index].definition;
            for dependency in &result.dependencies {
                if let Some(target) = function_indices[dependency.0 as usize]
                    && component[target] > group
                {
                    report(
                        diagnostics,
                        Diagnostic::error(
                            "E-MEMORY-DEPENDENCY",
                            "an indirect effect dependency was discovered after its analysis component",
                            program.functions[index].body.span,
                        ),
                    );
                    return None;
                }
                callers[dependency.0 as usize].insert(index);
            }
            let next = result
                .memory
                .map(Inferred::Ready)
                .unwrap_or(Inferred::Unknown);
            if next != summaries[definition.0 as usize] {
                summaries[definition.0 as usize] = next;
                for &caller in &callers[definition.0 as usize] {
                    if component[caller] == group && !queued[caller] {
                        queued[caller] = true;
                        queue.push_back(caller);
                    }
                }
            }
        }
    }
    Some(summaries)
}

impl MemorySummary {
    pub(super) fn valid(&self, inputs: usize, definitions: usize) -> bool {
        if !self.normal_return {
            return self == &Self::default();
        }
        if self.writes.len() > 1024 || self.loans.len() > 128 {
            return false;
        }
        let place = |p: &MemoryPlace| p.input < inputs && p.fields.len() <= 128;
        let loan = |l: &MemoryLoan| match *l {
            MemoryLoan::Input(i) => i < inputs,
            MemoryLoan::Fresh(i) => (i as usize) < self.loans.len(),
        };
        let mut pending = vec![&self.returned];
        for write in &self.writes {
            if !place(&write.target) {
                return false;
            }
            pending.push(&write.value);
        }
        let mut remaining = 4096usize;
        while let Some(value) = pending.pop() {
            let Some(next) = remaining.checked_sub(1 + value.origins.len() + value.functions.len())
            else {
                return false;
            };
            remaining = next;
            if value.origins.len() > 64
                || value.functions.len() > 64
                || value.functions.windows(2).any(|p| p[0] >= p[1])
                || value.functions.iter().any(|d| d.0 as usize >= definitions)
            {
                return false;
            }
            for origin in &value.origins {
                let valid = match origin {
                    MemoryOrigin::Reference {
                        place: p, loan: l, ..
                    } => place(p) && loan(l),
                    MemoryOrigin::Opaque(i) => *i < inputs,
                    MemoryOrigin::Static => true,
                };
                if !valid {
                    return false;
                }
            }
            if let Some(fields) = &value.fields {
                pending.extend(fields);
            }
        }
        for (index, parents) in self.loans.iter().enumerate() {
            if parents.len() > 128
                || parents.windows(2).any(|p| p[0] >= p[1])
                || parents
                    .iter()
                    .any(|l| !loan(l) || *l == MemoryLoan::Fresh(index as u32))
            {
                return false;
            }
        }
        let mut resolved = vec![false; self.loans.len()];
        for _ in 0..self.loans.len() {
            let mut progress = false;
            for (index, parents) in self.loans.iter().enumerate() {
                if !resolved[index]
                    && parents.iter().all(|l| match *l {
                        MemoryLoan::Input(_) => true,
                        MemoryLoan::Fresh(i) => resolved[i as usize],
                    })
                {
                    resolved[index] = true;
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        if resolved.iter().any(|&r| !r) {
            return false;
        }
        true
    }
}
