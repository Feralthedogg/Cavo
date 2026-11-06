use super::*;

impl State {
    pub(in crate::mir::borrow) fn capture(
        &self,
        context: &Context<'_>,
    ) -> Option<summary::Outcome> {
        let returned = &self.values[context.body.return_local.0 as usize];
        let mut roots = returned.loans();
        for location in self.writes.keys() {
            if let Root::External(input) = location.root {
                roots.extend(self.memory[input as usize].project(&location.path).loans());
            }
        }
        let mut capture = Capture {
            context,
            state: self,
            fresh: BTreeMap::new(),
            visiting: Loans::new(),
            loans: Vec::new(),
        };
        for loan in roots {
            capture.origin(loan)?;
        }
        let returned = capture.value(returned)?;
        let mut writes = Vec::with_capacity(self.writes.len());
        for (location, definite) in &self.writes {
            let Root::External(input) = location.root else {
                return None;
            };
            let value = capture.value(&self.memory[input as usize].project(&location.path))?;
            writes.push(summary::Write {
                target: summary::Footprint {
                    input,
                    path: location.path.clone(),
                },
                value,
                definite: *definite,
            });
        }
        Some(summary::Outcome {
            returned,
            writes,
            loans: capture.loans,
            unmodeled: false,
        })
    }
}

struct Capture<'a> {
    context: &'a Context<'a>,
    state: &'a State,
    fresh: BTreeMap<LoanId, u32>,
    visiting: Loans,
    loans: Vec<summary::FreshLoan>,
}
impl Capture<'_> {
    fn origin(&mut self, loan: LoanId) -> Option<summary::Origin> {
        if let Some(index) = self.context.sites.inputs.iter().position(|id| *id == loan) {
            return Some(summary::Origin::Input(index as u32));
        }
        if Some(loan) == self.context.sites.static_loan {
            return Some(summary::Origin::Static);
        }
        if let Some(&index) = self.fresh.get(&loan) {
            return Some(summary::Origin::Fresh(index));
        }
        if self.loans.len() >= ORIGIN_LIMIT || !self.visiting.insert(loan) {
            return None;
        }
        let memory = self.state;
        let state = &memory.loans[loan.0 as usize];
        let mut parents = BTreeSet::new();
        for &parent in &state.parents {
            parents.insert(self.origin(parent)?);
        }
        let targets = state
            .targets
            .iter()
            .map(|location| {
                let Root::External(input) = location.root else {
                    return None;
                };
                Some(summary::Footprint {
                    input,
                    path: location.path.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let index = self.loans.len() as u32;
        self.loans.push(summary::FreshLoan {
            targets,
            parents,
            mutable: self.context.loans[loan.0 as usize].mutable,
            unknown: state.unknown,
        });
        self.fresh.insert(loan, index);
        self.visiting.remove(&loan);
        Some(summary::Origin::Fresh(index))
    }
    fn value(&mut self, value: &Value) -> Option<summary::Value> {
        let mut fields = BTreeMap::new();
        for (path, loans) in &value.fields {
            let origins = loans
                .iter()
                .map(|&loan| self.origin(loan))
                .collect::<Option<BTreeSet<_>>>()?;
            fields.insert(path.clone(), origins);
        }
        Some(summary::Value {
            parameters: value.parameters.clone(),
            fields,
            functions: value.functions.clone(),
            vtables: value.vtables.clone(),
            unknown: value.unknown,
        })
    }
}
