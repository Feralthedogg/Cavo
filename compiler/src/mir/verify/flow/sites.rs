use super::*;
use std::collections::HashMap;

#[derive(Clone, Copy)]
pub(super) enum Site {
    None,
    Capture(usize),
    Predicate(usize),
}

pub(super) struct VariantTest<'a> {
    pub place: &'a Place,
    pub variant: hir::DefId,
}

/// State snapshots retain compact IDs into immutable MIR sites, not cloned
/// projection vectors for every incoming edge of the fixed point.
pub(super) struct Sites<'a> {
    pub blocks: Vec<Vec<Site>>,
    pub captures: Vec<&'a Place>,
    pub tests: Vec<VariantTest<'a>>,
    tests_by_place: HashMap<&'a Place, HashMap<hir::DefId, usize>>,
}

impl<'a> Sites<'a> {
    pub fn build(body: &'a Body) -> Self {
        let mut sites = Self {
            blocks: Vec::with_capacity(body.blocks.len()),
            captures: Vec::new(),
            tests: Vec::new(),
            tests_by_place: HashMap::new(),
        };
        for block in &body.blocks {
            let mut statements = Vec::with_capacity(block.statements.len());
            for statement in &block.statements {
                statements.push(sites.statement(&statement.kind));
            }
            sites.blocks.push(statements);
        }
        sites
    }

    fn statement(&mut self, statement: &'a StatementKind) -> Site {
        match statement {
            StatementKind::Assign {
                value: Rvalue::AddressOf(place),
                ..
            } => {
                let id = self.captures.len();
                self.captures.push(place);
                Site::Capture(id)
            }
            StatementKind::Assign {
                destination,
                value: Rvalue::IsVariant { place, variant },
            } if destination.projection.is_empty() => {
                if let Some(id) = self.test(place, *variant) {
                    return Site::Predicate(id);
                }
                let id = self.tests.len();
                self.tests.push(VariantTest {
                    place,
                    variant: *variant,
                });
                self.tests_by_place
                    .entry(place)
                    .or_default()
                    .insert(*variant, id);
                Site::Predicate(id)
            }
            _ => Site::None,
        }
    }

    pub fn test(&self, place: &Place, variant: hir::DefId) -> Option<usize> {
        self.tests_by_place.get(place)?.get(&variant).copied()
    }
}
