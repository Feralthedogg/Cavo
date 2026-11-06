use super::*;
use std::{collections::HashMap, ops::Range};

struct Node {
    leaves: Range<usize>,
    fields: Vec<usize>,
    variants: HashMap<hir::DefId, usize>,
    tag: Option<usize>,
    user_drop: bool,
}

pub(super) struct Paths {
    pub roots: Vec<usize>,
    nodes: Vec<Node>,
    pub leaves: usize,
}

impl Paths {
    pub fn build(body: &Body, properties: &Properties) -> Result<Self, InvariantError> {
        let mut paths = Self {
            roots: Vec::with_capacity(body.locals.len()),
            nodes: Vec::new(),
            leaves: 0,
        };
        for local in &body.locals {
            let root = if matches!(local.kind, LocalKind::Address | LocalKind::ArrayIterator) {
                paths.scalar(false)?
            } else {
                paths.add(local.ty, properties, 0)?
            };
            paths.roots.push(root);
        }
        Ok(paths)
    }

    fn node(&mut self, user_drop: bool) -> Result<usize, InvariantError> {
        require(self.nodes.len() < LIMIT, "owned move-path limit exceeded")?;
        let id = self.nodes.len();
        self.nodes.push(Node {
            leaves: self.leaves..self.leaves,
            fields: Vec::new(),
            variants: HashMap::new(),
            tag: None,
            user_drop,
        });
        Ok(id)
    }

    fn scalar(&mut self, user_drop: bool) -> Result<usize, InvariantError> {
        let id = self.node(user_drop)?;
        self.leaves += 1;
        self.nodes[id].leaves.end = self.leaves;
        Ok(id)
    }

    fn add(
        &mut self,
        ty: TyId,
        properties: &Properties,
        depth: usize,
    ) -> Result<usize, InvariantError> {
        require(depth < 128, "owned move-path depth limit exceeded")?;
        let id = self.node(properties.user_drop(ty))?;
        if let Some(variants) = properties.enum_variants(ty) {
            self.nodes[id].tag = Some(self.leaves);
            self.leaves += 1;
            for &variant in variants {
                let fields = properties
                    .variant_fields(ty, variant)
                    .ok_or_else(|| InvariantError::new("missing enum field type facts".into()))?;
                let payload = self.aggregate(fields, properties, depth + 1)?;
                self.nodes[id].variants.insert(variant, payload);
            }
        } else if let Some(fields) = properties.fields(ty) {
            for &field in fields {
                let child = self.add(field, properties, depth + 1)?;
                self.nodes[id].fields.push(child);
            }
        }
        self.finish(id);
        Ok(id)
    }

    fn aggregate(
        &mut self,
        fields: &[TyId],
        properties: &Properties,
        depth: usize,
    ) -> Result<usize, InvariantError> {
        let id = self.node(false)?;
        for &field in fields {
            let child = self.add(field, properties, depth)?;
            self.nodes[id].fields.push(child);
        }
        self.finish(id);
        Ok(id)
    }

    fn finish(&mut self, id: usize) {
        if self.nodes[id].leaves.start == self.leaves {
            self.leaves += 1;
        }
        self.nodes[id].leaves.end = self.leaves;
    }

    pub fn field(&self, node: usize, field: u32) -> Result<usize, InvariantError> {
        self.nodes[node]
            .fields
            .get(field as usize)
            .copied()
            .ok_or_else(|| InvariantError::new("field has no owned initialization path".into()))
    }
    pub fn variant(&self, node: usize, variant: hir::DefId) -> Result<usize, InvariantError> {
        self.nodes[node]
            .variants
            .get(&variant)
            .copied()
            .ok_or_else(|| InvariantError::new("variant has no owned initialization path".into()))
    }
    pub fn protected(&self, node: usize) -> bool {
        self.nodes[node].user_drop
    }
    pub fn contains_tag(&self, node: usize, tag: usize) -> bool {
        self.nodes[tag]
            .tag
            .is_some_and(|tag| self.nodes[node].leaves.contains(&tag))
    }
    pub fn tag_initialized(&self, node: usize, state: &State) -> bool {
        self.nodes[node]
            .tag
            .is_some_and(|tag| state.init[tag] == Init::Yes)
    }
    pub fn initialized(&self, node: usize, state: &State) -> bool {
        state.init[self.nodes[node].leaves.clone()]
            .iter()
            .all(|init| *init == Init::Yes)
    }
    pub fn may_live(&self, node: usize, state: &State) -> bool {
        state.init[self.nodes[node].leaves.clone()]
            .iter()
            .any(|init| *init != Init::No)
    }
    pub fn set(&self, access: &Access, state: &mut State, init: Init) {
        if let Some(node) = access.node {
            for current in &mut state.init[self.nodes[node].leaves.clone()] {
                *current = if access.indexed {
                    match (*current, init) {
                        (Init::Yes, Init::Yes) => Init::Yes,
                        (Init::No, Init::No) => Init::No,
                        _ => Init::Maybe,
                    }
                } else {
                    init
                };
            }
        }
    }
}
