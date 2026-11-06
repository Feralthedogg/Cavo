//! Conservative finite witness propagation for effect dispatch. Captured/mutable
//! aliases and unknown call results invalidate the closed witness set.
use super::*;
use crate::mir::{LocalKind, Place, Rvalue, StatementKind};

pub(super) struct Witnesses {
    values: Vec<BTreeSet<u32>>,
    unknown: Vec<bool>,
}

impl Witnesses {
    pub fn compute(body: &Body) -> Self {
        let mut result = Self {
            values: vec![BTreeSet::new(); body.locals.len()],
            unknown: body
                .locals
                .iter()
                .map(|local| local.kind == LocalKind::Parameter)
                .collect(),
        };
        let mut copies = Vec::new();
        for block in &body.blocks {
            for statement in &block.statements {
                if let StatementKind::Assign { destination, value } = &statement.kind {
                    result.assignment(destination, value, &mut copies);
                }
            }
            if let Terminator::Call { destination, .. } | Terminator::DynCall { destination, .. } =
                &block.terminator
            {
                result.unknown[destination.local.0 as usize] = true;
            }
        }
        result.propagate(&copies);
        result
    }

    fn assignment(
        &mut self,
        destination: &Place,
        value: &Rvalue,
        copies: &mut Vec<(usize, usize)>,
    ) {
        let local = destination.local.0 as usize;
        if !destination.projection.is_empty() {
            self.unknown[local] = true;
            return;
        }
        match value {
            Rvalue::DynCoerce { vtable, .. } => {
                self.values[local].insert(*vtable);
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if place.projection.is_empty() =>
            {
                copies.push((local, place.local.0 as usize))
            }
            Rvalue::AddressOf(place)
            | Rvalue::Borrow {
                mutable: true,
                place,
            } => {
                self.unknown[place.local.0 as usize] = true;
            }
            _ => self.unknown[local] = true,
        }
    }

    fn propagate(&mut self, copies: &[(usize, usize)]) {
        let mut remaining = 200_000usize;
        loop {
            let mut changed = false;
            for &(to, from) in copies {
                if remaining == 0 {
                    self.unknown.fill(true);
                    return;
                }
                remaining -= 1;
                let unknown = self.unknown[from];
                changed |= unknown && !self.unknown[to];
                self.unknown[to] |= unknown;
                let before = self.values[to].len();
                let incoming = self.values[from].clone();
                self.values[to].extend(incoming);
                if self.values[to].len() > 128 {
                    self.unknown[to] = true;
                    self.values[to].clear();
                }
                changed |= self.values[to].len() != before;
            }
            if !changed {
                return;
            }
        }
    }

    pub fn targets(
        &self,
        receiver: &Operand,
        method: hir::DefId,
        hir: &hir::Program,
    ) -> Option<BTreeSet<hir::DefId>> {
        let (Operand::Copy(place) | Operand::Move(place)) = receiver else {
            return None;
        };
        if !place.projection.is_empty() || self.unknown[place.local.0 as usize] {
            return None;
        }
        let values = &self.values[place.local.0 as usize];
        if values.is_empty() {
            return None;
        }
        let mut targets = BTreeSet::new();
        for &vtable in values {
            let table = hir.vtables.get(vtable as usize)?;
            targets.insert(
                table
                    .slots
                    .iter()
                    .find(|slot| slot.declaration == method)?
                    .implementation,
            );
        }
        Some(targets)
    }
}
