//! Structural storage facts and the separately declared permission to copy.
//! Transfer-trait selection uses Structural directly, so Copy impl bounds may
//! depend on Send/Sync without recursively asking for Copy properties again.
mod structural;
use crate::{hir, types::TyId};
pub(crate) use structural::Structural;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Property {
    pub copy: bool,
    pub references: bool,
    pub may_drop: bool,
}

pub(crate) struct Properties {
    structural: Structural,
    copies: Vec<bool>,
}
impl std::ops::Deref for Properties {
    type Target = Structural;
    fn deref(&self) -> &Self::Target {
        &self.structural
    }
}
impl Properties {
    pub fn compute(program: &mut hir::Program) -> Self {
        let structural = Structural::compute(program);
        let count = program.types.values().len();
        let copies = (0..count)
            .map(|index| hir::traits::is_copy(program, TyId(index as u32)))
            .collect();
        Self { structural, copies }
    }
    pub fn get(&self, ty: TyId) -> Property {
        let shape = self.structural.get(ty);
        Property {
            copy: self.copies.get(ty.0 as usize).copied().unwrap_or(false),
            references: shape.references,
            may_drop: shape.may_drop,
        }
    }
    pub fn carries_origins(&self, ty: TyId) -> bool {
        let shape = self.structural.get(ty);
        shape.references || shape.raw_pointers
    }
}
