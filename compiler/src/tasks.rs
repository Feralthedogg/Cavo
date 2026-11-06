//! Typed task boundaries. Runtime admission/drain remains an explicit MIR
//! protocol; type checking never substitutes the pinned LLAM host drain.

mod analysis;
mod availability;
mod verify;
pub(crate) use verify::intrinsic_shape;
pub(crate) use verify::validate_hir;
pub mod transfer;
use crate::{
    hir,
    source::Span,
    types::{Region, TyId},
};
pub use analysis::Report;
pub(crate) use analysis::analyze;
pub(crate) use analysis::independent_frames;

#[derive(Clone, Debug, Default)]
pub struct Declarations {
    pub trusted: std::collections::BTreeMap<hir::DefId, std::sync::Arc<str>>,
    pub result: Option<hir::DefId>,
    pub(crate) forbidden:
        std::collections::BTreeMap<hir::DefId, std::collections::HashSet<transfer::Property>>,
    pub task: Option<hir::DefId>,
    pub spawn_error: Option<hir::DefId>,
    pub task_error: Option<hir::DefId>,
    pub scopes: Vec<Scope>,
    pub captures: Vec<hir::DefId>,
}

#[derive(Clone, Debug)]
pub struct Scope {
    pub owner: hir::DefId,
    pub region: Region,
    pub span: Span,
}

pub fn task_arguments(program: &hir::Program, ty: TyId) -> Option<(Region, TyId)> {
    let crate::types::Ty::Named {
        definition,
        arguments,
    } = program.types.get(ty)
    else {
        return None;
    };
    if Some(*definition) != program.tasks.task {
        return None;
    }
    match arguments.as_slice() {
        [
            crate::types::GenericArg::Lifetime(region),
            crate::types::GenericArg::Type(result),
        ] => Some((*region, *result)),
        _ => None,
    }
}

pub(crate) fn admission_result(
    program: &hir::Program,
    ty: TyId,
    result: TyId,
    captures: TyId,
) -> bool {
    use crate::types::{GenericArg as G, Ty};
    let Ty::Named {
        definition,
        arguments,
    } = program.types.get(ty)
    else {
        return false;
    };
    if program.tasks.result != Some(*definition) {
        return false;
    }
    let [G::Type(task), G::Type(error)] = arguments.as_slice() else {
        return false;
    };
    let Some((_, child)) = task_arguments(program, *task) else {
        return false;
    };
    child == result
        && matches!(program.types.get(*error), Ty::Named { definition, arguments }
        if Some(*definition) == program.tasks.spawn_error && arguments == &[G::Type(captures)])
}
