//! Declaration identities and implementation witnesses for static/dynamic dispatch.

use super::DefId;
use crate::arena::Access as _;
use crate::types::{GenericArg, TyId};
mod callable;
mod copy;
pub(crate) use copy::eligibility as copy_eligibility;
pub(crate) use copy::implementations as copy_implementations;
mod verify;
pub(crate) use verify::validate;
mod select;
pub(crate) use callable::{closure_selection, validate_closure_trait};
pub(crate) use select::Matcher;
pub use select::supertraits;
pub use select::{SelectionError, check_bounds, select_drop, select_method, select_trait};
pub use select::{check_bounds as validate_arguments, require_trait};

/// Built-ins have language-defined permission; nominal values require a checked
/// Copy impl and its ordinary trait-bound obligations. This is the sole query.
pub fn is_copy(program: &mut super::Program, ty: TyId) -> bool {
    select::copy(program, ty)
}

pub fn has_drop(program: &super::Program, ty: TyId) -> bool {
    matches!(program.types.get(ty), crate::types::Ty::Named { .. })
        && !matches!(select_drop(program, ty), Ok(None))
}

pub fn parameter_has_role(
    program: &super::Program,
    owner: DefId,
    index: u32,
    role: LanguageItem,
) -> bool {
    let Some(definition) = program.definitions.get_id(owner) else {
        return false;
    };
    let mut pending: Vec<_> = definition
        .bounds
        .iter()
        .filter(|bound| bound.parameter == index)
        .map(|bound| bound.trait_ref.definition)
        .collect();
    let mut seen = std::collections::HashSet::new();
    while let Some(definition) = pending.pop() {
        if !seen.insert(definition) {
            continue;
        }
        if seen.len() > 4096 {
            return false;
        }
        let Some(trait_) = program
            .traits
            .iter()
            .find(|trait_| trait_.definition == definition)
        else {
            continue;
        };
        if trait_.language_item == Some(role) {
            return true;
        }
        pending.extend(trait_.supertraits.iter().map(|parent| parent.definition));
    }
    false
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LanguageItem {
    Send,
    Sync,
    TaskTransfer,
    SuspendSafe,
    Copy,
    Drop,
    From,
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitRef {
    pub definition: DefId,
    pub arguments: Vec<GenericArg>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitBound {
    pub parameter: u32,
    pub trait_ref: TraitRef,
}

#[derive(Clone, Debug)]
pub struct Trait {
    pub definition: DefId,
    pub methods: Vec<TraitMethod>,
    pub language_item: Option<LanguageItem>,
    pub supertraits: Vec<TraitRef>,
}

#[derive(Clone, Debug)]
pub struct TraitMethod {
    pub definition: DefId,
    /// Prefix of method arguments supplied by Self and the owning trait.
    pub inherited_parameters: u32,
    pub has_default: bool,
}

#[derive(Clone, Debug)]
pub struct Impl {
    pub negative: bool,
    pub definition: DefId,
    pub target: TyId,
    pub trait_ref: Option<TraitRef>,
    pub methods: Vec<ImplMethod>,
}

/// Restrictions are consulted before positive selection. They cannot become
/// witnesses or acquire trust, and therefore need no recursive trait matching.
pub(crate) fn negative_roles(
    program: &super::Program,
    nominal: DefId,
) -> impl Iterator<Item = LanguageItem> + '_ {
    program.implementations.iter().filter_map(move |item| {
        if !item.negative
            || !matches!(program.types.get(item.target), crate::types::Ty::Named { definition, .. } if *definition == nominal)
        {
            return None;
        }
        let reference = item.trait_ref.as_ref()?;
        program.traits.iter().find(|trait_| trait_.definition == reference.definition)?.language_item
    })
}

#[derive(Clone, Debug)]
pub struct ImplMethod {
    pub declaration: Option<DefId>,
    pub implementation: DefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodSelection {
    pub definition: DefId,
    pub type_arguments: Vec<GenericArg>,
}

#[derive(Clone, Debug)]
pub struct Vtable {
    pub trait_ref: TraitRef,
    pub concrete: TyId,
    pub slots: Vec<VtableSlot>,
}

#[derive(Clone, Debug)]
pub struct VtableSlot {
    pub declaration: DefId,
    pub implementation: DefId,
    pub signature: TyId,
    pub type_arguments: Vec<GenericArg>,
}
