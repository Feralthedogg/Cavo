//! Contract identities, evidence and checks are independent of their renderer.
//! A logical predicate is never an ordinary bool that can forge permission.

mod analysis;
mod checks;
mod dependencies;
mod evidence;
mod guard;
mod json;
mod roles;
pub(crate) use analysis::analyze;
pub(crate) use dependencies::collect as trust_dependencies;
pub(crate) use roles::{intrinsic_shape, predicate_shape, validate_hir};
pub(crate) mod memory;
pub(crate) mod purity;
pub(crate) mod source;
pub use evidence::*;
pub use guard::*;
pub use source::Report;

use crate::{hir, source::Span, types::GenericArg};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default)]
pub struct Declarations {
    pub predicates: BTreeMap<hir::DefId, PredicateDefinition>,
    pub intrinsics: BTreeMap<hir::DefId, Intrinsic>,
    /// Only the typed signature expressions, before the body is checked.
    pub signatures: BTreeMap<hir::DefId, hir::Function>,
}

#[derive(Clone, Debug)]
pub struct PredicateDefinition {
    pub memory: Option<MemoryPredicate>,
    pub body: Option<hir::Function>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryPredicate {
    Scalar,
    Readable,
    Writable,
    ReadableUnaligned,
    WritableUnaligned,
    Initialized,
    Disjoint,
    OwnedAllocation,
    BorrowedFrom,
    ActiveUnion,
    NoRetain,
    NoCallback,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    TaskJoin,
    TaskCancel,
    TaskIgnore,
    Length,
    AsPtr,
    AsMutPtr,
    Read,
    ReadUnaligned,
    Take,
    Initialize,
    Replace,
    WriteUnaligned,
    Allocate,
    Deallocate,
    Offset,
}

#[derive(Clone, Debug)]
pub enum Action {
    Precondition,
    Requirement,
    Postcondition,
    Assume { reason: std::sync::Arc<str> },
}

#[derive(Clone, Debug)]
pub struct Atom {
    pub predicate: MemoryPredicate,
    pub type_arguments: Vec<GenericArg>,
    pub arguments: Vec<crate::mir::Operand>,
    pub declaration: Span,
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub action: Action,
    pub atom: Atom,
}

#[derive(Clone, Debug)]
pub struct SourceAssumption {
    pub predicate: hir::ExprId,
    pub reason: std::sync::Arc<str>,
}
