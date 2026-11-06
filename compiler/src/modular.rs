//! Stable declaration contracts. Callers use these bounds; implementation
//! inference is retained separately and must refine every published promise.
pub mod capsule;
mod syntax;
mod verify;
pub(crate) use syntax::collect;
pub(crate) use verify::analyze;

use crate::{external::ReferenceStore, hir, mir::effects::Effect, source::Span};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Default)]
pub struct Declarations {
    pub assumptions: BTreeMap<hir::DefId, BTreeSet<crate::contracts::Trust>>,
    pub functions: BTreeMap<hir::DefId, Contract>,
    pub imported: BTreeMap<hir::DefId, String>,
}

#[derive(Clone, Debug)]
pub struct Contract {
    pub upper: BTreeSet<Effect>,
    pub bounded: bool,
    pub pure: bool,
    pub no_retain: bool,
    pub no_callback: bool,
    pub no_free: bool,
    pub reads: Option<Vec<String>>,
    pub writes: Option<Vec<String>>,
    pub returns: Option<Vec<String>>,
    pub normal: Vec<ReferenceStore>,
    pub panic: Vec<ReferenceStore>,
    pub cancel: Vec<ReferenceStore>,
    pub explicit: bool,
    pub affinity: bool,
    pub span: Span,
}

impl Contract {
    pub(crate) fn cleanup_safe(&self) -> bool {
        use Effect::*;
        self.bounded
            && self.upper.is_disjoint(&BTreeSet::from([
                Poll,
                AsyncPreempt,
                Park,
                Cancel,
                Panic,
                Allocate,
                Block,
                Thread,
            ]))
    }
    pub(crate) fn conservative(span: Span) -> Self {
        Self {
            upper: crate::mir::effects::all_effects(),
            bounded: false,
            pure: false,
            no_retain: false,
            no_callback: false,
            no_free: false,
            reads: None,
            writes: None,
            returns: None,
            normal: Vec::new(),
            panic: Vec::new(),
            cancel: Vec::new(),
            explicit: false,
            affinity: false,
            span,
        }
    }
}

pub(crate) fn usable(program: &hir::Program, definition: hir::DefId) -> bool {
    program
        .functions
        .iter()
        .any(|function| function.definition == definition)
        || program.modular.imported.contains_key(&definition)
        || program.traits.iter().any(|item| {
            item.methods
                .iter()
                .any(|method| method.definition == definition)
        })
}

#[derive(Debug, Default)]
pub struct Report {
    pub diagnostics: Vec<crate::diagnostic::Diagnostic>,
}
