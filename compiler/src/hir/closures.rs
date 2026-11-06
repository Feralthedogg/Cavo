use super::{DefId, DefinitionKind, InvariantError, Program};
use crate::arena::Access as _;
use crate::types::Ty;

/// Environments remain ordinary owned records. The kind selects the hidden
/// function's receiver contract, not an unchecked callable coercion.
#[derive(Clone, Debug)]
pub struct Closure {
    pub environment: DefId,
    pub function: DefId,
    pub kind: ClosureKind,
    /// Weaker callable contracts have real checked receiver-conversion bodies.
    pub adapters: Vec<(ClosureKind, DefId)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

impl ClosureKind {
    pub fn supports(self, required: Self) -> bool {
        self <= required
    }
}

impl Program {
    /// Definitions that cannot be addressed as bare source-module functions.
    /// Interface and summary lookup build this set once at their own boundary.
    pub fn internal_definitions(&self) -> std::collections::HashSet<DefId> {
        let mut internal = std::collections::HashSet::new();
        internal.extend(self.tasks.captures.iter().copied());
        internal.extend(self.contracts.intrinsics.keys().copied());
        internal.extend(self.modular.imported.keys().copied());
        for closure in &self.closures {
            internal.insert(closure.environment);
            internal.insert(closure.function);
            internal.extend(closure.adapters.iter().map(|(_, definition)| *definition));
        }
        for declaration in &self.traits {
            internal.extend(declaration.methods.iter().map(|method| method.definition));
        }
        for implementation in &self.implementations {
            internal.insert(implementation.definition);
            internal.extend(
                implementation
                    .methods
                    .iter()
                    .map(|method| method.implementation),
            );
        }
        internal
    }

    pub(super) fn validate_closures(&self) -> Result<(), InvariantError> {
        let mut environments = std::collections::HashSet::new();
        let mut functions = std::collections::HashSet::new();
        for closure in &self.closures {
            if !environments.insert(closure.environment) || !functions.insert(closure.function) {
                return Err(InvariantError(
                    "duplicate closure environment or function".into(),
                ));
            }
            self.validate_closure(closure)?;
            for &(kind, function) in &closure.adapters {
                if kind <= closure.kind || !functions.insert(function) {
                    return Err(InvariantError(
                        "invalid or duplicate closure adapter".into(),
                    ));
                }
                self.validate_closure_entry(closure.environment, function, kind)?;
            }
        }
        Ok(())
    }

    fn validate_closure(&self, closure: &Closure) -> Result<(), InvariantError> {
        self.validate_closure_entry(closure.environment, closure.function, closure.kind)
    }

    fn validate_closure_entry(
        &self,
        environment: DefId,
        function: DefId,
        kind: ClosureKind,
    ) -> Result<(), InvariantError> {
        let expected = environment;
        let environment = self.definitions.get_id(environment);
        let function = self.definitions.get_id(function);
        let (Some(environment), Some(function)) = (environment, function) else {
            return Err(InvariantError(
                "closure has an invalid definition ID".into(),
            ));
        };
        if environment.kind != DefinitionKind::Record || function.kind != DefinitionKind::Function {
            return Err(InvariantError(
                "closure metadata has an invalid definition kind".into(),
            ));
        }
        let Ty::Function { parameters, .. } = self.types.get(function.ty) else {
            return Err(InvariantError(
                "closure entry has no function signature".into(),
            ));
        };
        let Some(&receiver) = parameters.first() else {
            return Err(InvariantError(
                "closure entry has no environment receiver".into(),
            ));
        };
        let receiver = match (kind, self.types.get(receiver)) {
            (
                ClosureKind::Fn,
                Ty::Reference {
                    mutable: false,
                    inner,
                    ..
                },
            )
            | (
                ClosureKind::FnMut,
                Ty::Reference {
                    mutable: true,
                    inner,
                    ..
                },
            ) => *inner,
            (ClosureKind::FnOnce, _) => receiver,
            _ => {
                return Err(InvariantError(
                    "closure receiver does not match its callable kind".into(),
                ));
            }
        };
        if !matches!(self.types.get(receiver), Ty::Named { definition, .. } if *definition == expected)
        {
            return Err(InvariantError(
                "closure receiver has the wrong environment type".into(),
            ));
        }
        Ok(())
    }
}
