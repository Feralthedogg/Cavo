//! Trait declarations are collected before their signatures. Implementations
//! provide checked witnesses; a spelling such as `Drop` never grants a role.

mod coherence;
mod collect;
mod drop_check;
mod implementations;
pub(crate) use drop_check::validate_destructors;
pub(crate) mod dynamic;

use super::*;
use crate::{hir::traits as model, types::GenericArg};

#[derive(Default)]
pub(super) struct State {
    pub method_owners: HashMap<DefId, DefId>,
    pub impl_indices: HashMap<DefId, usize>,
    pub trait_indices: HashMap<DefId, usize>,
    checks: BoundChecks,
}

enum BoundChecks {
    Pending(Vec<(DefId, Vec<GenericArg>, Span)>),
    Active,
}
impl Default for BoundChecks {
    fn default() -> Self {
        Self::Pending(Vec::new())
    }
}

impl Context<'_> {
    pub(super) fn is_copy_type(&mut self, ty: TyId) -> bool {
        model::is_copy(&mut self.program, ty)
    }

    pub(super) fn add_method_self(
        &mut self,
        method: DefId,
        parameters: &mut HashMap<Symbol, TyId>,
    ) {
        let Some(&owner) = self.trait_state.method_owners.get(&method) else {
            return;
        };
        let Some(&index) = self.trait_state.impl_indices.get(&owner) else {
            return;
        };
        let Some(name) = self.symbols.lookup("Self") else {
            return;
        };
        let target = self.program.implementations[index].target;
        if target == TyId::ERROR {
            return;
        }
        let arguments = self.program.types.generic_arguments(method);
        let count = self.program.types.generic_parameters(owner).len();
        let target = self
            .program
            .types
            .substitute_generics(target, owner, &arguments[..count]);
        match target {
            Ok(target) => {
                parameters.insert(name, target);
            }
            Err(error) => self.error(
                "E-TRAIT-TYPE",
                error.to_string(),
                self.definition(method).span,
            ),
        }
    }

    pub(super) fn trait_reference(
        &mut self,
        syntax: ast::TypeId,
        module: ModuleId,
        owner: DefId,
        parameters: &HashMap<Symbol, TyId>,
    ) -> Option<model::TraitRef> {
        let node = self.ast.ty(syntax);
        let TypeKind::Path { path, arguments } = &node.kind else {
            self.error("E-TRAIT-NAME", "a trait bound must name a trait", node.span);
            return None;
        };
        let definition = self.resolve(module, path)?;
        if self.definition(definition).kind != D::Trait {
            self.error(
                "E-TRAIT-NAME",
                "this name does not denote a trait",
                node.span,
            );
            return None;
        }
        let scope = super::const_generics::TypeScope {
            module,
            owner,
            parameters,
        };
        match self.resolve_generic_arguments(
            definition,
            arguments,
            scope,
            &super::constants::ConstBindings::new(),
            node.span,
        ) {
            Ok(arguments) => Some(model::TraitRef {
                definition,
                arguments,
            }),
            Err(error) => {
                self.error(error.code, error.message, error.span);
                None
            }
        }
    }

    pub(super) fn resolve_dynamic(
        &mut self,
        bounds: &[ast::TypeId],
        module: ModuleId,
        owner: DefId,
        parameters: &HashMap<Symbol, TyId>,
        span: Span,
    ) -> TyId {
        if bounds.len() != 1 {
            self.error(
                "E-TRAIT-OBJECT",
                "a dynamic object requires one principal trait",
                span,
            );
            return TyId::ERROR;
        }
        let Some(trait_ref) = self.trait_reference(bounds[0], module, owner, parameters) else {
            return TyId::ERROR;
        };
        self.validate_object_safety(trait_ref.definition);
        self.program.types.intern(Ty::Dynamic {
            trait_definition: trait_ref.definition,
            arguments: trait_ref.arguments,
        })
    }

    pub(super) fn check_generic_bounds(
        &mut self,
        owner: DefId,
        arguments: &[GenericArg],
        span: Span,
    ) {
        if let BoundChecks::Pending(pending) = &mut self.trait_state.checks {
            pending.push((owner, arguments.to_vec(), span));
            return;
        }
        if let Err(error) = model::check_bounds(&mut self.program, owner, arguments) {
            self.error("E-TRAIT-BOUND", error.to_string(), span);
        }
    }

    pub(super) fn activate_bound_checks(&mut self) {
        let BoundChecks::Pending(pending) =
            std::mem::replace(&mut self.trait_state.checks, BoundChecks::Active)
        else {
            return;
        };
        for (owner, arguments, span) in pending {
            self.check_generic_bounds(owner, &arguments, span);
        }
    }

    pub(super) fn lookup_associated(&self, owner: DefId, name: Symbol) -> Option<DefId> {
        if let Some(&index) = self.trait_state.trait_indices.get(&owner) {
            return self.program.traits[index]
                .methods
                .iter()
                .find(|method| self.definition(method.definition).name == name)
                .map(|method| method.definition);
        }
        let mut found = None;
        for implementation in &self.program.implementations {
            if !matches!(self.program.types.get(implementation.target), Ty::Named { definition, .. } if *definition == owner)
            {
                continue;
            }
            for method in &implementation.methods {
                if self.definition(method.implementation).name == name
                    && found.replace(method.implementation).is_some()
                {
                    return None;
                }
            }
        }
        found
    }

    pub(super) fn is_drop_method(&self, definition: DefId) -> bool {
        let drop = self
            .program
            .traits
            .iter()
            .find(|trait_| trait_.language_item == Some(model::LanguageItem::Drop));
        let Some(drop) = drop
            .and_then(|trait_| trait_.methods.first())
            .map(|method| method.definition)
        else {
            return false;
        };
        definition == drop
            || self
                .program
                .implementations
                .iter()
                .flat_map(|implementation| &implementation.methods)
                .any(|method| {
                    method.declaration == Some(drop) && method.implementation == definition
                })
    }

    pub(super) fn select_from_conversion(
        &mut self,
        source: TyId,
        target: TyId,
        span: Span,
    ) -> Option<model::MethodSelection> {
        let trait_ = self
            .program
            .traits
            .iter()
            .find(|trait_| trait_.language_item == Some(model::LanguageItem::From))?;
        let method = trait_.methods.first()?.definition;
        let arguments = [GenericArg::Type(target), GenericArg::Type(source)];
        match model::select_method(&self.program, method, &arguments) {
            Ok(selection) => selection,
            Err(error) => {
                self.error("E-TRAIT-SELECTION", error.to_string(), span);
                None
            }
        }
    }
}

fn clone_generic(parameter: &GenericParam) -> GenericParam {
    match parameter {
        GenericParam::Type { name, bounds } => GenericParam::Type {
            name: *name,
            bounds: bounds.clone(),
        },
        GenericParam::Const { name, ty } => GenericParam::Const {
            name: *name,
            ty: *ty,
        },
        GenericParam::Lifetime(name) => GenericParam::Lifetime(*name),
    }
}
