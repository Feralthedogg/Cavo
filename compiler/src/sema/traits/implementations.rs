use super::*;
use crate::types::GenericParamKind;

impl Context<'_> {
    pub(in crate::sema) fn prepare_implementations(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let ItemKind::Impl {
                target, trait_type, ..
            } = &item.kind
            else {
                continue;
            };
            let (Some(owner), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            let parameters = self.parameters(owner);
            let target = self.resolve_type(*target, module, owner, &parameters);
            let trait_ref = trait_type
                .and_then(|syntax| self.trait_reference(syntax, module, owner, &parameters));
            let slot = self.trait_state.impl_indices[&owner];
            self.program.implementations[slot].target = target;
            self.program.implementations[slot].trait_ref = trait_ref;
            if trait_type.is_none()
                && !matches!(self.program.types.get(target), Ty::Named { .. } | Ty::Error)
            {
                self.error(
                    "E-IMPL-ORPHAN",
                    "inherent implementations require a locally declared nominal type",
                    item.span,
                );
            }
        }
    }

    pub(in crate::sema) fn validate_implementations(&mut self) {
        self.collect_trait_bounds();
        self.activate_bound_checks();
        self.reject_supertrait_cycles();
        self.validate_language_roles();
        for index in 0..self.program.implementations.len() {
            self.validate_implementation(index);
        }
        self.validate_trait_requirements();
        self.reject_overlapping_implementations();
        self.validate_dynamic_types();
    }

    fn validate_trait_requirements(&mut self) {
        let references: Vec<_> = self
            .program
            .definitions
            .iter()
            .flat_map(|definition| {
                definition
                    .bounds
                    .iter()
                    .map(|bound| (bound.trait_ref.clone(), definition.span))
            })
            .collect();
        for (reference, span) in references {
            self.check_generic_bounds(reference.definition, &reference.arguments, span);
        }
        for index in 0..self.program.implementations.len() {
            let implementation = self.program.implementations[index].clone();
            let Some(reference) = implementation.trait_ref else {
                continue;
            };
            let span = self.definition(implementation.definition).span;
            self.check_generic_bounds(reference.definition, &reference.arguments, span);
            let parents = match model::supertraits(&mut self.program, &reference) {
                Ok(parents) => parents,
                Err(error) => {
                    self.error("E-TRAIT-SUPER", error.to_string(), span);
                    continue;
                }
            };
            for parent in parents.into_iter().skip(1) {
                if let Err(error) =
                    model::require_trait(&mut self.program, implementation.target, &parent)
                {
                    self.error("E-TRAIT-SUPER", error.to_string(), span);
                }
            }
        }
    }

    fn reject_supertrait_cycles(&mut self) {
        let indices: HashMap<_, _> = self
            .program
            .traits
            .iter()
            .enumerate()
            .map(|(index, trait_)| (trait_.definition, index))
            .collect();
        let edges: Vec<Vec<usize>> = self
            .program
            .traits
            .iter()
            .map(|trait_| {
                trait_
                    .supertraits
                    .iter()
                    .filter_map(|parent| indices.get(&parent.definition).copied())
                    .collect()
            })
            .collect();
        for component in crate::graph::components(&edges) {
            if component.len() > 1 || edges[component[0]].contains(&component[0]) {
                let definition = self.program.traits[component[0]].definition;
                self.error(
                    "E-TRAIT-CYCLE",
                    "supertrait requirements form a cycle",
                    self.definition(definition).span,
                );
            }
        }
    }

    fn collect_trait_bounds(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let (Some(owner), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            let generics = match &item.kind {
                ItemKind::Function(function) => &function.generics,
                ItemKind::Record { generics, .. }
                | ItemKind::Enum { generics, .. }
                | ItemKind::TypeAlias { generics, .. }
                | ItemKind::Trait { generics, .. }
                | ItemKind::Impl { generics, .. }
                | ItemKind::Contract { generics, .. } => generics,
                _ => continue,
            };
            let parameters = self.parameters(owner);
            if let ItemKind::Trait { bounds, .. } = &item.kind {
                let references: Vec<_> = bounds
                    .iter()
                    .filter_map(|&bound| self.trait_reference(bound, module, owner, &parameters))
                    .collect();
                if let Some(&slot) = self.trait_state.trait_indices.get(&owner) {
                    self.program.traits[slot].supertraits = references;
                }
            }
            for generic in generics {
                self.collect_parameter_bounds(owner, module, generic, &parameters);
            }
        }
        self.inherit_method_bounds();
        self.inherit_trait_bounds();
    }

    fn collect_parameter_bounds(
        &mut self,
        owner: DefId,
        module: ModuleId,
        generic: &GenericParam,
        parameters: &HashMap<Symbol, TyId>,
    ) {
        let GenericParam::Type { name, bounds } = generic else {
            return;
        };
        let Some(Ty::Parameter { index, .. }) = parameters
            .get(&name.symbol)
            .map(|ty| self.program.types.get(*ty))
        else {
            return;
        };
        let parameter = *index;
        for &bound in bounds {
            if let Some(trait_ref) = self.trait_reference(bound, module, owner, parameters) {
                self.program.definitions[owner.0 as usize]
                    .bounds
                    .push(model::TraitBound {
                        parameter,
                        trait_ref,
                    });
            }
        }
    }

    fn inherit_method_bounds(&mut self) {
        let mut owners: Vec<_> = self
            .trait_state
            .method_owners
            .iter()
            .map(|(&method, &owner)| (method, owner))
            .collect();
        owners.sort_unstable_by_key(|(method, _)| method.0);
        for (method, owner) in owners {
            let arguments = self.program.types.generic_arguments(method);
            let bounds = self.definition(owner).bounds.clone();
            for mut bound in bounds {
                for argument in &mut bound.trait_ref.arguments {
                    match self
                        .program
                        .types
                        .substitute_arg(*argument, owner, &arguments)
                    {
                        Ok(value) => *argument = value,
                        Err(error) => self.error(
                            "E-TRAIT-BOUND",
                            error.to_string(),
                            self.definition(method).span,
                        ),
                    }
                }
                self.program.definitions[method.0 as usize]
                    .bounds
                    .push(bound);
            }
        }
    }

    fn inherit_trait_bounds(&mut self) {
        for index in 0..self.program.traits.len() {
            let trait_ = self.program.traits[index].clone();
            let trait_bounds = self.definition(trait_.definition).bounds.clone();
            for method in trait_.methods {
                let arguments = self.program.types.generic_arguments(method.definition);
                let inherited = &arguments[1..method.inherited_parameters as usize];
                self.program.definitions[method.definition.0 as usize]
                    .bounds
                    .push(model::TraitBound {
                        parameter: 0,
                        trait_ref: model::TraitRef {
                            definition: trait_.definition,
                            arguments: inherited.to_vec(),
                        },
                    });
                for mut bound in trait_bounds.clone() {
                    bound.parameter += 1;
                    for argument in &mut bound.trait_ref.arguments {
                        match self.program.types.substitute_arg(
                            *argument,
                            trait_.definition,
                            inherited,
                        ) {
                            Ok(value) => *argument = value,
                            Err(error) => self.error(
                                "E-TRAIT-BOUND",
                                error.to_string(),
                                self.definition(method.definition).span,
                            ),
                        }
                    }
                    self.program.definitions[method.definition.0 as usize]
                        .bounds
                        .push(bound);
                }
            }
        }
    }

    fn validate_language_roles(&mut self) {
        let mut roles = HashSet::new();
        for index in 0..self.program.traits.len() {
            let trait_ = self.program.traits[index].clone();
            let Some(role) = trait_.language_item else {
                continue;
            };
            let span = self.definition(trait_.definition).span;
            if !roles.insert(role) {
                self.error(
                    "E-LANG-ITEM",
                    "duplicate declaration of a language trait role",
                    span,
                );
            }
            self.validate_language_role(&trait_, role);
        }
    }

    fn validate_language_role(&mut self, trait_: &model::Trait, role: model::LanguageItem) {
        let span = self.definition(trait_.definition).span;
        if role == model::LanguageItem::Copy {
            if !trait_.methods.is_empty()
                || !trait_.supertraits.is_empty()
                || !self
                    .definition(trait_.definition)
                    .generic_parameter_kinds
                    .is_empty()
            {
                self.error(
                    "E-LANG-ITEM",
                    "Copy is a marker trait without methods or generic parameters",
                    span,
                );
            }
            return;
        }
        if trait_.methods.len() != 1 {
            self.error(
                "E-LANG-ITEM",
                "a language trait must declare exactly one method",
                span,
            );
            return;
        }
        let valid = self.language_signature_valid(&trait_.methods[0], role);
        if !valid {
            self.error(
                "E-LANG-ITEM",
                "language trait has an invalid generic or method signature",
                span,
            );
        }
    }

    fn language_signature_valid(
        &self,
        method: &model::TraitMethod,
        role: model::LanguageItem,
    ) -> bool {
        let Ty::Function { parameters, result } = self
            .program
            .types
            .get(self.definition(method.definition).ty)
        else {
            return false;
        };
        let self_ty = self
            .program
            .types
            .values()
            .iter()
            .position(
                |ty| matches!(ty, Ty::Parameter { owner, index: 0 } if *owner == method.definition),
            )
            .map(|index| TyId(index as u32));
        match role {
            model::LanguageItem::Copy => unreachable!("marker handled above"),
            model::LanguageItem::Drop => {
                self.valid_drop_signature(method, parameters, *result, self_ty)
            }
            model::LanguageItem::From => {
                self.valid_from_signature(method, parameters, *result, self_ty)
            }
            model::LanguageItem::Fn | model::LanguageItem::FnMut | model::LanguageItem::FnOnce => {
                self.valid_fn_signature(role, parameters, self_ty)
                    && self.definition(method.definition).generic_parameter_kinds
                        [method.inherited_parameters as usize..]
                        .iter()
                        .all(|kind| *kind == GenericParamKind::Lifetime)
            }
        }
    }

    fn valid_drop_signature(
        &self,
        method: &model::TraitMethod,
        parameters: &[TyId],
        result: TyId,
        self_ty: Option<TyId>,
    ) -> bool {
        method.inherited_parameters == 1
            && self
                .definition(method.definition)
                .generic_parameter_kinds
                .len()
                == 1
            && parameters.len() == 1
            && result == TyId::VOID
            && matches!(self.program.types.get(parameters[0]), Ty::Reference { mutable: true, inner, .. } if Some(*inner) == self_ty)
            && self
                .definition(method.definition)
                .declaration_clauses
                .is_empty()
    }

    fn valid_from_signature(
        &self,
        method: &model::TraitMethod,
        parameters: &[TyId],
        result: TyId,
        self_ty: Option<TyId>,
    ) -> bool {
        method.inherited_parameters == 2
            && self.definition(method.definition).generic_parameter_kinds
                == [GenericParamKind::Type, GenericParamKind::Type]
            && parameters.len() == 1
            && Some(result) == self_ty
            && matches!(self.program.types.get(parameters[0]), Ty::Parameter { owner, index: 1 } if *owner == method.definition)
    }

    fn valid_fn_signature(
        &self,
        role: model::LanguageItem,
        parameters: &[TyId],
        self_ty: Option<TyId>,
    ) -> bool {
        let Some(receiver) = parameters.first() else {
            return false;
        };
        match role {
            model::LanguageItem::Fn => {
                matches!(self.program.types.get(*receiver), Ty::Reference { mutable: false, inner, .. } if Some(*inner) == self_ty)
            }
            model::LanguageItem::FnMut => {
                matches!(self.program.types.get(*receiver), Ty::Reference { mutable: true, inner, .. } if Some(*inner) == self_ty)
            }
            model::LanguageItem::FnOnce => Some(*receiver) == self_ty,
            _ => false,
        }
    }

    fn validate_implementation(&mut self, index: usize) {
        let implementation = self.program.implementations[index].clone();
        let Some(reference) = &implementation.trait_ref else {
            return;
        };
        let Some(&trait_index) = self.trait_state.trait_indices.get(&reference.definition) else {
            return;
        };
        let trait_ = self.program.traits[trait_index].clone();
        for method in &trait_.methods {
            self.validate_impl_method(index, &implementation, method);
        }
        for method in &implementation.methods {
            let name = self.definition(method.implementation).name;
            if !trait_
                .methods
                .iter()
                .any(|method| self.definition(method.definition).name == name)
            {
                self.error(
                    "E-IMPL-METHOD",
                    "implementation declares a method outside its trait",
                    self.definition(method.implementation).span,
                );
            }
        }
        if trait_.language_item == Some(model::LanguageItem::Drop) {
            self.validate_drop_target(&implementation);
        }
        if trait_.language_item == Some(model::LanguageItem::Copy)
            && !self.is_copy_type(implementation.target)
        {
            self.error(
                "E-COPY-IMPL",
                "Copy cannot be implemented for a type with non-Copy fields or a destructor",
                self.definition(implementation.definition).span,
            );
        }
    }

    fn validate_impl_method(
        &mut self,
        index: usize,
        implementation: &model::Impl,
        declaration: &model::TraitMethod,
    ) {
        let Some(method) = self.bind_impl_method(index, implementation, declaration) else {
            return;
        };
        let inherited = self
            .definition(implementation.definition)
            .generic_parameter_kinds
            .len();
        let arguments = self.program.types.generic_arguments(method);
        let target = self.program.types.substitute_generics(
            implementation.target,
            implementation.definition,
            &arguments,
        );
        let Ok(target) = target else {
            self.error(
                "E-IMPL-SIGNATURE",
                "implementation Self substitution failed",
                self.definition(method).span,
            );
            return;
        };
        let mut expected_arguments = vec![GenericArg::Type(target)];
        for argument in &implementation
            .trait_ref
            .as_ref()
            .expect("trait implementation")
            .arguments
        {
            match self.program.types.substitute_arg(
                *argument,
                implementation.definition,
                &arguments,
            ) {
                Ok(argument) => expected_arguments.push(argument),
                Err(error) => {
                    self.error(
                        "E-IMPL-SIGNATURE",
                        error.to_string(),
                        self.definition(method).span,
                    );
                    return;
                }
            }
        }
        expected_arguments.extend_from_slice(&arguments[inherited..]);
        self.compare_method_signature(declaration.definition, method, &expected_arguments);
    }

    fn bind_impl_method(
        &mut self,
        index: usize,
        implementation: &model::Impl,
        declaration: &model::TraitMethod,
    ) -> Option<DefId> {
        let name = self.definition(declaration.definition).name;
        let Some((slot, method)) = implementation
            .methods
            .iter()
            .enumerate()
            .find(|(_, method)| self.definition(method.implementation).name == name)
        else {
            if declaration.has_default {
                self.program.implementations[index]
                    .methods
                    .push(model::ImplMethod {
                        declaration: Some(declaration.definition),
                        implementation: declaration.definition,
                    });
                return None;
            }
            self.error(
                "E-IMPL-MISSING",
                "implementation is missing a required method",
                self.definition(implementation.definition).span,
            );
            return None;
        };
        let method = method.implementation;
        self.program.implementations[index].methods[slot].declaration =
            Some(declaration.definition);
        self.program.definitions[method.0 as usize].visibility =
            self.definition(declaration.definition).visibility;
        Some(method)
    }

    fn compare_method_signature(
        &mut self,
        declaration: DefId,
        implementation: DefId,
        arguments: &[GenericArg],
    ) {
        if self.definition(declaration).generic_parameter_kinds.len() != arguments.len() {
            self.error(
                "E-IMPL-SIGNATURE",
                "method generic parameter count differs from its trait declaration",
                self.definition(implementation).span,
            );
            return;
        }
        let expected = self.program.types.substitute_generics(
            self.definition(declaration).ty,
            declaration,
            arguments,
        );
        let actual = self.definition(implementation).ty;
        // Elided receiver lifetimes are universally callable on both sides.
        // Compare their closed binders, retaining all explicit relationships.
        let actual = self
            .program
            .types
            .generalize_callable(actual, implementation);
        let expected = expected
            .ok()
            .and_then(|ty| self.program.types.generalize_callable(ty, implementation));
        if !actual
            .zip(expected)
            .is_some_and(|(actual, expected)| self.program.types.compatible(actual, expected))
        {
            self.error(
                "E-IMPL-SIGNATURE",
                "method signature does not satisfy its trait declaration",
                self.definition(implementation).span,
            );
        }
        if self.definition(declaration).declaration_clauses
            != self.definition(implementation).declaration_clauses
            && !self.definition(declaration).declaration_clauses.is_empty()
        {
            self.error(
                "E-IMPL-CONTRACT",
                "trait method contract refinement is not established",
                self.definition(implementation).span,
            );
        }
        let required = self.definition(declaration).attributes.clone();
        for attribute in required {
            if !self.program.definitions[implementation.0 as usize]
                .attributes
                .iter()
                .any(|present| {
                    present.name == attribute.name && present.arguments == attribute.arguments
                })
            {
                self.program.definitions[implementation.0 as usize]
                    .attributes
                    .push(attribute);
            }
        }
    }

    fn validate_dynamic_types(&mut self) {
        let objects: Vec<_> = self
            .program
            .types
            .values()
            .iter()
            .filter_map(|ty| match ty {
                Ty::Dynamic {
                    trait_definition, ..
                } => Some(*trait_definition),
                _ => None,
            })
            .collect();
        for definition in objects {
            self.validate_object_safety(definition);
        }
    }

    pub(in crate::sema) fn validate_object_safety(&mut self, definition: DefId) {
        let mut pending = vec![definition];
        let mut seen = HashSet::new();
        while let Some(definition) = pending.pop() {
            if !seen.insert(definition) {
                continue;
            }
            if seen.len() > 4096 {
                self.error(
                    "E-TRAIT-OBJECT",
                    "dyn supertrait traversal exceeds its limit",
                    self.definition(definition).span,
                );
                return;
            }
            let Some(&index) = self.trait_state.trait_indices.get(&definition) else {
                continue;
            };
            pending.extend(
                self.program.traits[index]
                    .supertraits
                    .iter()
                    .map(|parent| parent.definition),
            );
            self.validate_object_methods(index);
        }
    }

    fn validate_object_methods(&mut self, index: usize) {
        let methods = self.program.traits[index].methods.clone();
        for method in methods {
            if self.definition(method.definition).ty == TyId::ERROR {
                continue;
            }
            let self_ty = self.program.types.intern(Ty::Parameter {
                owner: method.definition,
                index: 0,
            });
            let method = dynamic::ObjectMethod {
                definition: method.definition,
                self_ty,
                inherited_parameters: method.inherited_parameters,
            };
            if let Err(error) = dynamic::object_safe_method(&self.program, method) {
                self.error("E-TRAIT-OBJECT", error.message, error.span);
            }
        }
    }
}
