use super::*;
use crate::{
    hir::traits::{self as model, TraitRef},
    types::GenericArg,
};

impl Body<'_, '_> {
    pub(super) fn associated_call(
        &mut self,
        callee: ast::ExprId,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        expected: Option<TyId>,
        span: Span,
    ) -> Option<ExprId> {
        let A::Path(path) = &self.context.ast.expr(callee).kind else {
            return None;
        };
        if path.len() < 2 || self.find_local(path[0].symbol).is_some() {
            return None;
        }
        let (name, prefix) = path.split_last()?;
        let mut target = self.associated_type(prefix)?;
        if let Ty::Named { definition, .. } = self.type_kind(target)
            && self
                .context
                .variants
                .contains_key(&(*definition, name.symbol))
        {
            return None;
        }
        if let (Ty::Named { definition, .. }, Some(expected)) = (self.type_kind(target), expected)
            && matches!(self.type_kind(expected), Ty::Named { definition: found, .. } if found == definition)
        {
            target = expected;
        }
        let selection = self.select_method(target, *name)?;
        if self.context.is_drop_method(selection.definition) {
            self.context.error(
                "E-DROP-EXPLICIT",
                "destructors are invoked only by ownership cleanup",
                span,
            );
            return Some(self.add_expr(H::Error, TyId::ERROR, span));
        }
        let mut seeds = selection.type_arguments;
        if let Ty::Named { definition, .. } = self.type_kind(target)
            && self.context.definition(*definition).ty == target
            && prefix.len() == 1
            && !self.generic_types.contains_key(&prefix[0].symbol)
        {
            seeds.clear();
        } // Infer the nominal's arguments from values/result.
        let ty = self
            .context
            .program
            .types
            .generalize_callable(
                self.context.definition(selection.definition).ty,
                selection.definition,
            )
            .unwrap_or(TyId::ERROR);
        let callee = self.add_expr(H::Definition(selection.definition), ty, span);
        Some(self.call_resolved(
            ResolvedCall {
                callee,
                leading_arguments: Vec::new(),
                generic_arguments: seeds,
                prelude: Vec::new(),
            },
            explicit,
            arguments,
            expected,
            span,
        ))
    }

    fn associated_type(&mut self, path: &[ast::Name]) -> Option<TyId> {
        if path.len() == 1 {
            if let Some(&ty) = self.generic_types.get(&path[0].symbol) {
                return Some(ty);
            }
            if let Some(ty) = self
                .context
                .program
                .types
                .builtin(self.context.symbols.get(path[0].symbol))
            {
                return Some(ty);
            }
        }
        let definition = self.context.lookup(self.module, path)?;
        matches!(
            self.context.definition(definition).kind,
            hir::DefinitionKind::Record
                | hir::DefinitionKind::Union
                | hir::DefinitionKind::Enum
                | hir::DefinitionKind::TypeAlias
        )
        .then(|| self.context.definition(definition).ty)
    }

    pub(super) fn method_call(
        &mut self,
        callee: ast::ExprId,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        expected: Option<TyId>,
        span: Span,
    ) -> Option<ExprId> {
        let A::Field { base, name } = self.context.ast.expr(callee).kind else {
            return None;
        };
        if let A::Path(path) = &self.context.ast.expr(base).kind
            && !(path.len() == 1 && self.find_local(path[0].symbol).is_some())
            && self.context.is_namespace(self.module, path)
        {
            return None; // The field checker emits the source-backed :: fix.
        }
        let receiver = self.expression(base, None);
        let target = self.receiver_type(receiver);
        if let Some(field) = self.callable_field(receiver, target, name) {
            let target = ResolvedCall {
                callee: field,
                leading_arguments: Vec::new(),
                generic_arguments: Vec::new(),
                prelude: Vec::new(),
            };
            return Some(self.call_resolved(target, explicit, arguments, expected, span));
        }
        if matches!(self.type_kind(target), Ty::Dynamic { .. }) {
            return Some(self.dynamic_call(receiver, target, name, explicit, arguments, span));
        }
        let Some(target) = self.static_method_target(receiver, target, name, span) else {
            return Some(self.add_expr(H::Error, TyId::ERROR, span));
        };
        Some(self.call_resolved(target, explicit, arguments, expected, span))
    }

    fn static_method_target(
        &mut self,
        receiver: ExprId,
        target: TyId,
        name: ast::Name,
        span: Span,
    ) -> Option<ResolvedCall> {
        let selection = self.select_method(target, name)?;
        if self.context.is_drop_method(selection.definition) {
            self.context.error(
                "E-DROP-EXPLICIT",
                "destructors are invoked only by ownership cleanup",
                span,
            );
            return None;
        }
        let formal = self.receiver_formal(&selection, span)?;
        let (receiver, prelude) = self.receiver_storage(receiver, formal, name, span);
        let receiver = if matches!(
            self.context
                .program
                .contracts
                .intrinsics
                .get(&selection.definition),
            Some(crate::contracts::Intrinsic::TaskJoin | crate::contracts::Intrinsic::TaskIgnore)
        ) {
            self.add_expr(
                H::Unary {
                    op: U::Move,
                    operand: receiver,
                },
                self.ty(receiver),
                span,
            )
        } else {
            receiver
        };
        let receiver = self.method_receiver(receiver, formal, span);
        let ty = self
            .context
            .program
            .types
            .generalize_callable(
                self.context.definition(selection.definition).ty,
                selection.definition,
            )
            .unwrap_or(TyId::ERROR);
        let callee = self.add_expr(H::Definition(selection.definition), ty, span);
        Some(ResolvedCall {
            callee,
            leading_arguments: vec![receiver],
            generic_arguments: selection.type_arguments,
            prelude,
        })
    }

    pub(super) fn trait_callable_target(
        &mut self,
        callee: ExprId,
        span: Span,
    ) -> Option<ResolvedCall> {
        let target = self.receiver_type(callee);
        let (role, selection) = self.callable_trait_selection(target)?;
        if role == model::LanguageItem::FnOnce
            && self.method_place(callee)
            && !self.context.is_copy_type(target)
        {
            self.context.error(
                "E-MOVE-EXPLICIT",
                "calling a stored FnOnce value requires an explicit move",
                span,
            );
            return Some(ResolvedCall {
                callee: self.add_expr(H::Error, TyId::ERROR, span),
                leading_arguments: Vec::new(),
                generic_arguments: Vec::new(),
                prelude: Vec::new(),
            });
        }
        let formal = self.receiver_formal(&selection, span)?;
        let receiver = self.method_receiver(callee, formal, span);
        let ty = self
            .context
            .program
            .types
            .generalize_callable(
                self.context.definition(selection.definition).ty,
                selection.definition,
            )
            .unwrap_or(TyId::ERROR);
        let callee = self.add_expr(H::Definition(selection.definition), ty, span);
        Some(ResolvedCall {
            callee,
            leading_arguments: vec![receiver],
            generic_arguments: selection.type_arguments,
            prelude: Vec::new(),
        })
    }

    fn callable_trait_selection(
        &self,
        target: TyId,
    ) -> Option<(model::LanguageItem, model::MethodSelection)> {
        let Ty::Parameter { owner, index } = *self.type_kind(target) else {
            return None;
        };
        let bounds = &self.context.definition(owner).bounds;
        for role in [
            model::LanguageItem::Fn,
            model::LanguageItem::FnMut,
            model::LanguageItem::FnOnce,
        ] {
            for bound in bounds.iter().filter(|bound| bound.parameter == index) {
                let Some(trait_) = self.context.program.traits.iter().find(|trait_| {
                    trait_.definition == bound.trait_ref.definition
                        && trait_.language_item == Some(role)
                }) else {
                    continue;
                };
                let method = trait_.methods.first()?.definition;
                let mut arguments = vec![GenericArg::Type(target)];
                arguments.extend_from_slice(&bound.trait_ref.arguments);
                return Some((
                    role,
                    model::MethodSelection {
                        definition: method,
                        type_arguments: arguments,
                    },
                ));
            }
        }
        None
    }

    fn receiver_storage(
        &mut self,
        value: ExprId,
        formal: TyId,
        name: ast::Name,
        span: Span,
    ) -> (ExprId, Vec<StmtId>) {
        if !matches!(self.type_kind(formal), Ty::Reference { .. })
            || matches!(self.type_kind(self.ty(value)), Ty::Reference { .. })
            || self.method_place(value)
        {
            return (value, Vec::new());
        }
        let ty = self.ty(value);
        let local = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(hir::Local {
            name: name.symbol,
            ty,
            mutable: true,
            span,
        });
        self.states.push(Init::Initialized);
        let statement = self.add_stmt(
            S::Declare {
                local,
                initializer: Some(value),
            },
            span,
        );
        (self.add_expr(H::Local(local), ty, span), vec![statement])
    }

    fn method_place(&self, mut value: ExprId) -> bool {
        for _ in 0..128 {
            match self.expr(value).kind {
                H::Group(inner) => value = inner,
                H::Local(_)
                | H::Field { .. }
                | H::Index { .. }
                | H::Unary {
                    op: U::Dereference, ..
                } => return true,
                _ => return false,
            }
        }
        false
    }

    fn receiver_type(&self, value: ExprId) -> TyId {
        match self.type_kind(self.ty(value)) {
            Ty::Reference { inner, .. } => *inner,
            _ => self.ty(value),
        }
    }

    fn receiver_formal(&mut self, selection: &model::MethodSelection, span: Span) -> Option<TyId> {
        let signature = self.context.definition(selection.definition).ty;
        let Ty::Function { parameters, .. } = self.type_kind(signature) else {
            return None;
        };
        let Some(&formal) = parameters.first() else {
            self.context.error(
                "E-METHOD-RECEIVER",
                "an associated function without a receiver must use ::",
                span,
            );
            return None;
        };
        let (inner, mutable) = match *self.type_kind(formal) {
            Ty::Reference { inner, mutable, .. } => (inner, Some(mutable)),
            _ => (formal, None),
        };
        let inner = match self.context.program.types.substitute_generics(
            inner,
            selection.definition,
            &selection.type_arguments,
        ) {
            Ok(inner) => inner,
            Err(error) => {
                self.context
                    .error("E-METHOD-RECEIVER", error.to_string(), span);
                return None;
            }
        };
        Some(match mutable {
            Some(mutable) => {
                let region = self.context.program.types.fresh_region();
                self.context.program.types.intern(Ty::Reference {
                    region,
                    mutable,
                    inner,
                })
            }
            None => inner,
        })
    }

    fn callable_field(&mut self, value: ExprId, ty: TyId, name: ast::Name) -> Option<ExprId> {
        let Ty::Named {
            definition,
            arguments,
        } = self.type_kind(ty).clone()
        else {
            return None;
        };
        let record = self
            .context
            .program
            .records
            .iter()
            .find(|record| record.definition == definition)?;
        let (index, field) = record
            .fields
            .iter()
            .enumerate()
            .find(|(_, field)| field.name == name.symbol)?;
        let (field_ty, visibility, field_span) = (field.ty, field.visibility, field.span);
        if !self
            .context
            .field_visible(definition, visibility, self.module)
        {
            self.context
                .error("E-NAME-PRIVATE", "this field is private", field_span);
        }
        let ty = self
            .context
            .program
            .types
            .substitute_generics(field_ty, definition, &arguments)
            .unwrap_or(TyId::ERROR);
        Some(self.add_expr(
            H::Field {
                base: value,
                index: index as u32,
            },
            ty,
            name.span,
        ))
    }

    fn select_method(&mut self, target: TyId, name: ast::Name) -> Option<model::MethodSelection> {
        let mut selections = self.bound_methods(target, name.symbol);
        if selections.is_empty() {
            selections = self.concrete_methods(target, name);
        }
        if selections.len() != 1 {
            self.context.error(
                "E-METHOD-SELECTION",
                if selections.is_empty() {
                    "no method is established for this receiver type"
                } else {
                    "method call is ambiguous between implementations"
                },
                name.span,
            );
            return None;
        }
        let selected = selections.pop().expect("one candidate");
        let declaration = self.context.definition(selected.definition);
        if !self
            .context
            .visible(declaration.visibility, declaration.module, self.module)
        {
            self.context
                .error("E-NAME-PRIVATE", "this method is private", name.span);
            return None;
        }
        Some(selected)
    }

    fn concrete_methods(&mut self, target: TyId, name: ast::Name) -> Vec<model::MethodSelection> {
        let mut found = Vec::new();
        for index in 0..self.context.program.implementations.len() {
            let implementation = &self.context.program.implementations[index];
            let mut matcher = model::Matcher::new(&self.context.program, implementation.definition);
            let matched = match matcher.ty(implementation.target, target, 0) {
                Ok(matched) => matched,
                Err(error) => {
                    self.context
                        .error("E-TRAIT-SELECTION", error.to_string(), name.span);
                    return Vec::new();
                }
            };
            if !matched {
                continue;
            }
            let Some(arguments) = matcher.complete() else {
                continue;
            };
            let methods: Vec<_> = implementation
                .methods
                .iter()
                .filter(|method| self.context.definition(method.implementation).name == name.symbol)
                .map(|method| {
                    (
                        method.implementation,
                        method.declaration == Some(method.implementation),
                    )
                })
                .collect();
            for (definition, default) in methods {
                let type_arguments = if default {
                    match self.default_method_arguments(index, target, &arguments, name.span) {
                        Some(arguments) => arguments,
                        None => continue,
                    }
                } else {
                    arguments.clone()
                };
                found.push(model::MethodSelection {
                    definition,
                    type_arguments,
                });
            }
        }
        found
    }

    fn default_method_arguments(
        &mut self,
        index: usize,
        target: TyId,
        arguments: &[GenericArg],
        span: Span,
    ) -> Option<Vec<GenericArg>> {
        let implementation = &self.context.program.implementations[index];
        let owner = implementation.definition;
        let trait_arguments = implementation.trait_ref.as_ref()?.arguments.clone();
        let mut inferred = vec![GenericArg::Type(target)];
        for argument in trait_arguments {
            match self
                .context
                .program
                .types
                .substitute_arg(argument, owner, arguments)
            {
                Ok(argument) => inferred.push(argument),
                Err(error) => {
                    self.context
                        .error("E-TRAIT-SELECTION", error.to_string(), span);
                    return None;
                }
            }
        }
        Some(inferred)
    }

    fn bound_methods(&mut self, target: TyId, name: Symbol) -> Vec<model::MethodSelection> {
        let Ty::Parameter { owner, index } = *self.type_kind(target) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        let bounds = self.context.definition(owner).bounds.clone();
        for bound in bounds {
            if bound.parameter != index {
                continue;
            }
            let Ok(references) = model::supertraits(&mut self.context.program, &bound.trait_ref)
            else {
                continue;
            };
            for reference in references {
                let Some(trait_) = self
                    .context
                    .program
                    .traits
                    .iter()
                    .find(|trait_| trait_.definition == reference.definition)
                else {
                    continue;
                };
                for method in &trait_.methods {
                    if self.context.definition(method.definition).name != name {
                        continue;
                    }
                    let mut arguments = vec![GenericArg::Type(target)];
                    arguments.extend_from_slice(&reference.arguments);
                    let selected = model::MethodSelection {
                        definition: method.definition,
                        type_arguments: arguments,
                    };
                    if !found.contains(&selected) {
                        found.push(selected);
                    }
                }
            }
        }
        found
    }

    fn method_receiver(&mut self, value: ExprId, formal: TyId, span: Span) -> ExprId {
        if let Ty::Reference { mutable, .. } = self.type_kind(formal) {
            let mutable = *mutable;
            let place = if let Ty::Reference { inner, .. } = self.type_kind(self.ty(value)) {
                self.add_expr(
                    H::Unary {
                        op: U::Dereference,
                        operand: value,
                    },
                    *inner,
                    span,
                )
            } else {
                value
            };
            if mutable && !self.mutable_place(place) {
                self.context.error(
                    "E-BORROW-MUTABLE",
                    "method requires a mutable receiver",
                    span,
                );
            }
            let inner = self.ty(place);
            let region = self.context.program.types.fresh_region();
            let ty = self.context.program.types.intern(Ty::Reference {
                region,
                mutable,
                inner,
            });
            return self.add_expr(
                H::Unary {
                    op: if mutable { U::BorrowMut } else { U::Borrow },
                    operand: place,
                },
                ty,
                span,
            );
        }
        self.add_expr(
            H::Unary {
                op: U::Move,
                operand: value,
            },
            self.ty(value),
            span,
        )
    }

    pub(super) fn coerce_dynamic(&mut self, mut value: ExprId, expected: TyId) -> Option<ExprId> {
        let (expected_mutable, reference) = self.dynamic_target(expected)?;
        let Ty::Reference { mutable, inner, .. } = self.type_kind(self.ty(value)).clone() else {
            return None;
        };
        if !mutable && expected_mutable {
            self.mismatch(self.ty(value), expected, self.expr(value).span);
            return Some(self.add_expr(H::Error, TyId::ERROR, self.expr(value).span));
        }
        if mutable && !expected_mutable {
            let span = self.expr(value).span;
            let place = self.add_expr(
                H::Unary {
                    op: U::Dereference,
                    operand: value,
                },
                inner,
                span,
            );
            let region = self.context.program.types.fresh_region();
            let ty = self.context.program.types.intern(Ty::Reference {
                region,
                mutable: false,
                inner,
            });
            value = self.add_expr(
                H::Unary {
                    op: U::Borrow,
                    operand: place,
                },
                ty,
                span,
            );
        }
        let table = super::super::traits::dynamic::plan_vtable(
            &mut self.context.program,
            &reference,
            inner,
        );
        match table {
            Ok(table) => {
                let vtable = self.context.program.vtables.len() as u32;
                self.context.program.vtables.push(table);
                Some(self.add_expr(
                    H::DynCoerce { value, vtable },
                    expected,
                    self.expr(value).span,
                ))
            }
            Err(error) => {
                self.context
                    .error("E-TRAIT-OBJECT", error.message, error.span);
                Some(self.add_expr(H::Error, TyId::ERROR, self.expr(value).span))
            }
        }
    }

    fn dynamic_target(&self, ty: TyId) -> Option<(bool, TraitRef)> {
        let Ty::Reference { mutable, inner, .. } = self.type_kind(ty) else {
            return None;
        };
        let Ty::Dynamic {
            trait_definition,
            arguments,
        } = self.type_kind(*inner)
        else {
            return None;
        };
        Some((
            *mutable,
            TraitRef {
                definition: *trait_definition,
                arguments: arguments.clone(),
            },
        ))
    }

    fn dynamic_call(
        &mut self,
        receiver: ExprId,
        target: TyId,
        name: ast::Name,
        explicit: &[ast::GenericArg],
        arguments: &[ast::ExprId],
        span: Span,
    ) -> ExprId {
        let Some((method, trait_arguments)) = self.dynamic_method(target, name) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        if self.context.is_drop_method(method) || !explicit.is_empty() {
            self.context.error(
                "E-TRAIT-OBJECT",
                "dynamic dispatch cannot invoke Drop or generic methods directly",
                span,
            );
            return self.add_expr(H::Error, TyId::ERROR, span);
        }
        let Some((parameters, result)) =
            self.dynamic_signature(target, method, trait_arguments, span)
        else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        if parameters.len() != arguments.len() + 1 {
            self.context.error(
                "E-CALL-ARITY",
                "dynamic method argument count differs from its declaration",
                span,
            );
        }
        let Some(&formal) = parameters.first() else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let receiver = self.method_receiver(receiver, formal, span);
        let mut checked = Vec::with_capacity(arguments.len());
        for (index, &argument) in arguments.iter().enumerate() {
            checked.push(self.expression(argument, parameters.get(index + 1).copied()));
        }
        self.add_expr(
            H::DynCall {
                receiver,
                trait_method: method,
                arguments: checked,
                parameter_types: parameters.into_iter().skip(1).collect(),
            },
            result,
            span,
        )
    }

    fn dynamic_method(
        &mut self,
        target: TyId,
        name: ast::Name,
    ) -> Option<(DefId, Vec<GenericArg>)> {
        let Ty::Dynamic {
            trait_definition,
            arguments,
        } = self.type_kind(target).clone()
        else {
            return None;
        };
        let reference = TraitRef {
            definition: trait_definition,
            arguments,
        };
        let references = match model::supertraits(&mut self.context.program, &reference) {
            Ok(references) => references,
            Err(error) => {
                self.context
                    .error("E-TRAIT-OBJECT", error.to_string(), name.span);
                return None;
            }
        };
        let mut found = None;
        for reference in references {
            let trait_ = self
                .context
                .program
                .traits
                .iter()
                .find(|trait_| trait_.definition == reference.definition)?;
            for method in &trait_.methods {
                if self.context.definition(method.definition).name == name.symbol
                    && found
                        .replace((method.definition, reference.arguments.clone()))
                        .is_some()
                {
                    self.context.error(
                        "E-METHOD-SELECTION",
                        "dynamic method is ambiguous between supertraits",
                        name.span,
                    );
                    return None;
                }
            }
        }
        if found.is_none() {
            self.context.error(
                "E-METHOD-SELECTION",
                "dynamic trait has no such method",
                name.span,
            );
        }
        found
    }

    fn dynamic_signature(
        &mut self,
        target: TyId,
        method: DefId,
        trait_arguments: Vec<GenericArg>,
        span: Span,
    ) -> Option<(Vec<TyId>, TyId)> {
        let mut arguments = vec![GenericArg::Type(target)];
        arguments.extend(trait_arguments);
        let kinds = self
            .context
            .definition(method)
            .generic_parameter_kinds
            .clone();
        for kind in &kinds[arguments.len()..] {
            if *kind != crate::types::GenericParamKind::Lifetime {
                self.context.error(
                    "E-TRAIT-OBJECT",
                    "dynamic method has an unresolved generic parameter",
                    span,
                );
                return None;
            }
            arguments.push(GenericArg::Lifetime(
                self.context.program.types.fresh_region(),
            ));
        }
        let signature = match self.context.program.types.substitute_generics(
            self.context.definition(method).ty,
            method,
            &arguments,
        ) {
            Ok(signature) => signature,
            Err(error) => {
                self.context
                    .error("E-TRAIT-OBJECT", error.to_string(), span);
                return None;
            }
        };
        let Ty::Function { parameters, result } = self.type_kind(signature).clone() else {
            return None;
        };
        Some((parameters, result))
    }
}
