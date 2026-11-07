use super::*;

impl Context<'_> {
    pub(in crate::sema) fn collect_implementation(
        &mut self,
        item_id: ast::ItemId,
        module: ModuleId,
    ) {
        let item = self.ast.item(item_id);
        let ItemKind::Impl {
            target,
            trait_type,
            generics,
            trusted_reason,
            negative,
            ..
        } = &item.kind
        else {
            return;
        };
        let Some(name) = target_name(self.ast, *target)
            .or_else(|| trait_type.and_then(|ty| target_name(self.ast, ty)))
        else {
            self.error(
                "E-IMPL-TARGET",
                "implementation target must have a named root",
                item.span,
            );
            return;
        };
        let owner = self.add_definition(name, module, D::Impl, item.visibility, None);
        if let Some(reason) = trusted_reason {
            let span = self.ast.expr(*reason).span;
            let text = self.sources.file(span.file).slice(span);
            if let (_, hir::Constant::String(reason)) = literal::check(
                text,
                ast::LiteralKind::String,
                None,
                false,
                span,
                &mut self.program.types,
                self.diagnostics,
            ) {
                if reason.trim().is_empty() || reason.len() > 4096 {
                    self.error(
                        "E-IMPL-TRUST",
                        "contract impl requires a non-empty justification of at most 4096 UTF-8 bytes",
                        span,
                    );
                } else {
                    self.program.tasks.trusted.insert(owner, reason.into());
                }
            }
        }
        self.item_definitions[item_id.0 as usize] = Some(owner);
        self.program.definitions[owner].ty = TyId::VOID;
        self.program.modules[module].definitions.push(owner);
        self.collect_generic_parameters(owner, generics, true);
        self.trait_state
            .impl_indices
            .insert(owner, self.program.implementations.len());
        self.program.implementations.push(model::Impl {
            negative: *negative,
            definition: owner,
            target: TyId::ERROR,
            trait_ref: None,
            methods: Vec::new(),
        });
    }

    pub(in crate::sema) fn collect_trait_members(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let (Some(owner), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            match &item.kind {
                ItemKind::Trait {
                    generics, methods, ..
                } => self.collect_trait(owner, module, generics, methods),
                ItemKind::Impl {
                    generics, methods, ..
                } => self.collect_impl_methods(owner, module, generics, methods),
                _ => {}
            }
        }
    }

    fn collect_trait(
        &mut self,
        owner: DefId,
        module: ModuleId,
        generics: &[GenericParam],
        methods: &[ast::ItemId],
    ) {
        let role = self.language_item(owner);
        let mut definitions = Vec::new();
        let mut names = HashSet::new();
        for &item in methods {
            let Some(method) = self.collect_method(item, module, generics, Some(owner)) else {
                continue;
            };
            self.program.definitions[method].visibility = self.definition(owner).visibility;
            if !names.insert(self.definition(method).name) {
                self.error(
                    "E-TRAIT-METHOD",
                    "duplicate trait method",
                    self.definition(method).span,
                );
            }
            definitions.push(model::TraitMethod {
                definition: method,
                inherited_parameters: generics.len() as u32 + 1,
                has_default: matches!(&self.ast.item(item).kind, ItemKind::Function(function) if function.body.is_some()),
            });
        }
        self.trait_state
            .trait_indices
            .insert(owner, self.program.traits.len());
        self.program.traits.push(model::Trait {
            definition: owner,
            methods: definitions,
            language_item: role,
            supertraits: Vec::new(),
        });
    }

    fn collect_impl_methods(
        &mut self,
        owner: DefId,
        module: ModuleId,
        generics: &[GenericParam],
        methods: &[ast::ItemId],
    ) {
        let Some(&index) = self.trait_state.impl_indices.get(&owner) else {
            return;
        };
        let mut names = HashSet::new();
        for &item in methods {
            if matches!(&self.ast.item(item).kind, ItemKind::Function(function) if function.body.is_none())
                && !self
                    .ast
                    .item(item)
                    .attributes
                    .iter()
                    .any(|attribute| self.symbols.get(attribute.name.symbol) == "intrinsic")
                && !self
                    .verified_modules
                    .get(&self.ast.item(item).span.file)
                    .is_some_and(|proof| {
                        self.ast
                            .item(item)
                            .name
                            .is_some_and(|name| proof.certified_offsets.contains(&name.span.start))
                    })
            {
                self.error(
                    "E-IMPL-BODY",
                    "implementation methods require an executable body",
                    self.ast.item(item).span,
                );
            }
            let Some(method) = self.collect_method(item, module, generics, None) else {
                continue;
            };
            if !names.insert(self.definition(method).name) {
                self.error(
                    "E-IMPL-METHOD",
                    "duplicate implementation method",
                    self.definition(method).span,
                );
            }
            self.trait_state.method_owners.insert(method, owner);
            self.program.implementations[index]
                .methods
                .push(model::ImplMethod {
                    declaration: None,
                    implementation: method,
                });
        }
    }

    fn collect_method(
        &mut self,
        item_id: ast::ItemId,
        module: ModuleId,
        inherited: &[GenericParam],
        trait_owner: Option<DefId>,
    ) -> Option<DefId> {
        let item = self.ast.item(item_id);
        let ItemKind::Function(function) = &item.kind else {
            self.error(
                "E-TRAIT-METHOD",
                "trait and impl members must be functions",
                item.span,
            );
            return None;
        };
        let name = item.name?;
        let method = self.add_definition(name, module, D::Function, item.visibility, None);
        self.item_definitions[item_id.0 as usize] = Some(method);
        self.item_modules[item_id.0 as usize] = Some(module);
        self.program.modules[module].definitions.push(method);
        let mut generics = Vec::new();
        if let Some(owner) = trait_owner {
            let symbol = self
                .symbols
                .lookup("Self")
                .unwrap_or(self.definition(owner).name);
            generics.push(GenericParam::Type {
                name: Name {
                    symbol,
                    span: item.span,
                },
                bounds: Vec::new(),
            });
        }
        generics.extend(inherited.iter().map(clone_generic));
        generics.extend(function.generics.iter().map(clone_generic));
        self.collect_generic_parameters(method, &generics, true);
        self.copy_method_contract(method, item);
        Some(method)
    }

    fn copy_method_contract(&mut self, definition: DefId, item: &ast::Item) {
        let target = &mut self.program.definitions[definition];
        target.attributes = item
            .attributes
            .iter()
            .map(|attribute| hir::Attribute {
                constant: None,
                name: attribute.name.symbol,
                arguments: attribute.arguments.clone(),
                span: attribute.span,
            })
            .collect();
        if let ItemKind::Function(function) = &item.kind {
            target.const_origin = function.constant.then_some(definition);
            target.declaration_clauses = function
                .clauses
                .iter()
                .map(|clause| (clause.kind, self.ast.expr(clause.predicate).span))
                .collect();
        }
    }

    fn language_item(&mut self, definition: DefId) -> Option<model::LanguageItem> {
        let mut role = None;
        for attribute in &self.definition(definition).attributes {
            if self.symbols.get(attribute.name) != "lang" {
                continue;
            }
            if role.is_some() || attribute.arguments.len() != 1 {
                self.error(
                    "E-LANG-ITEM",
                    "a language item requires exactly one role",
                    attribute.span,
                );
                return None;
            }
            let token = &attribute.arguments[0];
            let text = self.sources.file(token.span.file).slice(token.span);
            role = match text {
                "copy" => Some(model::LanguageItem::Copy),
                "send" => Some(model::LanguageItem::Send),
                "sync" => Some(model::LanguageItem::Sync),
                "task_transfer" => Some(model::LanguageItem::TaskTransfer),
                "suspend_safe" => Some(model::LanguageItem::SuspendSafe),
                "drop" => Some(model::LanguageItem::Drop),
                "from" => Some(model::LanguageItem::From),
                "fn" => Some(model::LanguageItem::Fn),
                "fn_mut" => Some(model::LanguageItem::FnMut),
                "fn_once" => Some(model::LanguageItem::FnOnce),
                _ => {
                    self.error("E-LANG-ITEM", "unknown trait language role", attribute.span);
                    return None;
                }
            };
        }
        role
    }
}

fn target_name(ast: &Ast, target: ast::TypeId) -> Option<Name> {
    match &ast.ty(target).kind {
        TypeKind::Path { path, .. } => path.last().copied(),
        TypeKind::Reference { inner, .. }
        | TypeKind::Array { inner, .. }
        | TypeKind::Slice(inner) => target_name(ast, *inner),
        _ => None,
    }
}
