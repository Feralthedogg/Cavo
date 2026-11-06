mod body;
mod const_generics;
mod constants;
mod layout;
mod literal;
mod moves;
pub(crate) use moves::{requires_execution_mir, validate as validate_moves};
mod attributes;
mod discriminants;
mod traits;
pub(crate) use discriminants::enum_discriminants;
pub(crate) use traits::validate_destructors;

use crate::{
    diagnostic::{Diagnostic, report},
    hir::{self, DefId, DefinitionKind as D, ModuleId},
    source::{SourceMap, Span},
    symbol::{Interner, Symbol},
    syntax::ast::{self, Ast, GenericParam, ItemKind, Name, TypeKind, Visibility},
    types::{Region, Ty, TyId, TypeContext},
};
use std::collections::{HashMap, HashSet};

pub fn check(
    ast: &Ast,
    sources: &SourceMap,
    symbols: &Interner,
    diagnostics: &mut Vec<Diagnostic>,
) -> hir::Program {
    let mut context = Context {
        ast,
        sources,
        symbols,
        diagnostics,
        program: hir::Program {
            constants: crate::ctfe::Program::default(),
            stage: hir::ValidationStage::Types,
            modules: Vec::new(),
            definitions: Vec::new(),
            types: TypeContext::new(),
            records: Vec::new(),
            enums: Vec::new(),
            functions: Vec::new(),
            closures: Vec::new(),
            traits: Vec::new(),
            implementations: Vec::new(),
            vtables: Vec::new(),
        },
        module_paths: HashMap::new(),
        names: Vec::new(),
        imports: Vec::new(),
        item_definitions: vec![None; ast.items.len()],
        item_modules: vec![None; ast.items.len()],
        generics: HashMap::new(),
        const_parameter_types: HashMap::new(),
        constant_assertions: HashSet::new(),
        variants: HashMap::new(),
        record_indices: Vec::new(),
        aliases: Vec::new(),
        alias_depth: 0,
        type_depth: 0,
        region_binders: Vec::new(),
        result_item: None,
        constant_queries: constants::Queries::default(),
        trait_state: traits::State::default(),
    };
    context.collect();
    context.collect_trait_members();
    context
        .record_indices
        .resize(context.program.definitions.len(), None);
    context.prepare_implementations();
    context.signatures();
    context.result_item = body::result_item(&mut context);
    context.check_constant_declarations();
    context.check_attribute_constants();
    context.check_enum_discriminants();
    context.check_assert_declarations();
    context.validate_implementations();
    context.record_cycles();
    context.check_bodies();
    context.check_instantiated_assertions();
    context.program
}

struct Context<'a> {
    ast: &'a Ast,
    sources: &'a SourceMap,
    symbols: &'a Interner,
    diagnostics: &'a mut Vec<Diagnostic>,
    program: hir::Program,
    module_paths: HashMap<Vec<Symbol>, ModuleId>,
    names: Vec<HashMap<Symbol, DefId>>,
    imports: Vec<HashMap<Symbol, ModuleId>>,
    item_definitions: Vec<Option<DefId>>,
    item_modules: Vec<Option<ModuleId>>,
    generics: HashMap<DefId, Vec<Symbol>>,
    const_parameter_types: HashMap<(DefId, u32), ast::TypeId>,
    constant_assertions: HashSet<(DefId, crate::types::ConstId, Span)>,
    variants: HashMap<(DefId, Symbol), DefId>,
    record_indices: Vec<Option<usize>>,
    aliases: Vec<AliasState>,
    alias_depth: usize,
    type_depth: usize,
    region_binders: Vec<Vec<Symbol>>,
    result_item: Option<DefId>,
    constant_queries: constants::Queries,
    trait_state: traits::State,
}

#[derive(Clone, Copy)]
enum AliasState {
    NotAlias,
    Unresolved(ast::TypeId),
    Resolving,
    Resolved(TyId),
}

impl Context<'_> {
    fn check_bodies(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let (Some(definition), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            if let ItemKind::Function(function) = &item.kind
                && let Some(body) = &function.body
            {
                let checked = body::check_function(self, module, definition, function, body);
                self.program.functions.push(checked);
            }
        }
    }

    fn error(&mut self, code: &'static str, message: impl Into<String>, span: Span) {
        report(self.diagnostics, Diagnostic::error(code, message, span));
    }
    fn unsupported(&mut self, feature: &str, span: Span) {
        self.error(
            "E-FRONTEND-STAGE",
            format!(
                "{feature} is parsed but its semantic pass is not implemented in this foundation"
            ),
            span,
        );
    }
    fn definition(&self, id: DefId) -> &hir::Definition {
        &self.program.definitions[id.0 as usize]
    }
    fn collect(&mut self) {
        let ast = self.ast;
        let mut module_ids = Vec::new();
        for module in &ast.modules {
            let path: Vec<_> = module.name.iter().map(|name| name.symbol).collect();
            let id = if let Some(&id) = self.module_paths.get(&path) {
                id
            } else {
                let id = ModuleId(self.program.modules.len() as u32);
                self.program.modules.push(hir::Module {
                    path: path.clone(),
                    definitions: Vec::new(),
                });
                self.names.push(HashMap::new());
                self.imports.push(HashMap::new());
                self.module_paths.insert(path, id);
                id
            };
            module_ids.push(id);
            for &item in &module.items {
                self.collect_item(item, id, None);
            }
        }
        for (module, &id) in ast.modules.iter().zip(&module_ids) {
            for import in &module.imports {
                let path: Vec<_> = import.path.iter().map(|name| name.symbol).collect();
                if let Some(&target) = self.module_paths.get(&path) {
                    if let Some(last) = path.last()
                        && self.imports[id.0 as usize].insert(*last, target).is_some()
                    {
                        self.error("E-NAME-DUPLICATE", "duplicate import alias", import.span);
                    }
                } else {
                    self.error(
                        "E-NAME-MODULE",
                        format!(
                            "module '{}' was not supplied to the frontend",
                            self.path_name(&import.path)
                        ),
                        import.span,
                    );
                }
            }
        }
    }
    fn collect_item(&mut self, item_id: ast::ItemId, module: ModuleId, foreign_abi: Option<&str>) {
        let ast = self.ast;
        let item = ast.item(item_id);
        self.item_modules[item_id.0 as usize] = Some(module);
        if let ItemKind::Extern { abi, items } = &item.kind {
            let value = self.sources.file(item.span.file).slice(ast.expr(*abi).span);
            let abi = literal::decode_quoted(value).unwrap_or_default();
            if abi != "C" {
                self.error("E-ABI-001", "only extern \"C\" is supported", item.span);
            }
            for &child in items {
                self.collect_item(child, module, Some(&abi));
            }
            return;
        }
        if matches!(item.kind, ItemKind::Impl { .. }) {
            self.collect_implementation(item_id, module);
            return;
        }
        let Some(name) = item.name else {
            return;
        };
        if let Some(&previous) = self.names[module.0 as usize].get(&name.symbol) {
            report(
                self.diagnostics,
                Diagnostic::error(
                    "E-NAME-DUPLICATE",
                    format!("duplicate definition '{}'", self.symbols.get(name.symbol)),
                    name.span,
                )
                .label(self.definition(previous).span, "first definition"),
            );
            return;
        }
        if self
            .program
            .types
            .builtin(self.symbols.get(name.symbol))
            .is_some()
            || self.symbols.get(name.symbol) == "ptr"
        {
            self.error(
                "E-NAME-RESERVED",
                "a definition cannot shadow a primitive type",
                name.span,
            );
        }
        let kind = match item.kind {
            ItemKind::Function(_) => D::Function,
            ItemKind::TypeAlias { .. } => D::TypeAlias,
            ItemKind::Record { union: false, .. } => D::Record,
            ItemKind::Record { union: true, .. } => D::Union,
            ItemKind::Enum { .. } => D::Enum,
            ItemKind::Trait { .. } => D::Trait,
            ItemKind::Contract { .. } => D::Contract,
            ItemKind::Global(_) => D::Global,
            // Assertions create no value/type definition; their module is
            // retained above for the dedicated constant-assertion phase.
            ItemKind::StaticAssert(_) => return,
            ItemKind::Extern { .. } | ItemKind::Impl { .. } => unreachable!(),
        };
        let definition = self.add_definition(name, module, kind, item.visibility, foreign_abi);
        if let ItemKind::Function(function) = &item.kind {
            self.program.definitions[definition.0 as usize].const_origin =
                function.constant.then_some(definition);
            self.program.definitions[definition.0 as usize].declaration_clauses = function
                .clauses
                .iter()
                .map(|c| (c.kind, self.ast.expr(c.predicate).span))
                .collect();
        }
        self.program.definitions[definition.0 as usize].attributes = item
            .attributes
            .iter()
            .map(|attribute| hir::Attribute {
                constant: None,
                name: attribute.name.symbol,
                arguments: attribute.arguments.clone(),
                span: attribute.span,
            })
            .collect();
        self.names[module.0 as usize].insert(name.symbol, definition);
        self.program.modules[module.0 as usize]
            .definitions
            .push(definition);
        self.item_definitions[item_id.0 as usize] = Some(definition);
        if let ItemKind::TypeAlias { target, .. } = item.kind {
            self.aliases[definition.0 as usize] = AliasState::Unresolved(target);
        }
        let generics = match &item.kind {
            ItemKind::Function(f) => &f.generics,
            ItemKind::TypeAlias { generics, .. }
            | ItemKind::Record { generics, .. }
            | ItemKind::Enum { generics, .. }
            | ItemKind::Trait { generics, .. }
            | ItemKind::Contract { generics, .. } => generics,
            _ => return,
        };
        self.collect_generic_parameters(definition, generics, true);
        if self.definition(definition).lifetime_parameters.len() > 64 {
            self.error(
                "E-REGION-LIMIT",
                "a declaration exceeds the lifetime parameter limit",
                item.span,
            );
        }
        if let ItemKind::Enum { variants, .. } = &item.kind {
            let mut children = Vec::new();
            for (index, variant) in variants.iter().enumerate() {
                if self
                    .variants
                    .contains_key(&(definition, variant.name.symbol))
                {
                    self.error(
                        "E-NAME-DUPLICATE",
                        "duplicate enum variant",
                        variant.name.span,
                    );
                    continue;
                }
                let child = self.add_definition(
                    variant.name,
                    module,
                    D::Variant {
                        parent: definition,
                        index: index as u32,
                    },
                    item.visibility,
                    None,
                );
                self.variants
                    .insert((definition, variant.name.symbol), child);
                children.push(child);
            }
            self.program.enums.push(hir::Enum {
                definition,
                discriminants: (0..children.len())
                    .map(|index| self.program.types.const_value(index as u64))
                    .collect(),
                variants: children,
            });
        }
    }
    fn add_definition(
        &mut self,
        name: Name,
        module: ModuleId,
        kind: D,
        visibility: Visibility,
        foreign: Option<&str>,
    ) -> DefId {
        let id = DefId(self.program.definitions.len() as u32);
        self.program.definitions.push(hir::Definition {
            const_origin: None,
            name: name.symbol,
            module,
            visibility,
            kind,
            ty: TyId::ERROR,
            span: name.span,
            attributes: Vec::new(),
            foreign_abi: foreign.map(str::to_owned),
            lifetime_parameters: Vec::new(),
            type_parameter_count: 0,
            generic_parameter_kinds: Vec::new(),
            declaration_clauses: Vec::new(),
            bounds: Vec::new(),
        });
        self.aliases.push(AliasState::NotAlias);
        id
    }
    fn signatures(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let (Some(definition), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            let parameters = self.parameters(definition);
            self.validate_const_parameters(definition);
            match &item.kind {
                ItemKind::TypeAlias { .. } => {
                    self.resolve_alias(definition, item.span);
                }
                ItemKind::Function(function) => {
                    let args = function
                        .parameters
                        .iter()
                        .map(|p| {
                            let ty = self.resolve_type(p.ty, module, definition, &parameters);
                            if ty == TyId::VOID
                                || ty == TyId::STR
                                || matches!(
                                    self.program.types.get(ty),
                                    Ty::Slice(_) | Ty::Dynamic { .. }
                                )
                            {
                                self.error(
                                    "E-TYPE-SIZED",
                                    "parameters require a sized value type",
                                    p.name.span,
                                );
                            }
                            ty
                        })
                        .collect();
                    let result =
                        self.resolve_type(function.result, module, definition, &parameters);
                    if result == TyId::STR
                        || matches!(
                            self.program.types.get(result),
                            Ty::Slice(_) | Ty::Dynamic { .. }
                        )
                    {
                        self.error("E-TYPE-SIZED", "return type must be sized", item.span);
                    }
                    let ty = self.program.types.intern(Ty::Function {
                        parameters: args,
                        result,
                    });
                    self.program.definitions[definition.0 as usize].ty = ty;
                    if function.variadic {
                        self.unsupported("variadic call promotion", item.span);
                    }
                }
                ItemKind::Record { union, fields, .. } => {
                    let args = self.parameter_arguments(definition);
                    let ty = self.program.types.intern(Ty::Named {
                        definition,
                        arguments: args,
                    });
                    self.program.definitions[definition.0 as usize].ty = ty;
                    let mut names = HashSet::new();
                    let fields = fields
                        .iter()
                        .map(|field| {
                            if !names.insert(field.name.symbol) {
                                self.error("E-NAME-DUPLICATE", "duplicate field", field.name.span);
                            }
                            let ty = self.resolve_type(field.ty, module, definition, &parameters);
                            if ty == TyId::VOID
                                || ty == TyId::STR
                                || matches!(
                                    self.program.types.get(ty),
                                    Ty::Slice(_) | Ty::Dynamic { .. }
                                )
                            {
                                self.error(
                                    "E-TYPE-SIZED",
                                    "fields must have a sized value type",
                                    field.name.span,
                                );
                            }
                            hir::Field {
                                name: field.name.symbol,
                                ty,
                                visibility: field.visibility,
                                span: field.name.span,
                            }
                        })
                        .collect();
                    self.record_indices[definition.0 as usize] = Some(self.program.records.len());
                    self.program.records.push(hir::Record {
                        definition,
                        parameters: self.generics.get(&definition).cloned().unwrap_or_default(),
                        fields,
                    });
                    if *union {
                        self.unsupported("raw union permission checking", item.span);
                    }
                }
                ItemKind::Enum { variants, .. } => {
                    let args = self.parameter_arguments(definition);
                    let result = self.program.types.intern(Ty::Named {
                        definition,
                        arguments: args,
                    });
                    self.program.definitions[definition.0 as usize].ty = result;
                    for variant in variants {
                        let Some(&child) = self.variants.get(&(definition, variant.name.symbol))
                        else {
                            continue;
                        };
                        if !variant.named_fields.is_empty() {
                            self.unsupported("named enum fields", variant.name.span);
                        }
                        let fields: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|&ty| self.resolve_type(ty, module, definition, &parameters))
                            .collect();
                        let ty = if fields.is_empty() {
                            result
                        } else {
                            self.program.types.intern(Ty::Function {
                                parameters: fields,
                                result,
                            })
                        };
                        self.program.definitions[child.0 as usize].ty = ty;
                    }
                }
                ItemKind::Trait { .. } => {
                    self.program.definitions[definition.0 as usize].ty = TyId::VOID
                }
                ItemKind::Contract { .. } => {
                    self.unsupported("named contract predicate checking", item.span)
                }
                ItemKind::Global(_) => {
                    if let Err(error) = self.declared_constant_type(definition) {
                        self.report_constant(error);
                    }
                }
                _ => {}
            }
        }
    }
    fn resolve_alias(&mut self, definition: DefId, span: Span) -> TyId {
        let target = match self.aliases[definition.0 as usize] {
            AliasState::Resolved(ty) => return ty,
            AliasState::Resolving => {
                report(
                    self.diagnostics,
                    Diagnostic::error(
                        "E-TYPE-ALIAS-CYCLE",
                        "type alias expansion is recursive",
                        span,
                    )
                    .label(self.definition(definition).span, "alias being expanded"),
                );
                return TyId::ERROR;
            }
            AliasState::Unresolved(target) => target,
            AliasState::NotAlias => unreachable!("only aliases have expansion templates"),
        };
        if self.alias_depth >= 128 {
            self.error(
                "E-TYPE-DEPTH",
                "type alias dependencies exceed 128 levels",
                span,
            );
            return TyId::ERROR;
        }
        self.aliases[definition.0 as usize] = AliasState::Resolving;
        self.alias_depth += 1;
        let parameters = self.parameters(definition);
        // Alias templates are resolved in their declaration scope, even when a
        // forward use occurs inside a callable's lifetime binder.
        let caller_binders = std::mem::take(&mut self.region_binders);
        let mut ty = self.resolve_type(
            target,
            self.definition(definition).module,
            definition,
            &parameters,
        );
        self.region_binders = caller_binders;
        self.alias_depth -= 1;
        if self.program.types.nesting(ty) > 128 {
            self.error(
                "E-TYPE-ALIAS-LIMIT",
                "expanded alias type exceeds 128 levels",
                span,
            );
            ty = TyId::ERROR;
        }
        self.aliases[definition.0 as usize] = AliasState::Resolved(ty);
        self.program.definitions[definition.0 as usize].ty = ty;
        ty
    }
    fn resolve_type(
        &mut self,
        id: ast::TypeId,
        module: ModuleId,
        owner: DefId,
        parameters: &HashMap<Symbol, TyId>,
    ) -> TyId {
        self.resolve_type_with_bindings(
            id,
            module,
            owner,
            parameters,
            &constants::ConstBindings::new(),
        )
    }
    fn resolve_type_with_bindings(
        &mut self,
        id: ast::TypeId,
        module: ModuleId,
        owner: DefId,
        parameters: &HashMap<Symbol, TyId>,
        bindings: &constants::ConstBindings,
    ) -> TyId {
        if self.type_depth >= 128 {
            self.error(
                "E-TYPE-DEPTH",
                "type resolution nesting exceeds 128 levels",
                self.ast.ty(id).span,
            );
            return TyId::ERROR;
        }
        self.type_depth += 1;
        let ty = self.resolve_type_inner(id, module, owner, parameters, bindings);
        self.type_depth -= 1;
        self.program
            .types
            .close_callable_elision(ty)
            .unwrap_or_else(|| {
                self.error(
                    "E-REGION-LIMIT",
                    "callable lifetime closure exceeds its resource limit",
                    self.ast.ty(id).span,
                );
                TyId::ERROR
            })
    }
    fn resolve_type_inner(
        &mut self,
        id: ast::TypeId,
        module: ModuleId,
        owner: DefId,
        parameters: &HashMap<Symbol, TyId>,
        bindings: &constants::ConstBindings,
    ) -> TyId {
        let ast = self.ast;
        let node = ast.ty(id);
        let ty = match &node.kind {
            TypeKind::Path { path, arguments } => {
                return self.resolve_path_type(
                    path,
                    arguments,
                    const_generics::TypeScope {
                        module,
                        owner,
                        parameters,
                    },
                    bindings,
                    node.span,
                );
            }
            TypeKind::Reference {
                lifetime,
                mutable,
                inner,
            } => {
                let region = match lifetime {
                    Some(name) if self.symbols.get(name.symbol) == "static" => Region::Static,
                    Some(name) => {
                        if let Some((depth, index)) =
                            self.region_binders.iter().rev().enumerate().find_map(
                                |(depth, names)| {
                                    names
                                        .iter()
                                        .position(|&n| n == name.symbol)
                                        .map(|index| (depth, index))
                                },
                            )
                        {
                            let inner = self.resolve_type_with_bindings(
                                *inner, module, owner, parameters, bindings,
                            );
                            return self.program.types.intern(Ty::Reference {
                                region: Region::Bound {
                                    depth: depth as u16,
                                    index: index as u16,
                                },
                                mutable: *mutable,
                                inner,
                            });
                        }
                        if !self
                            .definition(owner)
                            .lifetime_parameters
                            .contains(&name.symbol)
                        {
                            self.error(
                                "E-REGION-NAME",
                                format!("undeclared lifetime '{}", self.symbols.get(name.symbol)),
                                name.span,
                            );
                        }
                        Region::Named {
                            owner,
                            name: name.symbol,
                        }
                    }
                    None => self.program.types.fresh_region(),
                };
                let inner =
                    self.resolve_type_with_bindings(*inner, module, owner, parameters, bindings);
                Ty::Reference {
                    region,
                    mutable: *mutable,
                    inner,
                }
            }
            TypeKind::Slice(inner) => Ty::Slice(
                self.resolve_type_with_bindings(*inner, module, owner, parameters, bindings),
            ),
            TypeKind::Array { inner, length } => {
                let inner =
                    self.resolve_type_with_bindings(*inner, module, owner, parameters, bindings);
                let length = match self.const_length(module, owner, *length, bindings) {
                    Ok(length) => length,
                    Err(error) => {
                        self.report_constant(error);
                        return TyId::ERROR;
                    }
                };
                return match self.program.types.array_type(inner, length) {
                    Ok(ty) => ty,
                    Err(error) => {
                        self.error("E-CONST-EVAL", error.to_string(), node.span);
                        TyId::ERROR
                    }
                };
            }
            TypeKind::Function {
                lifetimes,
                parameters: args,
                result,
                attributes,
            } => {
                if !attributes.is_empty() {
                    self.unsupported("callable effect bound checking", node.span);
                }
                if !lifetimes.is_empty() {
                    let mut names = Vec::new();
                    for name in lifetimes {
                        if self.symbols.get(name.symbol) == "static" || names.contains(&name.symbol)
                        {
                            self.error(
                                "E-REGION-NAME",
                                "callable lifetime binders must be unique and cannot bind 'static",
                                name.span,
                            );
                        }
                        names.push(name.symbol);
                    }
                    if names.len() > 64 {
                        self.error(
                            "E-REGION-LIMIT",
                            "callable lifetime binder exceeds 64 parameters",
                            node.span,
                        );
                        return TyId::ERROR;
                    }
                    self.region_binders.push(names);
                }
                let args = args
                    .iter()
                    .map(|&arg| {
                        self.resolve_type_with_bindings(arg, module, owner, parameters, bindings)
                    })
                    .collect();
                let result =
                    self.resolve_type_with_bindings(*result, module, owner, parameters, bindings);
                let inner = self.program.types.intern(Ty::Function {
                    parameters: args,
                    result,
                });
                let inner=self.program.types.elide_callable_result(inner).unwrap_or_else(||{
                    self.error("E-REGION-ELISION","callable return lifetime requires exactly one reference input or an explicit lifetime",node.span);TyId::ERROR
                });
                if !lifetimes.is_empty() {
                    self.region_binders.pop();
                    return self.program.types.intern(Ty::ForAll {
                        parameters: lifetimes.len() as u16,
                        inner,
                    });
                }
                return inner;
            }
            TypeKind::Const(_) => {
                self.error(
                    "E-TYPE-QUALIFIER",
                    "const type qualifier is only valid inside ptr<const T>",
                    node.span,
                );
                return TyId::ERROR;
            }
            TypeKind::Dynamic(bounds) => {
                return self.resolve_dynamic(bounds, module, owner, parameters, node.span);
            }
            TypeKind::Lifetime(_) => {
                self.unsupported("explicit lifetime argument checking", node.span);
                return TyId::ERROR;
            }
            TypeKind::Infer => {
                self.error("E-TYPE-INFER", "this type must be explicit", node.span);
                return TyId::ERROR;
            }
            TypeKind::Error => return TyId::ERROR,
        };
        self.program.types.intern(ty)
    }
    fn resolve(&mut self, module: ModuleId, path: &[Name]) -> Option<DefId> {
        let definition = self.lookup(module, path);
        let span = path.first()?.span.join(path.last()?.span);
        let Some(definition) = definition else {
            self.error(
                "E-NAME-UNKNOWN",
                format!("unknown name '{}'", self.path_name(path)),
                span,
            );
            return None;
        };
        let found = self.definition(definition);
        if found.module != module && found.visibility == Visibility::Private {
            report(
                self.diagnostics,
                Diagnostic::error(
                    "E-NAME-PRIVATE",
                    format!("'{}' is private", self.path_name(path)),
                    span,
                )
                .label(found.span, "private declaration"),
            );
            return None;
        }
        Some(definition)
    }
    fn lookup(&self, module: ModuleId, path: &[Name]) -> Option<DefId> {
        if path.len() == 1 {
            return self.names[module.0 as usize].get(&path[0].symbol).copied();
        }
        let module_path: Vec<_> = path[..path.len() - 1]
            .iter()
            .map(|name| name.symbol)
            .collect();
        if let Some(&target) = self.module_paths.get(&module_path) {
            return self.names[target.0 as usize]
                .get(&path.last()?.symbol)
                .copied();
        }
        if path.len() == 2
            && let Some(&target) = self.imports[module.0 as usize].get(&path[0].symbol)
        {
            return self.names[target.0 as usize].get(&path[1].symbol).copied();
        }
        let mut parent = self.lookup(module, &path[..path.len() - 1])?;
        if self.definition(parent).kind == D::TypeAlias
            && self.generics.get(&parent).is_none_or(Vec::is_empty)
            && let Ty::Named {
                definition,
                arguments,
            } = self.program.types.get(self.definition(parent).ty)
            && arguments.is_empty()
        {
            parent = *definition;
        }
        self.variants
            .get(&(parent, path.last()?.symbol))
            .copied()
            .or_else(|| self.lookup_associated(parent, path.last().expect("nonempty path").symbol))
    }
    fn is_namespace(&mut self, module: ModuleId, path: &[Name]) -> bool {
        let symbols: Vec<_> = path.iter().map(|name| name.symbol).collect();
        self.module_paths.contains_key(&symbols)
            || (path.len() == 1
                && (self.imports[module.0 as usize].contains_key(&path[0].symbol)
                    || self.symbols.get(path[0].symbol) == "ptr"
                    || self
                        .program
                        .types
                        .builtin(self.symbols.get(path[0].symbol))
                        .is_some()))
            || self.lookup(module, path).is_some_and(|definition| {
                matches!(
                    self.definition(definition).kind,
                    D::Record | D::Union | D::Enum | D::TypeAlias | D::Trait
                )
            })
    }
    fn path_name(&self, path: &[Name]) -> String {
        path.iter()
            .map(|name| self.symbols.get(name.symbol))
            .collect::<Vec<_>>()
            .join("::")
    }
    fn record_cycles(&mut self) {
        layout::check(self);
    }
}
