use super::*;
mod refinement;
use crate::contracts::{Intrinsic, MemoryPredicate, PredicateDefinition};
use crate::syntax::token::TokenKind;

impl Context<'_> {
    pub(super) fn bind_verified_modules(&mut self) {
        for (index, definition) in self.program.definitions.iter().enumerate() {
            if definition.kind == D::Function
                && let Some(digest) = self.verified_modules.get(&definition.span.file)
            {
                let id = DefId(index as u32);
                self.program
                    .modular
                    .assumptions
                    .insert(id, digest.assumptions.clone());
                if !digest.certified_offsets.contains(&definition.span.start) {
                    continue;
                }
                self.program
                    .modular
                    .imported
                    .insert(id, digest.identity.to_string());
                self.program
                    .modular
                    .functions
                    .entry(id)
                    .or_insert_with(|| crate::modular::Contract::conservative(definition.span));
            }
        }
    }
    pub(super) fn register_modular_contracts(&mut self) {
        let mut names = std::collections::BTreeMap::new();
        for (index, item) in self.ast.items.iter().enumerate() {
            if let ItemKind::Function(function) = &item.kind
                && let Some(definition) = self.item_definitions[index]
            {
                names.insert(
                    definition,
                    function.parameters.iter().map(|p| p.name.symbol).collect(),
                );
            }
        }
        crate::modular::collect(
            &mut self.program,
            &names,
            self.symbols,
            self.sources,
            self.diagnostics,
        );
    }
    pub(super) fn contract_signature(&mut self, definition: DefId, parameters: &[ast::Parameter]) {
        let module = self.definition(definition).module;
        let generics = self.parameters(definition);
        let parameters = parameters
            .iter()
            .map(|parameter| self.resolve_type(parameter.ty, module, definition, &generics))
            .collect();
        self.program.definitions[definition].ty = self.program.types.intern(Ty::Function {
            parameters,
            result: TyId::BOOL,
        });
        self.program.contracts.predicates.insert(
            definition,
            PredicateDefinition {
                memory: None,
                body: None,
            },
        );
    }

    pub(super) fn register_contract_roles(&mut self) {
        for index in 0..self.program.definitions.len() {
            let definition = DefId(index as u32);
            let attributes = self.program.definitions[index].attributes.clone();
            for attribute in attributes {
                let name = self.symbols.get(attribute.name);
                if name != "intrinsic"
                    && !(name == "lang" && self.definition(definition).kind == D::Contract)
                {
                    continue;
                }
                let Some(role) = role_name(&attribute, self.symbols) else {
                    self.error(
                        "E-LANG-ITEM",
                        "a compiler role requires one identifier",
                        attribute.span,
                    );
                    continue;
                };
                if name == "intrinsic" {
                    self.register_intrinsic(definition, role, attribute.span);
                } else if let Some(kind) = memory_role(role) {
                    if !crate::contracts::predicate_shape(
                        &self.program.types,
                        self.definition(definition).ty,
                        kind,
                    ) {
                        self.error("E-LANG-CONTRACT", "memory predicate signature does not match its compiler-defined relation", attribute.span);
                        continue;
                    }
                    if let Some(predicate) = self.program.contracts.predicates.get_mut(&definition)
                    {
                        predicate.memory = Some(kind);
                    }
                } else {
                    self.error(
                        "E-LANG-ITEM",
                        "unknown logical memory predicate role",
                        attribute.span,
                    );
                }
            }
        }
    }

    fn register_intrinsic(&mut self, definition: DefId, name: &str, span: Span) {
        let role = match name {
            "task_join" => Intrinsic::TaskJoin,
            "task_cancel" => Intrinsic::TaskCancel,
            "task_ignore" => Intrinsic::TaskIgnore,
            "len" => Intrinsic::Length,
            "as_ptr" => Intrinsic::AsPtr,
            "as_mut_ptr" => Intrinsic::AsMutPtr,
            "ptr_read" => Intrinsic::Read,
            "ptr_read_unaligned" => Intrinsic::ReadUnaligned,
            "ptr_take" => Intrinsic::Take,
            "ptr_initialize" => Intrinsic::Initialize,
            "ptr_replace" => Intrinsic::Replace,
            "ptr_write_unaligned" => Intrinsic::WriteUnaligned,
            "allocate" => Intrinsic::Allocate,
            "deallocate" => Intrinsic::Deallocate,
            "ptr_offset" => Intrinsic::Offset,
            _ => {
                self.error("E-INTRINSIC", "unknown compiler intrinsic role", span);
                return;
            }
        };
        let declaration = self.definition(definition);
        if declaration.kind != D::Function || declaration.foreign_abi.is_some()
            || !declaration.declaration_clauses.is_empty()
            || self.item_definitions.iter().position(|&item| item == Some(definition))
                .is_some_and(|index| matches!(&self.ast.items[index].kind, ItemKind::Function(function) if function.body.is_some()))
            || !crate::contracts::intrinsic_shape(&self.program.types, declaration.ty, role)
        {
            self.error("E-INTRINSIC", "intrinsic signature does not match its compiler-defined operation", span);
            return;
        }
        self.program.contracts.intrinsics.insert(definition, role);
    }
}

fn role_name<'a>(attribute: &hir::Attribute, symbols: &'a Interner) -> Option<&'a str> {
    match attribute.arguments.as_slice() {
        [
            crate::syntax::token::Token {
                kind: TokenKind::Ident(name),
                ..
            },
        ] => Some(symbols.get(*name)),
        _ => None,
    }
}

fn memory_role(name: &str) -> Option<MemoryPredicate> {
    Some(match name {
        "readable" => MemoryPredicate::Readable,
        "writable" => MemoryPredicate::Writable,
        "readable_unaligned" => MemoryPredicate::ReadableUnaligned,
        "writable_unaligned" => MemoryPredicate::WritableUnaligned,
        "initialized" => MemoryPredicate::Initialized,
        "disjoint" => MemoryPredicate::Disjoint,
        "owned_allocation" => MemoryPredicate::OwnedAllocation,
        "borrowed_from" => MemoryPredicate::BorrowedFrom,
        "active_union" => MemoryPredicate::ActiveUnion,
        "no_retain" => MemoryPredicate::NoRetain,
        "no_callback" => MemoryPredicate::NoCallback,
        _ => return None,
    })
}
