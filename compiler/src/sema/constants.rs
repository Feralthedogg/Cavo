//! Source-to-typed-constant queries. Compilation and value evaluation are separate:
//! both branches must type-check, but only executed branches create value cycles.

mod compile;

use super::*;
use crate::ctfe::{self, Error, Limits, Value};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub(super) enum ConstBinding {
    Runtime,
    Value(Value),
    Term(crate::types::ConstId),
}
pub(super) type ConstBindings = HashMap<Symbol, ConstBinding>;

#[derive(Default)]
pub(super) struct Queries {
    sources: Vec<Option<ast::ItemId>>,
    functions: HashSet<DefId>,
    globals: HashSet<DefId>,
    global_types: HashSet<DefId>,
    depth: usize,
}

impl Context<'_> {
    pub(super) fn integer_constant(
        &mut self,
        path: &[Name],
        span: Span,
    ) -> Result<Option<Value>, Error> {
        if path.len() != 2 || !matches!(self.symbols.get(path[1].symbol), "MIN" | "MAX") {
            return Ok(None);
        }
        let Some(ty) = self.program.types.builtin(self.symbols.get(path[0].symbol)) else {
            return Ok(None);
        };
        let Ty::Integer { signed, bits } = *self.program.types.get(ty) else {
            return Err(Error::new(
                "E-CONST-CONTEXT",
                "MIN/MAX requires an integer type",
                span,
            ));
        };
        let bits = if bits == 0 { 64 } else { bits };
        let maximum = self.symbols.get(path[1].symbol) == "MAX";
        let (magnitude, negative) = match (signed, maximum) {
            (true, true) => ((1u128 << (bits - 1)) - 1, false),
            (true, false) => (1u128 << (bits - 1), true),
            (false, true) => (u128::MAX >> (128 - bits), false),
            (false, false) => (0, false),
        };
        Ok(Some(Value {
            ty,
            kind: ctfe::ValueKind::Integer {
                magnitude,
                negative,
            },
        }))
    }
    pub(super) fn constant_item(&mut self, definition: DefId) -> Result<ast::ItemId, Error> {
        if self.constant_queries.sources.len() < self.program.definitions.len() {
            self.constant_queries
                .sources
                .resize(self.program.definitions.len(), None);
            for (index, &definition) in self.item_definitions.iter().enumerate() {
                if let Some(definition) = definition {
                    self.constant_queries.sources[definition.0 as usize] =
                        Some(ast::ItemId(index as u32));
                }
            }
        }
        self.constant_queries
            .sources
            .get(definition.0 as usize)
            .copied()
            .flatten()
            .ok_or_else(|| {
                self.constant_error(definition, "constant declaration has no source body")
            })
    }

    pub(super) fn constant_value(&mut self, definition: DefId) -> Result<Value, Error> {
        self.prepare_constant(definition)?;
        ctfe::evaluate_global(&self.program, definition, Limits::default())
    }

    pub(super) fn constant_type(&mut self, definition: DefId) -> Result<TyId, Error> {
        self.prepare_constant(definition)?;
        Ok(self.definition(definition).ty)
    }

    pub(super) fn declared_constant_type(&mut self, definition: DefId) -> Result<TyId, Error> {
        let item = self.constant_item(definition)?;
        let ItemKind::Global(variable) = &self.ast.item(item).kind else {
            return Err(self.constant_error(definition, "name is not a module constant"));
        };
        if !variable.constant {
            return Err(
                self.constant_error(definition, "module values require const initialization")
            );
        }
        if self.definition(definition).ty != TyId::ERROR {
            return Ok(self.definition(definition).ty);
        }
        if !self.constant_queries.global_types.insert(definition) {
            return Err(Error::new(
                "E-CONST-CYCLE",
                "constant type depends on its own value",
                self.definition(definition).span,
            ));
        }
        let module = self.definition(definition).module;
        let ty = self.resolve_type(variable.ty, module, definition, &HashMap::new());
        self.constant_queries.global_types.remove(&definition);
        if ty == TyId::ERROR {
            return Err(self.constant_error(definition, "constant has an invalid declared type"));
        }
        if matches!(
            self.program.types.get(ty),
            Ty::Void | Ty::Str | Ty::Slice(_) | Ty::Dynamic { .. }
        ) {
            return Err(
                self.constant_error(definition, "module constant requires a sized value type")
            );
        }
        self.program.definitions[definition.0 as usize].ty = ty;
        Ok(ty)
    }

    fn prepare_constant(&mut self, definition: DefId) -> Result<(), Error> {
        if self.program.constants.globals.contains_key(&definition) {
            return Ok(());
        }
        let ty = self.declared_constant_type(definition)?;
        if !self.constant_queries.globals.insert(definition) {
            return Ok(());
        }
        self.enter_constant_query(definition)?;
        let result = self.compile_global(definition, ty);
        self.constant_queries.depth -= 1;
        self.constant_queries.globals.remove(&definition);
        let global = result?;
        self.program.constants.globals.insert(definition, global);
        Ok(())
    }

    fn compile_global(&mut self, definition: DefId, ty: TyId) -> Result<ctfe::Global, Error> {
        let item = self.constant_item(definition)?;
        let ItemKind::Global(variable) = &self.ast.item(item).kind else {
            unreachable!("constant type checked");
        };
        let expression = variable.initializer.ok_or_else(|| {
            self.constant_error(definition, "module constant requires an initializer")
        })?;
        let module = self.definition(definition).module;
        let span = self.definition(definition).span;
        let (expressions, initializer) = compile::expression(
            self,
            module,
            definition,
            expression,
            ty,
            &ConstBindings::new(),
        )?;
        Ok(ctfe::Global {
            definition,
            ty,
            expressions,
            initializer,
            span,
        })
    }

    pub(super) fn const_function_type(&mut self, definition: DefId) -> Result<TyId, Error> {
        if self.program.constants.functions.contains_key(&definition) {
            return Ok(self.definition(definition).ty);
        }
        let item = self.constant_item(definition)?;
        let ItemKind::Function(function) = &self.ast.item(item).kind else {
            return Err(self.constant_error(
                definition,
                "constant call must directly name a const function",
            ));
        };
        if !function.constant
            || function.body.is_none()
            || self.definition(definition).foreign_abi.is_some()
        {
            return Err(self.constant_error(
                definition,
                "constant evaluation requires a checked source const function",
            ));
        }
        self.program.definitions[definition.0 as usize].const_origin = Some(definition);
        if self.constant_queries.functions.contains(&definition) {
            return (self.definition(definition).ty != TyId::ERROR)
                .then_some(self.definition(definition).ty)
                .ok_or_else(|| {
                    Error::new(
                        "E-CONST-CYCLE",
                        "constant function signature depends on itself",
                        self.definition(definition).span,
                    )
                });
        }
        self.constant_queries.functions.insert(definition);
        self.enter_constant_query(definition)?;
        let result = self.compile_constant_function(definition, item);
        self.constant_queries.depth -= 1;
        self.constant_queries.functions.remove(&definition);
        let body = result?;
        self.program.constants.functions.insert(definition, body);
        Ok(self.definition(definition).ty)
    }

    fn compile_constant_function(
        &mut self,
        definition: DefId,
        item: ast::ItemId,
    ) -> Result<ctfe::Function, Error> {
        let ItemKind::Function(function) = &self.ast.item(item).kind else {
            unreachable!("const function source checked");
        };
        let module = self.definition(definition).module;
        let parameters = self.parameters(definition);
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| self.resolve_type(parameter.ty, module, definition, &parameters))
            .collect();
        let result = self.resolve_type(function.result, module, definition, &parameters);
        let ty = self.program.types.intern(Ty::Function {
            parameters: arguments,
            result,
        });
        self.program.definitions[definition.0 as usize].ty = ty;
        compile::function(self, module, definition, function, &parameters)
    }

    pub(super) fn eval_constant(
        &mut self,
        module: ModuleId,
        owner: DefId,
        expression: ast::ExprId,
        expected: TyId,
        bindings: &ConstBindings,
    ) -> Result<Value, Error> {
        let (expressions, root) =
            compile::expression(self, module, owner, expression, expected, bindings)?;
        ctfe::evaluate_expression(
            &self.program,
            &expressions,
            root,
            Vec::new(),
            Limits::default(),
        )
    }

    pub(super) fn check_constant_declarations(&mut self) {
        let declarations: Vec<_> = self
            .item_definitions
            .iter()
            .enumerate()
            .filter_map(|(index, definition)| {
                let definition = (*definition)?;
                match &self.ast.items[index].kind {
                    ItemKind::Global(_)
                    | ItemKind::Function(ast::Function { constant: true, .. }) => Some(definition),
                    _ => None,
                }
            })
            .collect();
        for definition in declarations {
            let result = if self.definition(definition).kind == D::Global {
                self.constant_value(definition).map(|_| ())
            } else {
                self.const_function_type(definition).map(|_| ())
            };
            if let Err(error) = result {
                self.report_constant(error);
            }
        }
    }

    pub(super) fn report_constant(&mut self, error: Error) {
        let mut diagnostic = Diagnostic::error(error.code, error.message, error.span);
        for span in error.frames.into_iter().rev().take(8) {
            diagnostic = diagnostic.label(span, "while evaluating this constant query");
        }
        report(self.diagnostics, diagnostic);
    }

    fn constant_error(&self, definition: DefId, message: &str) -> Error {
        Error::new("E-CONST-CONTEXT", message, self.definition(definition).span)
    }
    fn enter_constant_query(&mut self, definition: DefId) -> Result<(), Error> {
        if self.constant_queries.depth >= 128 {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant declaration dependency limit exceeded",
                self.definition(definition).span,
            ));
        }
        self.constant_queries.depth += 1;
        Ok(())
    }
}
