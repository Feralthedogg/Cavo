//! Explicit captures become ordinary owned records and checked hidden functions.
//! Existing move/region/drop analysis therefore sees the environment's real data.

mod adapters;
mod body;
mod call;

use super::*;
use crate::{
    hir::ClosureKind,
    types::{GenericArg, GenericParamKind},
};

struct Capture {
    name: ast::Name,
    mode: ast::CaptureMode,
    value: ExprId,
    body_ty: TyId,
    storage_ty: TyId,
}

struct Declaration {
    environment: DefId,
    function: DefId,
    instance: TyId,
}

struct Syntax<'a> {
    parameters: &'a [ast::Parameter],
    result: Option<ast::TypeId>,
    body: &'a ast::Block,
}

impl Body<'_, '_> {
    pub(super) fn closure(
        &mut self,
        captures: &[ast::Capture],
        parameters: &[ast::Parameter],
        result: Option<ast::TypeId>,
        body: &ast::Block,
        span: Span,
    ) -> ExprId {
        let values = self.capture_values(captures);
        if values.len() != captures.len() {
            return self.add_expr(H::Error, TyId::ERROR, span);
        }
        let declaration = self.closure_declaration(&values, span);
        let outer = self
            .scopes
            .iter()
            .flat_map(|scope| scope.keys().copied())
            .collect();
        let syntax = Syntax {
            parameters,
            result,
            body,
        };
        let (function, kind) = self.closure_body(&declaration, &values, &syntax, outer);
        self.context.program.functions.push(function);
        let adapters = self.closure_adapters(&declaration, kind, span);
        self.context.program.closures.push(hir::Closure {
            environment: declaration.environment,
            function: declaration.function,
            kind,
            adapters,
        });
        self.add_expr(
            H::Record {
                definition: declaration.environment,
                fields: values
                    .into_iter()
                    .enumerate()
                    .map(|(index, capture)| (index as u32, capture.value))
                    .collect(),
            },
            declaration.instance,
            span,
        )
    }

    fn capture_values(&mut self, captures: &[ast::Capture]) -> Vec<Capture> {
        let mut seen = HashSet::new();
        let mut values = Vec::with_capacity(captures.len());
        for capture in captures {
            if !seen.insert(capture.name.symbol) {
                self.context.error(
                    "E-CLOSURE-CAPTURE",
                    "closure captures the same binding twice",
                    capture.name.span,
                );
                continue;
            }
            let Some(local) = self.find_local(capture.name.symbol) else {
                self.context.error(
                    "E-CLOSURE-CAPTURE",
                    "capture must name an enclosing local binding",
                    capture.name.span,
                );
                continue;
            };
            values.push(self.capture_value(capture, local));
        }
        values
    }

    fn capture_value(&mut self, capture: &ast::Capture, local: LocalId) -> Capture {
        let binding = &self.function.locals[local.0 as usize];
        let body_ty = binding.ty;
        if capture.mode == ast::CaptureMode::Mutable && !binding.mutable {
            self.context.error(
                "E-CLOSURE-CAPTURE",
                "mutable capture requires a mutable binding",
                capture.name.span,
            );
        }
        let (op, storage_ty) = match capture.mode {
            ast::CaptureMode::Move => (U::Move, body_ty),
            mode => {
                let mutable = mode == ast::CaptureMode::Mutable;
                let region = self.context.program.types.fresh_region();
                let ty = self.context.program.types.intern(Ty::Reference {
                    region,
                    mutable,
                    inner: body_ty,
                });
                (if mutable { U::BorrowMut } else { U::Borrow }, ty)
            }
        };
        let operand = self.read_local(local, capture.name.span);
        let value = self.add_expr(H::Unary { op, operand }, storage_ty, capture.name.span);
        Capture {
            name: capture.name,
            mode: capture.mode,
            value,
            body_ty,
            storage_ty,
        }
    }

    fn closure_declaration(&mut self, captures: &[Capture], span: Span) -> Declaration {
        let parent = self.definition;
        let name = ast::Name {
            symbol: self.context.definition(parent).name,
            span,
        };
        let environment = self.context.add_definition(
            name,
            self.module,
            hir::DefinitionKind::Record,
            ast::Visibility::Private,
            None,
        );
        let function = self.context.add_definition(
            name,
            self.module,
            hir::DefinitionKind::Function,
            ast::Visibility::Private,
            None,
        );
        self.inherit_closure_generics(environment, span);
        self.inherit_closure_generics(function, span);
        let template = self.environment_type(environment, environment);
        self.context.program.definitions[environment.0 as usize].ty = template;
        let signature = self.context.program.types.intern(Ty::Function {
            parameters: Vec::new(),
            result: TyId::VOID,
        });
        self.context.program.definitions[function.0 as usize].ty = signature;
        let arguments = self.context.program.types.generic_arguments(environment);
        let fields = captures
            .iter()
            .map(|capture| hir::Field {
                name: capture.name.symbol,
                ty: self.closure_substitute(capture.storage_ty, parent, &arguments, span),
                visibility: ast::Visibility::Private,
                span: capture.name.span,
            })
            .collect();
        let index = self.context.program.records.len();
        self.context.program.records.push(hir::Record {
            definition: environment,
            parameters: self
                .context
                .generics
                .get(&environment)
                .cloned()
                .unwrap_or_default(),
            fields,
        });
        self.context
            .record_indices
            .resize(self.context.program.definitions.len(), None);
        self.context.record_indices[environment.0 as usize] = Some(index);
        Declaration {
            environment,
            function,
            instance: self.environment_type(environment, parent),
        }
    }

    fn environment_type(&mut self, environment: DefId, argument_owner: DefId) -> TyId {
        let arguments = self.context.program.types.generic_arguments(argument_owner);
        self.context.program.types.intern(Ty::Named {
            definition: environment,
            arguments,
        })
    }

    fn inherit_closure_generics(&mut self, owner: DefId, span: Span) {
        let parent = self.context.definition(self.definition);
        let parameters = self
            .context
            .program
            .types
            .generic_parameters(self.definition)
            .to_vec();
        let (kinds, lifetimes, bounds) = (
            parent.generic_parameter_kinds.clone(),
            parent.lifetime_parameters.clone(),
            parent.bounds.clone(),
        );
        self.context
            .program
            .types
            .register_generic_parameters(owner, &parameters);
        let arguments = self.context.program.types.generic_arguments(owner);
        let bounds = bounds
            .into_iter()
            .map(|mut bound| {
                for argument in &mut bound.trait_ref.arguments {
                    *argument = self
                        .context
                        .program
                        .types
                        .substitute_arg(*argument, self.definition, &arguments)
                        .unwrap_or_else(|error| {
                            self.context.error(
                                "E-CLOSURE-GENERIC",
                                format!("closure bound substitution failed: {error}"),
                                span,
                            );
                            *argument
                        });
                }
                bound
            })
            .collect();
        let names: Vec<_> = parameters
            .iter()
            .filter_map(|&(name, kind)| (kind == GenericParamKind::Type).then_some(name))
            .collect();
        let definition = &mut self.context.program.definitions[owner.0 as usize];
        definition.type_parameter_count = names.len() as u32;
        definition.generic_parameter_kinds = kinds;
        definition.lifetime_parameters = lifetimes;
        definition.bounds = bounds;
        self.context
            .generics
            .insert(owner, parameters.iter().map(|&(name, _)| name).collect());
    }

    fn closure_substitute(
        &mut self,
        ty: TyId,
        owner: DefId,
        arguments: &[GenericArg],
        span: Span,
    ) -> TyId {
        match self
            .context
            .program
            .types
            .substitute_generics(ty, owner, arguments)
        {
            Ok(ty) => ty,
            Err(error) => {
                self.context.error(
                    "E-CLOSURE-GENERIC",
                    format!("closure type substitution failed: {error}"),
                    span,
                );
                TyId::ERROR
            }
        }
    }
}
