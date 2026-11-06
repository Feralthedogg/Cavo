mod assertions;
mod terms;

use super::constants::ConstBindings;
use super::*;
use crate::{
    ctfe,
    types::{ConstId, GenericArg, GenericParamKind},
};

#[derive(Clone, Copy)]
pub(super) struct TypeScope<'a> {
    pub module: ModuleId,
    pub owner: DefId,
    pub parameters: &'a HashMap<Symbol, TyId>,
}

impl Context<'_> {
    pub(super) fn collect_generic_parameters(
        &mut self,
        owner: DefId,
        generics: &[GenericParam],
        _allow_lifetimes: bool,
    ) {
        let mut names = HashSet::new();
        let mut metadata = Vec::with_capacity(generics.len());
        let mut lifetimes = Vec::new();
        for (index, parameter) in generics.iter().enumerate() {
            let (name, kind) = match parameter {
                GenericParam::Type { name, .. } => (*name, GenericParamKind::Type),
                GenericParam::Lifetime(name) => (*name, GenericParamKind::Lifetime),
                GenericParam::Const { name, ty } => {
                    self.const_parameter_types
                        .insert((owner, index as u32), *ty);
                    (*name, GenericParamKind::Const)
                }
            };
            if !names.insert(name.symbol) {
                self.error("E-NAME-DUPLICATE", "duplicate generic parameter", name.span);
            }
            if kind == GenericParamKind::Lifetime {
                if self.symbols.get(name.symbol) == "static" {
                    self.error(
                        "E-REGION-NAME",
                        "'static is predefined and cannot be declared",
                        name.span,
                    );
                }
                lifetimes.push(name.symbol);
            }
            metadata.push((name.symbol, kind));
        }
        let definition = &mut self.program.definitions[owner.0 as usize];
        definition.type_parameter_count = metadata
            .iter()
            .filter(|(_, kind)| *kind == GenericParamKind::Type)
            .count() as u32;
        definition.generic_parameter_kinds = metadata.iter().map(|(_, kind)| *kind).collect();
        definition.lifetime_parameters = lifetimes;
        self.generics
            .insert(owner, metadata.iter().map(|(name, _)| *name).collect());
        self.program
            .types
            .register_generic_parameters(owner, &metadata);
    }

    pub(super) fn parameters(&mut self, owner: DefId) -> HashMap<Symbol, TyId> {
        let metadata = self.program.types.generic_parameters(owner).to_vec();
        let mut values = metadata
            .into_iter()
            .enumerate()
            .filter(|(_, (_, kind))| *kind == GenericParamKind::Type)
            .map(|(index, (name, _))| {
                (
                    name,
                    self.program.types.intern(Ty::Parameter {
                        owner,
                        index: index as u32,
                    }),
                )
            })
            .collect();
        self.add_method_self(owner, &mut values);
        values
    }

    pub(super) fn parameter_arguments(&mut self, owner: DefId) -> Vec<GenericArg> {
        self.program.types.generic_arguments(owner)
    }

    pub(super) fn validate_const_parameters(&mut self, owner: DefId) {
        let parameters = self.parameters(owner);
        let module = self.definition(owner).module;
        let entries: Vec<_> = self
            .const_parameter_types
            .iter()
            .filter_map(|(&(found, _), &ty)| (found == owner).then_some(ty))
            .collect();
        for syntax in entries {
            let ty = self.resolve_type(syntax, module, owner, &parameters);
            if !matches!(
                self.program.types.get(ty),
                Ty::Integer {
                    signed: false,
                    bits: 0
                }
            ) {
                self.error(
                    "E-GENERIC-KIND",
                    "const generic parameters must have type usize",
                    self.ast.ty(syntax).span,
                );
            }
        }
    }

    pub(super) fn resolve_generic_argument(
        &mut self,
        argument: &ast::GenericArg,
        kind: GenericParamKind,
        scope: TypeScope<'_>,
        bindings: &ConstBindings,
    ) -> Result<GenericArg, ctfe::Error> {
        let span = self.generic_argument_span(argument);
        match (kind, argument) {
            (GenericParamKind::Type, ast::GenericArg::Type(ty)) => {
                Ok(GenericArg::Type(self.resolve_type_with_bindings(
                    *ty,
                    scope.module,
                    scope.owner,
                    scope.parameters,
                    bindings,
                )))
            }
            (GenericParamKind::Type, ast::GenericArg::Path(path)) => Ok(GenericArg::Type(
                self.resolve_path_type(path, &[], scope, bindings, span),
            )),
            (GenericParamKind::Const, ast::GenericArg::Const(value)) => {
                let ty = self.program.types.builtin("usize").expect("usize type");
                self.const_expression(scope.module, scope.owner, *value, ty, bindings)
                    .map(GenericArg::Const)
            }
            (GenericParamKind::Const, ast::GenericArg::Path(path)) => {
                let value = self.const_path(scope.module, scope.owner, path, bindings, span)?;
                if !matches!(
                    self.program
                        .types
                        .get(self.program.types.const_term(value).ty),
                    Ty::Integer {
                        signed: false,
                        bits: 0
                    }
                ) {
                    return Err(ctfe::Error::new(
                        "E-GENERIC-KIND",
                        "const generic arguments must have type usize",
                        span,
                    ));
                }
                Ok(GenericArg::Const(value))
            }
            (GenericParamKind::Lifetime, ast::GenericArg::Lifetime(name)) => self
                .resolve_lifetime(*name, scope.owner)
                .map(GenericArg::Lifetime),
            _ => Err(ctfe::Error::new(
                "E-GENERIC-KIND",
                format!("expected a {kind:?} generic argument"),
                span,
            )),
        }
    }

    pub(super) fn generic_argument_span(&self, argument: &ast::GenericArg) -> Span {
        match argument {
            ast::GenericArg::Type(ty) => self.ast.ty(*ty).span,
            ast::GenericArg::Const(value) => self.ast.expr(*value).span,
            ast::GenericArg::Path(path) => path
                .first()
                .expect("generic path")
                .span
                .join(path.last().expect("generic path").span),
            ast::GenericArg::Lifetime(name) => name.span,
        }
    }

    pub(super) fn resolve_generic_arguments(
        &mut self,
        definition: DefId,
        arguments: &[ast::GenericArg],
        scope: TypeScope<'_>,
        bindings: &ConstBindings,
        span: Span,
    ) -> Result<Vec<GenericArg>, ctfe::Error> {
        let kinds = self.definition(definition).generic_parameter_kinds.clone();
        let implicit_lifetimes = arguments.len()
            == kinds
                .iter()
                .filter(|&&kind| kind != GenericParamKind::Lifetime)
                .count()
            && !arguments
                .iter()
                .any(|arg| matches!(arg, ast::GenericArg::Lifetime(_)));
        if !implicit_lifetimes && arguments.len() != kinds.len() {
            return Err(ctfe::Error::new(
                "E-TYPE-ARITY",
                format!(
                    "expected {} generic arguments, found {}",
                    kinds.len(),
                    arguments.len()
                ),
                span,
            ));
        }
        let mut syntax = arguments.iter();
        kinds
            .into_iter()
            .map(|kind| {
                if kind == GenericParamKind::Lifetime && implicit_lifetimes {
                    return Ok(GenericArg::Lifetime(self.program.types.fresh_region()));
                }
                self.resolve_generic_argument(
                    syntax.next().expect("generic arity checked"),
                    kind,
                    scope,
                    bindings,
                )
            })
            .collect()
    }

    pub(super) fn resolve_lifetime(&self, name: Name, owner: DefId) -> Result<Region, ctfe::Error> {
        if self.symbols.get(name.symbol) == "static" {
            return Ok(Region::Static);
        }
        for (depth, binder) in self.region_binders.iter().rev().enumerate() {
            if let Some(index) = binder.iter().position(|&symbol| symbol == name.symbol) {
                return Ok(Region::Bound {
                    depth: depth as u16,
                    index: index as u16,
                });
            }
        }
        if self
            .program
            .definitions
            .get(owner.0 as usize)
            .is_some_and(|definition| definition.lifetime_parameters.contains(&name.symbol))
        {
            return Ok(Region::Named {
                owner,
                name: name.symbol,
            });
        }
        Err(ctfe::Error::new(
            "E-REGION-NAME",
            "generic argument names an undeclared lifetime",
            name.span,
        ))
    }

    pub(super) fn resolve_path_type(
        &mut self,
        path: &[Name],
        arguments: &[ast::GenericArg],
        scope: TypeScope<'_>,
        bindings: &ConstBindings,
        span: Span,
    ) -> TyId {
        if path.len() == 1 {
            if self.symbols.get(path[0].symbol) == "ptr" {
                return self.pointer_type(arguments, scope, bindings, span);
            }
            let simple = scope
                .parameters
                .get(&path[0].symbol)
                .copied()
                .or_else(|| self.program.types.builtin(self.symbols.get(path[0].symbol)));
            if let Some(ty) = simple {
                if !arguments.is_empty() {
                    self.error(
                        "E-TYPE-ARITY",
                        "this type does not accept generic arguments",
                        span,
                    );
                }
                return ty;
            }
        }
        let Some(definition) = self.resolve(scope.module, path) else {
            return TyId::ERROR;
        };
        if !matches!(
            self.definition(definition).kind,
            D::Record | D::Union | D::Enum | D::TypeAlias
        ) {
            self.error(
                "E-TYPE-NAME",
                "this name does not denote a value type",
                span,
            );
            return TyId::ERROR;
        }
        let arguments =
            match self.resolve_generic_arguments(definition, arguments, scope, bindings, span) {
                Ok(arguments) => arguments,
                Err(error) => {
                    self.error(error.code, error.message, error.span);
                    return TyId::ERROR;
                }
            };
        self.instantiate_named_type(definition, arguments, span)
    }

    fn instantiate_named_type(
        &mut self,
        definition: DefId,
        arguments: Vec<GenericArg>,
        span: Span,
    ) -> TyId {
        self.check_generic_bounds(definition, &arguments, span);
        let ty = if self.definition(definition).kind == D::TypeAlias {
            let target = self.resolve_alias(definition, span);
            self.program
                .types
                .instantiate_alias(target, definition, &arguments)
                .unwrap_or_else(|error| {
                    let code = match error {
                        crate::types::ConstError::Limit => "E-TYPE-ALIAS-LIMIT",
                        _ => "E-CONST-EVAL",
                    };
                    self.error(code, error.to_string(), span);
                    TyId::ERROR
                })
        } else {
            self.program.types.intern(Ty::Named {
                definition,
                arguments,
            })
        };
        match ctfe::normalize_type_constants(&mut self.program, ty, ctfe::Limits::default()) {
            Ok(ty) => ty,
            Err(error) => {
                self.report_constant(error);
                TyId::ERROR
            }
        }
    }

    fn pointer_type(
        &mut self,
        arguments: &[ast::GenericArg],
        scope: TypeScope<'_>,
        bindings: &ConstBindings,
        span: Span,
    ) -> TyId {
        let [argument] = arguments else {
            self.error("E-TYPE-ARITY", "ptr requires one type argument", span);
            return TyId::ERROR;
        };
        let (constant, inner) = match argument {
            ast::GenericArg::Type(ty) => match self.ast.ty(*ty).kind {
                TypeKind::Const(inner) => (
                    true,
                    self.resolve_type_with_bindings(
                        inner,
                        scope.module,
                        scope.owner,
                        scope.parameters,
                        bindings,
                    ),
                ),
                _ => (
                    false,
                    self.resolve_type_with_bindings(
                        *ty,
                        scope.module,
                        scope.owner,
                        scope.parameters,
                        bindings,
                    ),
                ),
            },
            ast::GenericArg::Path(path) => (
                false,
                self.resolve_path_type(path, &[], scope, bindings, span),
            ),
            _ => {
                self.error("E-GENERIC-KIND", "ptr requires a type argument", span);
                return TyId::ERROR;
            }
        };
        self.program.types.intern(Ty::Pointer { constant, inner })
    }
}
