use super::*;
use crate::{
    sema::const_generics::TypeScope,
    types::{ConstKind, GenericArg, GenericParamKind},
};

impl Body<'_, '_> {
    pub(super) fn repeat_expression(
        &mut self,
        value: ast::ExprId,
        count: ast::ExprId,
        expected: Option<TyId>,
        span: Span,
    ) -> (H, TyId) {
        let hint = expected.and_then(|ty| match self.type_kind(ty) {
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => Some(*inner),
            _ => None,
        });
        let value = self.expression(value, hint);
        let bindings = self.constant_bindings();
        let count = match self
            .context
            .const_length(self.module, self.definition, count, &bindings)
        {
            Ok(count) => count,
            Err(error) => {
                self.context.report_constant(error);
                return (H::Error, TyId::ERROR);
            }
        };
        let inner = self.ty(value);
        if !self.context.is_copy_type(inner) {
            self.context.error(
                "E-COPY-REPEAT",
                "array repetition requires a Copy element",
                span,
            );
        }
        let ty = match self.context.program.types.array_type(inner, count) {
            Ok(ty) => ty,
            Err(error) => {
                self.context.error("E-CONST-EVAL", error.to_string(), span);
                return (H::Error, TyId::ERROR);
            }
        };
        let kind = match self.context.program.types.const_usize(count) {
            Some(count) => H::Repeat { value, count },
            None => H::RepeatConst { value, count },
        };
        (kind, ty)
    }
    pub(super) fn resolve_explicit_generic(
        &mut self,
        argument: &ast::GenericArg,
        kind: GenericParamKind,
    ) -> Option<GenericArg> {
        let bindings = self.constant_bindings();
        let scope = TypeScope {
            module: self.module,
            owner: self.definition,
            parameters: &self.generic_types,
        };
        match self
            .context
            .resolve_generic_argument(argument, kind, scope, &bindings)
        {
            Ok(argument) => Some(argument),
            Err(error) => {
                self.context.report_constant(error);
                None
            }
        }
    }

    pub(super) fn infer_generic(
        &mut self,
        pattern: TyId,
        actual: TyId,
        owner: DefId,
        inferred: &mut [Option<GenericArg>],
        span: Span,
    ) {
        let mut pending = vec![(pattern, actual)];
        let mut remaining = 4096usize;
        while let Some((pattern, actual)) = pending.pop() {
            if remaining == 0 {
                self.context.error(
                    "E-TYPE-INFER",
                    "generic inference exceeds its work limit",
                    span,
                );
                return;
            }
            remaining -= 1;
            self.infer_pair(pattern, actual, owner, inferred, span, &mut pending);
        }
    }

    fn infer_pair(
        &mut self,
        pattern: TyId,
        actual: TyId,
        owner: DefId,
        inferred: &mut [Option<GenericArg>],
        span: Span,
        pending: &mut Vec<(TyId, TyId)>,
    ) {
        let pattern = self.type_kind(pattern).clone();
        let actual_kind = self.type_kind(actual).clone();
        if let Ty::Parameter {
            owner: found,
            index,
        } = pattern
            && found == owner
        {
            self.bind_generic(index, GenericArg::Type(actual), inferred, span);
            return;
        }
        if let Some(pair) = element_pair(&pattern, &actual_kind) {
            pending.push(pair);
            return;
        }
        match (pattern, actual_kind) {
            (Ty::SymbolicArray { inner, length }, actual) => {
                if let Some((element, count)) = self.array_arguments(actual) {
                    pending.push((inner, element));
                    self.infer_const(length, count, owner, inferred, span);
                }
            }
            (
                Ty::Named {
                    definition: a,
                    arguments: aa,
                },
                Ty::Named {
                    definition: b,
                    arguments: ba,
                },
            )
            | (
                Ty::Dynamic {
                    trait_definition: a,
                    arguments: aa,
                },
                Ty::Dynamic {
                    trait_definition: b,
                    arguments: ba,
                },
            ) if a == b => {
                self.infer_nominal(aa, ba, owner, inferred, span, pending);
            }
            (
                Ty::Function {
                    parameters: a,
                    result: ar,
                },
                Ty::Function {
                    parameters: b,
                    result: br,
                },
            ) => {
                pending.push((ar, br));
                pending.extend(a.into_iter().zip(b));
            }
            _ => {}
        }
    }

    fn array_arguments(&mut self, actual: Ty) -> Option<(TyId, crate::types::ConstId)> {
        match actual {
            Ty::Array { inner, length } => {
                Some((inner, self.context.program.types.const_value(length)))
            }
            Ty::SymbolicArray { inner, length } => Some((inner, length)),
            _ => None,
        }
    }

    fn infer_nominal(
        &mut self,
        pattern: Vec<GenericArg>,
        actual: Vec<GenericArg>,
        owner: DefId,
        inferred: &mut [Option<GenericArg>],
        span: Span,
        pending: &mut Vec<(TyId, TyId)>,
    ) {
        for (pattern, actual) in pattern.into_iter().zip(actual) {
            match (pattern, actual) {
                (GenericArg::Type(a), GenericArg::Type(b)) => pending.push((a, b)),
                (GenericArg::Const(a), GenericArg::Const(b)) => {
                    self.infer_const(a, b, owner, inferred, span)
                }
                _ => {}
            }
        }
    }

    fn infer_const(
        &mut self,
        pattern: crate::types::ConstId,
        actual: crate::types::ConstId,
        owner: DefId,
        inferred: &mut [Option<GenericArg>],
        span: Span,
    ) {
        if let ConstKind::Parameter {
            owner: found,
            index,
        } = self.context.program.types.const_term(pattern).kind
            && found == owner
        {
            self.bind_generic(index, GenericArg::Const(actual), inferred, span);
        }
    }

    fn bind_generic(
        &mut self,
        index: u32,
        actual: GenericArg,
        inferred: &mut [Option<GenericArg>],
        span: Span,
    ) {
        let Some(slot) = inferred.get_mut(index as usize) else {
            return;
        };
        match *slot {
            None => *slot = Some(actual),
            Some(expected)
                if self
                    .context
                    .program
                    .types
                    .generic_compatible(actual, expected) => {}
            Some(_) => self.context.error(
                "E-TYPE-INFER",
                "conflicting inferred generic arguments",
                span,
            ),
        }
    }

    pub(super) fn generic_constant(&mut self, name: ast::Name) -> Option<ExprId> {
        let index = self
            .context
            .program
            .types
            .generic_parameters(self.definition)
            .iter()
            .position(|&(symbol, kind)| symbol == name.symbol && kind == GenericParamKind::Const)?;
        let value = self
            .context
            .program
            .types
            .const_parameter(self.definition, index as u32);
        let ty = self.context.program.types.const_term(value).ty;
        Some(self.add_expr(H::ConstTerm(value), ty, name.span))
    }
}

fn element_pair(pattern: &Ty, actual: &Ty) -> Option<(TyId, TyId)> {
    match (pattern, actual) {
        (Ty::Reference { inner: a, .. }, Ty::Reference { inner: b, .. })
        | (Ty::Pointer { inner: a, .. }, Ty::Pointer { inner: b, .. })
        | (Ty::Array { inner: a, .. } | Ty::Slice(a), Ty::Array { inner: b, .. } | Ty::Slice(b))
        | (Ty::ForAll { inner: a, .. }, Ty::ForAll { inner: b, .. }) => Some((*a, *b)),
        _ => None,
    }
}
