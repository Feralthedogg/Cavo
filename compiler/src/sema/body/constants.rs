use super::*;
use crate::{
    ctfe::{Value, ValueKind},
    sema::constants::{ConstBinding, ConstBindings},
};

impl Body<'_, '_> {
    pub(super) fn constant_bindings(&self) -> ConstBindings {
        let mut bindings: ConstBindings = self
            .uncaptured
            .iter()
            .map(|&name| (name, ConstBinding::Runtime))
            .collect();
        for scope in &self.scopes {
            for (&name, local) in scope {
                bindings.insert(
                    name,
                    self.constant_values
                        .get(local)
                        .cloned()
                        .unwrap_or(ConstBinding::Runtime),
                );
            }
        }
        bindings
    }

    pub(super) fn constant_initializer(
        &mut self,
        variable: &ast::Variable,
        ty: TyId,
    ) -> Option<ConstBinding> {
        if !variable.constant {
            return None;
        }
        let expression = variable.initializer?;
        let bindings = self.constant_bindings();
        if matches!(
            self.context.program.types.get(ty),
            Ty::Bool
                | Ty::Integer {
                    signed: false,
                    bits: 0
                }
        ) {
            return self
                .context
                .const_expression(self.module, self.definition, expression, ty, &bindings)
                .ok()
                .map(ConstBinding::Term);
        }
        self.context
            .eval_constant(self.module, self.definition, expression, ty, &bindings)
            .ok()
            .map(ConstBinding::Value)
    }

    pub(super) fn constant_expression(&mut self, definition: DefId, span: Span) -> ExprId {
        match self.context.constant_value(definition) {
            Ok(value) => self.materialize_constant(value, span),
            Err(error) => {
                self.context.report_constant(error);
                self.add_expr(H::Error, TyId::ERROR, span)
            }
        }
    }

    pub(super) fn materialize_constant(&mut self, value: Value, span: Span) -> ExprId {
        let ty = value.ty;
        if let Some(value) = value.scalar() {
            return self.add_expr(H::Constant(value), ty, span);
        }
        match value.kind {
            ValueKind::Array(values) => {
                let values = values
                    .into_iter()
                    .map(|value| self.materialize_constant(value, span))
                    .collect();
                self.add_expr(H::Array(values), ty, span)
            }
            ValueKind::Record { definition, fields } => {
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| (index as u32, self.materialize_constant(value, span)))
                    .collect();
                self.add_expr(H::Record { definition, fields }, ty, span)
            }
            _ => {
                self.context.error(
                    "E-CONST-CONTEXT",
                    "constant cannot be used as a runtime value",
                    span,
                );
                self.add_expr(H::Error, TyId::ERROR, span)
            }
        }
    }

    pub(super) fn static_assertion(&mut self, assertion: &ast::StaticAssert) -> S {
        let bindings = self.constant_bindings();
        if let Err(error) =
            self.context
                .check_static_assert(assertion, self.module, self.definition, &bindings)
        {
            self.context.report_constant(error);
            return S::Error;
        }
        S::Empty
    }
}
