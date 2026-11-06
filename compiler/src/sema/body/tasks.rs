use super::*;
use crate::{
    local::properties::Properties,
    tasks::transfer::{self, Property},
    types::GenericArg,
};
mod capture;

impl Body<'_, '_> {
    pub(super) fn task_scope(&mut self, body: &ast::Block, span: Span) -> (S, bool) {
        let region = self.context.program.types.fresh_region();
        let scope = self.context.program.tasks.scopes.len() as u32;
        self.context.program.tasks.scopes.push(crate::tasks::Scope {
            owner: self.definition,
            region,
            span,
        });
        self.task_scopes.push((scope, region));
        let (body, falls) = self.block(body);
        self.task_scopes.pop();
        (S::TaskScope { scope, body }, falls)
    }

    pub(super) fn spawn(&mut self, operand: ast::ExprId, span: Span) -> ExprId {
        let Some(&(scope, region)) = self.task_scopes.last() else {
            self.context.error(
                "E-TASK-SCOPE",
                "spawn requires an active structured task scope",
                span,
            );
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let child = self.expression(operand, None);
        let H::Call {
            callee,
            type_arguments,
            arguments,
            parameter_types,
        } = self.expr(child).kind.clone()
        else {
            self.context.error(
                "E-TASK-SPAWN",
                "spawn requires a typed call; invoke an explicit closure to spawn it",
                span,
            );
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let child_result = self.ty(child);
        self.check_task_transfer(&parameter_types, child_result, span);
        let Some((task, error, result)) = self.task_providers(span) else {
            return self.add_expr(H::Error, TyId::ERROR, span);
        };
        let child_signature = self.context.program.types.intern(Ty::Function {
            parameters: parameter_types.clone(),
            result: child_result,
        });
        let capture_type = self.task_capture(child_signature, &parameter_types, child, span);
        let handle = self.context.program.types.intern(Ty::Named {
            definition: task,
            arguments: vec![GenericArg::Lifetime(region), GenericArg::Type(child_result)],
        });
        let error = self.context.program.types.intern(Ty::Named {
            definition: error,
            arguments: vec![GenericArg::Type(capture_type)],
        });
        let ty = self.context.program.types.intern(Ty::Named {
            definition: result,
            arguments: vec![GenericArg::Type(handle), GenericArg::Type(error)],
        });
        self.add_expr(
            H::Spawn {
                scope,
                callee,
                type_arguments,
                arguments,
                parameter_types,
                child_result,
                capture_type,
            },
            ty,
            span,
        )
    }

    fn task_providers(&mut self, span: Span) -> Option<(DefId, DefId, DefId)> {
        match (
            self.context.program.tasks.task,
            self.context.program.tasks.spawn_error,
            self.context.result_item,
        ) {
            (Some(task), Some(error), Some(result)) => Some((task, error, result)),
            _ => {
                self.context.error("E-TASK-LIBRARY", "spawn requires actual @lang(task), @lang(spawn_error), and @lang(result) declarations", span);
                None
            }
        }
    }

    fn check_task_transfer(&mut self, inputs: &[TyId], result: TyId, span: Span) {
        let properties = Properties::compute(&mut self.context.program);
        for ty in inputs.iter().copied().chain(std::iter::once(result)) {
            for property in [Property::Send, Property::TaskTransfer] {
                if let Err(reason) =
                    transfer::check(&self.context.program, &properties, ty, property)
                {
                    self.context.error(
                        "E-TASK-TRANSFER",
                        format!("cannot transfer this value to another task: {reason}"),
                        span,
                    );
                }
            }
        }
    }

    fn task_capture(
        &mut self,
        callee: TyId,
        parameters: &[TyId],
        child: ExprId,
        span: Span,
    ) -> TyId {
        let name = ast::Name {
            symbol: self.context.definition(self.definition).name,
            span,
        };
        let record = self.context.add_definition(
            name,
            self.module,
            hir::DefinitionKind::Record,
            ast::Visibility::Private,
            None,
        );
        self.inherit_closure_generics(record, span);
        let own = self.context.program.types.generic_arguments(record);
        let fields = std::iter::once(callee)
            .chain(parameters.iter().copied())
            .map(|ty| {
                let ty = self.closure_substitute(ty, self.definition, &own, span);
                hir::Field {
                    name: name.symbol,
                    ty,
                    visibility: ast::Visibility::Private,
                    span,
                }
            })
            .collect();
        let template = self.environment_type(record, record);
        self.context.program.definitions[record].ty = template;
        let index = self.context.program.records.len();
        self.context.program.records.push(hir::Record {
            definition: record,
            parameters: self
                .context
                .generics
                .get(&record)
                .cloned()
                .unwrap_or_default(),
            fields,
        });
        self.context
            .record_indices
            .resize(self.context.program.definitions.len(), None);
        self.context.record_indices[record.0 as usize] = Some(index);
        self.context.program.tasks.captures.push(record);
        self.task_capture_invoker(record, child, span);
        self.environment_type(record, self.definition)
    }
}
