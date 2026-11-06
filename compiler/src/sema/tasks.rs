use super::*;
use crate::syntax::token::TokenKind;
use crate::types::GenericParamKind as Kind;

impl Context<'_> {
    pub(super) fn register_task_roles(&mut self) {
        for index in 0..self.program.definitions.len() {
            let definition = DefId(index as u32);
            let item = self.definition(definition).clone();
            for attribute in &item.attributes {
                use crate::tasks::transfer::Property as P;
                let values: &[P] = match self.symbols.get(attribute.name) {
                    "thread_bound" => &[P::Send, P::Sync],
                    "task_bound" => &[P::TaskTransfer],
                    "park_unsafe" => &[P::SuspendSafe],
                    _ => &[],
                };
                self.program
                    .tasks
                    .forbidden
                    .entry(definition)
                    .or_default()
                    .extend(values);
            }
            let roles: Vec<_> = item
                .attributes
                .iter()
                .filter(|a| self.symbols.get(a.name) == "lang")
                .filter_map(|a| match a.arguments.as_slice() {
                    [
                        crate::syntax::token::Token {
                            kind: TokenKind::Ident(name),
                            ..
                        },
                    ] => Some(self.symbols.get(*name)),
                    _ => None,
                })
                .collect();
            for role in roles {
                self.register_task_role(definition, role, &item);
            }
        }
    }

    fn register_task_role(&mut self, definition: DefId, role: &str, item: &hir::Definition) {
        let (valid, previous) = match role {
            "task" => (
                item.kind == D::Record
                    && item.generic_parameter_kinds == [Kind::Lifetime, Kind::Type],
                self.program.tasks.task,
            ),
            "spawn_error" => (
                item.kind == D::Record && item.generic_parameter_kinds == [Kind::Type],
                self.program.tasks.spawn_error,
            ),
            "task_error" => (
                matches!(item.kind, D::Record | D::Enum) && item.generic_parameter_kinds.is_empty(),
                self.program.tasks.task_error,
            ),
            _ => return,
        };
        if !valid || previous.is_some() {
            self.error(
                "E-LANG-TASK",
                "task language role has an incompatible declaration or duplicate provider",
                item.span,
            );
            return;
        }
        if role == "task"
            && self
                .program
                .records
                .iter()
                .find(|r| r.definition == definition)
                .is_some_and(|r| !r.fields.is_empty())
        {
            self.error(
                "E-LANG-TASK",
                "task observation storage is opaque and cannot declare user fields",
                item.span,
            );
            return;
        }
        if role == "spawn_error" {
            let valid_capture = self.program.records.iter().find(|r| r.definition == definition)
                .is_some_and(|record| matches!(record.fields.as_slice(), [field]
                    if matches!(self.program.types.get(field.ty), Ty::Parameter { owner, index: 0 } if *owner == definition)));
            if !valid_capture {
                self.error(
                    "E-LANG-TASK",
                    "spawn_error must own exactly its original capture bundle",
                    item.span,
                );
                return;
            }
        }
        match role {
            "task" => self.program.tasks.task = Some(definition),
            "spawn_error" => self.program.tasks.spawn_error = Some(definition),
            "task_error" => self.program.tasks.task_error = Some(definition),
            _ => {}
        }
    }

    pub(super) fn validate_task_intrinsics(&mut self) {
        use crate::contracts::Intrinsic as I;
        let roles = self.program.contracts.intrinsics.clone();
        for (definition, role) in roles {
            if !matches!(role, I::TaskJoin | I::TaskIgnore | I::TaskCancel) {
                continue;
            }
            let declaration = self.definition(definition);
            let valid = crate::tasks::intrinsic_shape(&self.program, declaration.ty, role);
            if !valid {
                self.error("E-LANG-TASK", "task operation does not preserve its Task, value and error declaration identities", declaration.span);
            }
        }
    }
}

pub(super) fn validate_escapes(context: &mut Context<'_>) {
    let mut failures = Vec::new();
    for function in &context.program.functions {
        let owned: Vec<_> = context
            .program
            .tasks
            .scopes
            .iter()
            .filter(|scope| scope.owner == function.definition)
            .map(|scope| scope.region)
            .collect();
        for statement in &function.statements {
            if let hir::StmtKind::Return(Some(value)) = statement.kind
                && contains_scope(&context.program, function.expressions[value].ty, &owned, 0)
            {
                failures.push(statement.span);
            }
        }
    }
    for span in failures {
        context.error(
            "E-TASK-ESCAPE",
            "a scoped task handle cannot escape its owning scope",
            span,
        );
    }
}

fn contains_scope(program: &hir::Program, ty: TyId, regions: &[Region], depth: usize) -> bool {
    if depth >= 64 {
        return true;
    }
    if let Some((region, _)) = crate::tasks::task_arguments(program, ty) {
        return regions.contains(&region);
    }
    match program.types.get(ty) {
        Ty::Named { arguments, .. } => arguments.iter().any(|argument| match argument {
            crate::types::GenericArg::Type(ty) => contains_scope(program, *ty, regions, depth + 1),
            _ => false,
        }),
        Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Reference { inner, .. } => {
            contains_scope(program, *inner, regions, depth + 1)
        }
        _ => false,
    }
}

pub(super) fn contains_task(program: &hir::Program, ty: TyId, depth: usize) -> bool {
    if depth >= 64 {
        return true;
    }
    if crate::tasks::task_arguments(program, ty).is_some() {
        return true;
    }
    match program.types.get(ty) {
        Ty::Named { arguments, .. } => arguments.iter().any(|argument| match argument {
            crate::types::GenericArg::Type(ty) => contains_task(program, *ty, depth + 1),
            _ => false,
        }),
        Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Reference { inner, .. } => {
            contains_task(program, *inner, depth + 1)
        }
        _ => false,
    }
}

pub(super) fn validate_callable_identities(context: &mut Context<'_>) {
    let mut failures = Vec::new();
    let mut affinity_failures = Vec::new();
    for function in &context.program.functions {
        let protected = context
            .program
            .modular
            .functions
            .get(&function.definition)
            .is_some_and(|contract| contract.affinity)
            || context
                .definition(function.definition)
                .attributes
                .iter()
                .any(|attribute| context.symbols.get(attribute.name) == "nopreempt");
        let (direct, spawned) = callable_uses(function);
        for (index, expression) in function.expressions.iter().enumerate() {
            let hir::ExprKind::Definition(definition) = expression.kind else {
                continue;
            };
            let id = hir::ExprId(index as u32);
            let item = context.definition(definition);
            let affinity = context
                .program
                .modular
                .functions
                .get(&definition)
                .is_some_and(|c| c.affinity);
            if affinity && direct.contains(&id) && !spawned.contains(&id) && !protected {
                affinity_failures.push(expression.span);
            }
            let special = affinity
                || has_required_contract(&context.program, definition)
                || item.foreign_abi.is_some()
                || context
                    .program
                    .contracts
                    .intrinsics
                    .contains_key(&definition);
            if special
                && (!direct.contains(&id)
                    || spawned.contains(&id) && (affinity || item.foreign_abi.is_some()))
            {
                failures.push(expression.span);
            }
        }
    }
    for span in failures {
        context.error("E-CALLABLE-IDENTITY", "this function carries compiler, contract, ABI or thread-affinity obligations; use its direct checked call boundary", span);
    }
    for span in affinity_failures {
        context.error("E-CALLABLE-AFFINITY", "a freely movable function cannot call thread-bound code; declare a compatible thread-bound or nopreempt context", span);
    }
}

fn callable_uses(function: &hir::Function) -> (HashSet<hir::ExprId>, HashSet<hir::ExprId>) {
    let mut direct = HashSet::new();
    let mut spawned = HashSet::new();
    for expression in &function.expressions {
        let (callee, sites) = match expression.kind {
            hir::ExprKind::Call { callee, .. } => (callee, &mut direct),
            hir::ExprKind::Spawn { callee, .. } => (callee, &mut spawned),
            _ => continue,
        };
        collect_callee(function, callee, sites);
    }
    (direct, spawned)
}

fn collect_callee(function: &hir::Function, mut id: hir::ExprId, sites: &mut HashSet<hir::ExprId>) {
    for _ in 0..128 {
        sites.insert(id);
        match function.expressions[id].kind {
            hir::ExprKind::Group(inner) => id = inner,
            _ => return,
        }
    }
}

fn has_required_contract(program: &hir::Program, definition: DefId) -> bool {
    let required = |definition: DefId| {
        program.definitions[definition]
            .declaration_clauses
            .iter()
            .any(|(kind, _)| *kind == ast::ClauseKind::Requires)
    };
    required(definition)
        || program
            .implementations
            .iter()
            .flat_map(|item| &item.methods)
            .filter(|method| method.implementation == definition)
            .filter_map(|method| method.declaration)
            .any(required)
}
