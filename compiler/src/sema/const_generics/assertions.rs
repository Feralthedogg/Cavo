use super::*;

impl Context<'_> {
    pub(in crate::sema) fn check_assert_declarations(&mut self) {
        let ast = self.ast;
        for (index, item) in ast.items.iter().enumerate() {
            let Some(module) = self.item_modules[index] else {
                continue;
            };
            match &item.kind {
                ItemKind::StaticAssert(assertion) => {
                    // Module assertions have no generic binder. In particular,
                    // they must not inherit the first function's parameters.
                    self.report_assertion(assertion, module, DefId(u32::MAX));
                }
                ItemKind::Record { assertions, .. } => {
                    if let Some(owner) = self.item_definitions[index] {
                        for assertion in assertions {
                            self.report_assertion(assertion, module, owner);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn report_assertion(&mut self, assertion: &ast::StaticAssert, module: ModuleId, owner: DefId) {
        if let Err(error) =
            self.check_static_assert(assertion, module, owner, &ConstBindings::new())
        {
            self.report_constant(error);
        }
    }

    pub(in crate::sema) fn check_instantiated_assertions(&mut self) {
        let owners: HashSet<_> = self
            .program
            .constants
            .assertions
            .iter()
            .map(|a| a.owner)
            .collect();
        if owners.is_empty() {
            return;
        }
        let instances = assertion_instances(&self.program, &owners);
        for (owner, arguments, span) in instances {
            match self.program.types.generic_arguments_concrete(&arguments) {
                Ok(false) => continue,
                Ok(true) => {
                    if let Err(error) = ctfe::check_assertions(
                        &mut self.program,
                        owner,
                        &arguments,
                        ctfe::Limits::default(),
                    ) {
                        self.report_constant(error);
                    }
                }
                Err(error) => self.error("E-CONST-LIMIT", error.to_string(), span),
            }
        }
    }
}

fn assertion_instances(
    program: &hir::Program,
    owners: &HashSet<DefId>,
) -> Vec<(DefId, Vec<GenericArg>, Span)> {
    let mut instances = Vec::new();
    let mut seen = HashSet::new();
    for ty in program.types.values() {
        if let Ty::Named {
            definition,
            arguments,
        } = ty
            && owners.contains(definition)
        {
            register(
                &mut instances,
                &mut seen,
                *definition,
                arguments,
                program.definitions[definition.0 as usize].span,
            );
        }
    }
    for function in &program.functions {
        for expression in &function.expressions {
            if let hir::ExprKind::Call {
                callee,
                type_arguments,
                ..
            } = &expression.kind
                && let Some(owner) = direct_callee(function, *callee)
                && owners.contains(&owner)
            {
                register(
                    &mut instances,
                    &mut seen,
                    owner,
                    type_arguments,
                    expression.span,
                );
            }
        }
    }
    instances
}

fn register(
    instances: &mut Vec<(DefId, Vec<GenericArg>, Span)>,
    seen: &mut HashSet<(DefId, Vec<GenericArg>)>,
    owner: DefId,
    arguments: &[GenericArg],
    span: Span,
) {
    let key = (owner, arguments.to_vec());
    if seen.insert(key.clone()) {
        instances.push((owner, key.1, span));
    }
}

fn direct_callee(function: &hir::Function, mut expression: hir::ExprId) -> Option<DefId> {
    for _ in 0..128 {
        match function.expressions[expression.0 as usize].kind {
            hir::ExprKind::Definition(definition) => return Some(definition),
            hir::ExprKind::Group(inner) => expression = inner,
            _ => return None,
        }
    }
    None
}
