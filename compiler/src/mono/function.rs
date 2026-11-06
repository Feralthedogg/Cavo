use super::*;
use crate::arena::Access as _;
use crate::types::{ConstKind, ConstValue};

impl Builder<'_> {
    pub(super) fn instantiate_function(
        &mut self,
        source: &hir::Function,
        instance: &Instance,
        mapping: &mut types::Mapping,
    ) -> Result<hir::Function, Error> {
        let mut function = source.clone();
        function.definition = instance.definition;
        function.type_parameters.clear();
        let substitution = types::Substitution {
            owner: instance.key.definition,
            arguments: &instance.key.arguments,
            destination: instance.definition,
        };
        let mut mapper = types::Mapper::new(
            &mut self.program,
            substitution,
            self.options.constants,
            mapping,
        );
        function.result = mapper
            .ty(function.result)
            .map_err(|message| problem(source.body.span, "E-MONO-TYPE", message))?;
        for local in &mut function.locals {
            local.ty = mapper
                .ty(local.ty)
                .map_err(|message| problem(local.span, "E-MONO-TYPE", message))?;
        }
        let mut vtables = HashMap::new();
        for expression in &mut function.expressions {
            specialize_expression(&mut mapper, expression, &mut vtables)?;
        }
        remap_task_scopes(&mut mapper, &mut function)?;
        self.copy_modular_contract(source.definition, instance.definition);
        self.instantiate_contract_signature(source, instance, mapping)?;
        for index in 0..source.expressions.len() {
            self.retarget_expression(source, &mut function, index)?;
        }
        for &vtable in vtables.values() {
            self.retarget_vtable(vtable, source.body.span)?;
        }
        Ok(function)
    }

    fn copy_modular_contract(&mut self, source: hir::DefId, destination: hir::DefId) {
        if let Some(contract) = self.source.modular.functions.get(&source).cloned() {
            self.program.modular.functions.insert(destination, contract);
        }
        if let Some(module) = self.source.modular.imported.get(&source).cloned() {
            self.program.modular.imported.insert(destination, module);
        }
        if let Some(trust) = self.source.modular.assumptions.get(&source).cloned() {
            self.program.modular.assumptions.insert(destination, trust);
        }
    }

    fn retarget_expression(
        &mut self,
        source: &hir::Function,
        function: &mut hir::Function,
        index: usize,
    ) -> Result<(), Error> {
        let original = &source.expressions[index];
        match &original.kind {
            hir::ExprKind::Call { callee, .. } | hir::ExprKind::Spawn { callee, .. } => {
                let Some(definition) = direct_target(source, *callee) else {
                    return Ok(());
                };
                self.retarget_call(function, index, definition)
            }
            hir::ExprKind::Definition(definition)
                if self
                    .source_bodies
                    .get(definition.0 as usize)
                    .is_some_and(Option::is_some) =>
            {
                let declaration = &self.source.definitions[definition];
                if declaration
                    .generic_parameter_kinds
                    .iter()
                    .any(|kind| *kind != GenericParamKind::Lifetime)
                {
                    return Ok(());
                }
                let key = InstanceKey {
                    definition: *definition,
                    arguments: lifetime_arguments(self.source, *definition),
                };
                let target = self.enqueue(key)?;
                let definition = self.instances[target.0 as usize].definition;
                let ty = self.function_value_type(definition, original.span)?;
                function.expressions[index].kind = hir::ExprKind::Definition(definition);
                function.expressions[index].ty = ty;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn retarget_call(
        &mut self,
        function: &mut hir::Function,
        index: usize,
        mut definition: hir::DefId,
    ) -> Result<(), Error> {
        let span = function.expressions[index].span;
        if matches!(
            self.program.definitions[definition].kind,
            hir::DefinitionKind::Variant { .. }
        ) {
            return Ok(());
        }
        let (hir::ExprKind::Call { type_arguments, .. }
        | hir::ExprKind::Spawn { type_arguments, .. }) = &function.expressions[index].kind
        else {
            unreachable!();
        };
        let mut arguments = type_arguments.clone();
        if self.program.contracts.predicates.contains_key(&definition) {
            return Ok(());
        }
        if let Some(selected) = hir::traits::select_method(&self.program, definition, &arguments)
            .map_err(|error| problem(span, "E-MONO-METHOD", error.to_string()))?
        {
            definition = selected.definition;
            arguments = selected.type_arguments;
        }
        if self
            .source_bodies
            .get(definition.0 as usize)
            .is_none_or(Option::is_none)
        {
            if self.program.contracts.intrinsics.contains_key(&definition) {
                let specialized = self.specialize_intrinsic(definition, &arguments, span)?;
                return self.replace_call_target(function, index, specialized, Vec::new());
            }
            if arguments
                .iter()
                .any(|argument| !matches!(argument, GenericArg::Lifetime(_)))
            {
                return Err(problem(
                    span,
                    "E-MONO-CALL",
                    "generic external call requires a concrete ABI specialization",
                ));
            }
            return Ok(());
        }
        let target = self.enqueue(InstanceKey {
            definition,
            arguments: arguments.clone(),
        })?;
        let definition = self.instances[target.0 as usize].definition;
        self.replace_call_target(
            function,
            index,
            definition,
            arguments
                .into_iter()
                .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                .collect(),
        )
    }

    fn replace_call_target(
        &mut self,
        function: &mut hir::Function,
        index: usize,
        definition: hir::DefId,
        arguments: Vec<GenericArg>,
    ) -> Result<(), Error> {
        let span = function.expressions[index].span;
        let ty = self.function_value_type(definition, span)?;
        let callee = hir::ExprId(function.expressions.len() as u32);
        function.expressions.push(hir::Expr {
            kind: hir::ExprKind::Definition(definition),
            ty,
            span,
        });
        match &mut function.expressions[index].kind {
            hir::ExprKind::Call {
                callee: target,
                type_arguments,
                ..
            }
            | hir::ExprKind::Spawn {
                callee: target,
                type_arguments,
                ..
            } => {
                *target = callee;
                *type_arguments = arguments;
            }
            _ => unreachable!("call target specialization"),
        }
        Ok(())
    }

    fn instantiate_contract_signature(
        &mut self,
        source: &hir::Function,
        instance: &Instance,
        mapping: &mut types::Mapping,
    ) -> Result<(), Error> {
        let Some(mut header) = self
            .source
            .contracts
            .signatures
            .get(&source.definition)
            .cloned()
        else {
            return Ok(());
        };
        if header.clauses.is_empty() {
            return Ok(());
        }
        let original = header.clone();
        header.definition = instance.definition;
        let mut mapper = types::Mapper::new(
            &mut self.program,
            types::Substitution {
                owner: source.definition,
                arguments: &instance.key.arguments,
                destination: instance.definition,
            },
            self.options.constants,
            mapping,
        );
        header.result = mapper
            .ty(header.result)
            .map_err(|message| problem(source.body.span, "E-MONO-CONTRACT", message))?;
        for local in &mut header.locals {
            local.ty = mapper
                .ty(local.ty)
                .map_err(|message| problem(local.span, "E-MONO-CONTRACT", message))?;
        }
        let mut tables = HashMap::new();
        for expression in &mut header.expressions {
            specialize_expression(&mut mapper, expression, &mut tables)?;
        }
        for index in 0..original.expressions.len() {
            self.retarget_expression(&original, &mut header, index)?;
        }
        self.program
            .contracts
            .signatures
            .insert(instance.definition, header);
        Ok(())
    }

    fn function_value_type(&mut self, definition: hir::DefId, span: Span) -> Result<TyId, Error> {
        let ty = self.program.definitions[definition].ty;
        self.program
            .types
            .generalize_callable(ty, definition)
            .ok_or_else(|| {
                problem(
                    span,
                    "E-MONO-LIMIT",
                    "concrete callable generalization limit exceeded",
                )
            })
    }

    fn retarget_vtable(&mut self, index: u32, span: Span) -> Result<(), Error> {
        let mut table = self.program.vtables[index as usize].clone();
        let arguments: Vec<_> = std::iter::once(GenericArg::Type(table.concrete))
            .chain(table.trait_ref.arguments.iter().copied())
            .collect();
        for slot in &mut table.slots {
            let selected = hir::traits::select_method(&self.program, slot.declaration, &arguments)
                .map_err(|error| problem(span, "E-MONO-VTABLE", error.to_string()))?
                .ok_or_else(|| {
                    problem(
                        span,
                        "E-MONO-VTABLE",
                        "dynamic method has no concrete implementation",
                    )
                })?;
            let target = self.enqueue(InstanceKey {
                definition: selected.definition,
                arguments: selected.type_arguments.clone(),
            })?;
            slot.implementation = self.instances[target.0 as usize].definition;
            slot.signature = self.program.definitions[slot.implementation].ty;
            slot.type_arguments = selected
                .type_arguments
                .into_iter()
                .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                .collect();
        }
        self.program.vtables[index as usize] = table;
        Ok(())
    }
}

fn specialize_expression(
    mapper: &mut types::Mapper<'_, '_>,
    expression: &mut hir::Expr,
    vtables: &mut HashMap<u32, u32>,
) -> Result<(), Error> {
    let span = expression.span;
    let map_error = |message| problem(span, "E-MONO-TYPE", message);
    let callable_definition = matches!(&expression.kind, hir::ExprKind::Definition(_))
        && matches!(
            mapper.program.types.get(expression.ty),
            crate::types::Ty::Function { .. } | crate::types::Ty::ForAll { .. }
        );
    if !callable_definition {
        expression.ty = mapper.ty(expression.ty).map_err(map_error)?;
    }
    if let hir::ExprKind::Spawn {
        child_result,
        capture_type,
        ..
    } = &mut expression.kind
    {
        *child_result = mapper.ty(*child_result).map_err(map_error)?;
        *capture_type = mapper.ty(*capture_type).map_err(map_error)?;
    }
    match &mut expression.kind {
        hir::ExprKind::Call {
            type_arguments,
            parameter_types,
            ..
        }
        | hir::ExprKind::Spawn {
            type_arguments,
            parameter_types,
            ..
        } => {
            for argument in type_arguments {
                *argument = mapper.argument(*argument).map_err(map_error)?;
            }
            for ty in parameter_types {
                *ty = mapper.ty(*ty).map_err(map_error)?;
            }
        }
        hir::ExprKind::DynCall {
            parameter_types, ..
        } => {
            for ty in parameter_types {
                *ty = mapper.ty(*ty).map_err(map_error)?;
            }
        }
        hir::ExprKind::ConstTerm(value) => {
            let value = mapper.constant(*value).map_err(map_error)?;
            expression.kind =
                hir::ExprKind::Constant(constant(mapper.program, value).map_err(map_error)?);
        }
        hir::ExprKind::RepeatConst { value, count } => {
            let count = mapper.constant(*count).map_err(map_error)?;
            let count = mapper
                .program
                .types
                .const_usize(count)
                .ok_or_else(|| map_error("repeat length is not a concrete usize".into()))?;
            expression.kind = hir::ExprKind::Repeat {
                value: *value,
                count,
            };
        }
        hir::ExprKind::Match { arms, .. } => {
            for arm in arms {
                specialize_pattern(mapper, &mut arm.pattern, 0).map_err(map_error)?;
            }
        }
        hir::ExprKind::DynCoerce { vtable, .. } => {
            *vtable = specialized_vtable(mapper, *vtable, vtables).map_err(map_error)?;
        }
        _ => {}
    }
    Ok(())
}

fn remap_task_scopes(
    mapper: &mut types::Mapper<'_, '_>,
    function: &mut hir::Function,
) -> Result<(), Error> {
    let mut remapped = HashMap::new();
    for statement in &mut function.statements {
        if let hir::StmtKind::TaskScope { scope, .. } = &mut statement.kind {
            let old = mapper.program.tasks.scopes[*scope as usize].clone();
            let GenericArg::Lifetime(region) = mapper
                .argument(GenericArg::Lifetime(old.region))
                .map_err(|message| problem(statement.span, "E-MONO-TASK", message))?
            else {
                unreachable!("scope region");
            };
            let next = mapper.program.tasks.scopes.len() as u32;
            mapper.program.tasks.scopes.push(crate::tasks::Scope {
                owner: function.definition,
                region,
                span: old.span,
            });
            remapped.insert(*scope, next);
            *scope = next;
        }
    }
    for expression in &mut function.expressions {
        if let hir::ExprKind::Spawn { scope, .. } = &mut expression.kind {
            *scope = *remapped.get(scope).ok_or_else(|| {
                problem(
                    expression.span,
                    "E-MONO-TASK",
                    "spawn lost its owning scope",
                )
            })?;
        }
    }
    Ok(())
}

fn specialized_vtable(
    mapper: &mut types::Mapper<'_, '_>,
    original: u32,
    cache: &mut HashMap<u32, u32>,
) -> Result<u32, String> {
    if let Some(&index) = cache.get(&original) {
        return Ok(index);
    }
    let mut table = mapper
        .program
        .vtables
        .get(original as usize)
        .cloned()
        .ok_or("invalid source vtable ID")?;
    table.concrete = mapper.ty(table.concrete)?;
    for argument in &mut table.trait_ref.arguments {
        *argument = mapper.argument(*argument)?;
    }
    for slot in &mut table.slots {
        slot.signature = mapper.ty(slot.signature)?;
        for argument in &mut slot.type_arguments {
            *argument = mapper.argument(*argument)?;
        }
    }
    let index = mapper.program.vtables.len() as u32;
    mapper.program.vtables.push(table);
    cache.insert(original, index);
    Ok(index)
}

fn specialize_pattern(
    mapper: &mut types::Mapper<'_, '_>,
    pattern: &mut hir::Pattern,
    depth: usize,
) -> Result<(), String> {
    if depth >= 128 {
        return Err("pattern specialization depth limit exceeded".into());
    }
    pattern.ty = mapper.ty(pattern.ty)?;
    if let hir::PatternKind::Variant { fields, .. } = &mut pattern.kind {
        for field in fields {
            specialize_pattern(mapper, field, depth + 1)?;
        }
    }
    Ok(())
}
fn constant(program: &hir::Program, value: crate::types::ConstId) -> Result<hir::Constant, String> {
    match program.types.const_term(value).kind {
        ConstKind::Value(ConstValue::Usize(value)) => Ok(hir::Constant::Integer {
            magnitude: u128::from(value),
            negative: false,
        }),
        ConstKind::Value(ConstValue::Bool(value)) => Ok(hir::Constant::Bool(value)),
        _ => Err("constant term remains unresolved after instantiation".into()),
    }
}
fn direct_target(function: &hir::Function, mut expression: hir::ExprId) -> Option<hir::DefId> {
    for _ in 0..128 {
        match function.expressions.get_id(expression)?.kind {
            hir::ExprKind::Definition(definition) => return Some(definition),
            hir::ExprKind::Group(inner) => expression = inner,
            _ => return None,
        }
    }
    None
}
fn lifetime_arguments(program: &hir::Program, definition: hir::DefId) -> Vec<GenericArg> {
    program
        .types
        .generic_parameters(definition)
        .iter()
        .map(|(name, _)| {
            GenericArg::Lifetime(Region::Named {
                owner: definition,
                name: *name,
            })
        })
        .collect()
}
