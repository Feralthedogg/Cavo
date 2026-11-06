use super::*;
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
        for index in 0..source.expressions.len() {
            self.retarget_expression(source, &mut function, index)?;
        }
        for &vtable in vtables.values() {
            self.retarget_vtable(vtable, source.body.span)?;
        }
        Ok(function)
    }

    fn retarget_expression(
        &mut self,
        source: &hir::Function,
        function: &mut hir::Function,
        index: usize,
    ) -> Result<(), Error> {
        let original = &source.expressions[index];
        match &original.kind {
            hir::ExprKind::Call { callee, .. } => {
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
                let declaration = &self.source.definitions[definition.0 as usize];
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
            self.program.definitions[definition.0 as usize].kind,
            hir::DefinitionKind::Variant { .. }
        ) {
            return Ok(());
        }
        let hir::ExprKind::Call { type_arguments, .. } = &function.expressions[index].kind else {
            unreachable!();
        };
        let mut arguments = type_arguments.clone();
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
        let ty = self.function_value_type(definition, span)?;
        let callee = hir::ExprId(function.expressions.len() as u32);
        function.expressions.push(hir::Expr {
            kind: hir::ExprKind::Definition(definition),
            ty,
            span,
        });
        let hir::ExprKind::Call {
            callee: replaced,
            type_arguments,
            ..
        } = &mut function.expressions[index].kind
        else {
            unreachable!();
        };
        *replaced = callee;
        *type_arguments = arguments
            .into_iter()
            .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
            .collect();
        Ok(())
    }

    fn function_value_type(&mut self, definition: hir::DefId, span: Span) -> Result<TyId, Error> {
        let ty = self.program.definitions[definition.0 as usize].ty;
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
            slot.signature = self.program.definitions[slot.implementation.0 as usize].ty;
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
    match &mut expression.kind {
        hir::ExprKind::Call {
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
        match function.expressions.get(expression.0 as usize)?.kind {
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
