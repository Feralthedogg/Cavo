use super::*;

pub(super) fn metadata(program: &Program) -> Result<(), InvariantError> {
    for (index, module) in program.modules.iter().enumerate() {
        for &id in &module.definitions {
            require(
                program
                    .definitions
                    .get(id.0 as usize)
                    .is_some_and(|definition| definition.module.0 as usize == index),
                "module contains an invalid definition ID",
            )?;
        }
    }
    for definition in &program.definitions {
        declaration(program, definition)?;
    }
    for record in &program.records {
        record_metadata(program, record)?;
    }
    for enumeration in &program.enums {
        enum_metadata(program, enumeration)?;
    }
    Ok(())
}

fn declaration(program: &Program, definition: &Definition) -> Result<(), InvariantError> {
    body::const_origin(program, definition)?;
    require(
        definition.lifetime_parameters.len() <= 64,
        "definition exceeds the lifetime binder limit",
    )?;
    let mut lifetimes = std::collections::HashSet::new();
    require(
        definition
            .lifetime_parameters
            .iter()
            .all(|name| lifetimes.insert(name)),
        "duplicate lifetime binder",
    )?;
    require(
        (definition.module.0 as usize) < program.modules.len(),
        "definition has an invalid module ID",
    )?;
    require(
        definition.ty != TyId::ERROR && (definition.ty.0 as usize) < program.types.values().len(),
        "definition has an invalid type",
    )?;
    require(
        program.types.valid_region_scope(definition.ty),
        "definition has an escaping bound region or invalid callable binder",
    )?;
    require(
        definition
            .generic_parameter_kinds
            .iter()
            .filter(|&&kind| kind == crate::types::GenericParamKind::Type)
            .count()
            == definition.type_parameter_count as usize,
        "generic kind and type-parameter dimensions differ",
    )?;
    for attribute in &definition.attributes {
        if let Some(id) = attribute.constant {
            require(
                program
                    .types
                    .constant_terms()
                    .get(id.0 as usize)
                    .is_some_and(|term| {
                        matches!(
                            program.types.get(term.ty),
                            Ty::Integer {
                                signed: false,
                                bits: 0
                            }
                        )
                    }),
                "invalid attribute constant",
            )?;
        }
    }
    Ok(())
}

fn record_metadata(program: &Program, record: &Record) -> Result<(), InvariantError> {
    require(
        program
            .definitions
            .get(record.definition.0 as usize)
            .is_some_and(|definition| {
                matches!(
                    definition.kind,
                    DefinitionKind::Record | DefinitionKind::Union
                )
            }),
        "record has an invalid definition ID",
    )?;
    for field in &record.fields {
        require(
            field.ty != TyId::ERROR && (field.ty.0 as usize) < program.types.values().len(),
            "field has an invalid type",
        )?;
        require(
            program.types.valid_region_scope(field.ty),
            "field has an escaping bound region",
        )?;
    }
    Ok(())
}

fn enum_metadata(program: &Program, enumeration: &Enum) -> Result<(), InvariantError> {
    require(
        program
            .definitions
            .get(enumeration.definition.0 as usize)
            .is_some_and(|definition| definition.kind == DefinitionKind::Enum),
        "enum has an invalid definition ID",
    )?;
    require(
        enumeration.discriminants.len() == enumeration.variants.len(),
        "enum discriminant dimensions do not match",
    )?;
    for (index, (&variant, discriminant)) in enumeration
        .variants
        .iter()
        .zip(&enumeration.discriminants)
        .enumerate()
    {
        require(
            program
                .definitions
                .get(variant.0 as usize)
                .is_some_and(|definition| {
                    matches!(definition.kind, DefinitionKind::Variant { parent, index: ordinal }
                if parent == enumeration.definition && ordinal as usize == index)
                }),
            "enum has an invalid variant ID",
        )?;
        require(
            program
                .types
                .constant_terms()
                .get(discriminant.0 as usize)
                .is_some_and(|term| {
                    matches!(
                        program.types.get(term.ty),
                        Ty::Integer {
                            signed: false,
                            bits: 0
                        }
                    )
                }),
            "enum discriminant is not a valid usize term",
        )?;
    }
    Ok(())
}
