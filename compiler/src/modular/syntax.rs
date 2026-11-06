use super::*;
use crate::{
    diagnostic::{Diagnostic, report},
    source::SourceMap,
    symbol::{Interner, Symbol},
    syntax::{
        ast::Visibility,
        token::{Token, TokenKind as T},
    },
    types::{Ty, TyId},
};

pub(crate) fn collect(
    program: &mut hir::Program,
    names: &BTreeMap<hir::DefId, Vec<Symbol>>,
    symbols: &Interner,
    sources: &SourceMap,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for index in 0..program.definitions.len() {
        let id = hir::DefId(index as u32);
        let item = program.definitions[index].clone();
        if item.kind != hir::DefinitionKind::Function
            || program.contracts.intrinsics.contains_key(&id)
        {
            continue;
        }
        let declared = item
            .attributes
            .iter()
            .any(|a| is_contract_attribute(symbols.get(a.name)));
        if item.visibility != Visibility::Public && !declared {
            continue;
        }
        match parse(
            program,
            id,
            names.get(&id).map(Vec::as_slice).unwrap_or(&[]),
            symbols,
            sources,
        ) {
            Ok(contract) => {
                program.modular.functions.insert(id, contract);
            }
            Err(message) => report(
                diagnostics,
                Diagnostic::error("E-EFFECT-DECL", message, item.span),
            ),
        }
    }
    let methods: Vec<_> = program
        .implementations
        .iter()
        .flat_map(|i| &i.methods)
        .filter_map(|m| m.declaration.map(|d| (m.implementation, d)))
        .collect();
    for (implementation, declaration) in methods {
        if let Some(contract) = program.modular.functions.get(&declaration).cloned() {
            if let Some(own) = program.modular.functions.get(&implementation) {
                if !own.explicit {
                    program.modular.functions.insert(implementation, contract);
                } else if !refines(own, &contract) {
                    report(
                        diagnostics,
                        Diagnostic::error(
                            "E-EFFECT-REFINE",
                            "implementation effect bound exceeds the trait declaration",
                            own.span,
                        ),
                    );
                }
            } else {
                program.modular.functions.insert(implementation, contract);
            }
        }
    }
}

fn refines(own: &Contract, inherited: &Contract) -> bool {
    own.upper.is_subset(&inherited.upper)
        && (!inherited.bounded || own.bounded)
        && (!inherited.pure || own.pure)
        && (!inherited.no_callback || own.no_callback)
        && (!inherited.no_retain || own.no_retain)
        && (!inherited.no_free || own.no_free)
        && (!own.affinity || inherited.affinity)
        && frame_subset(&own.reads, &inherited.reads)
        && frame_subset(&own.writes, &inherited.writes)
        && frame_subset(&own.returns, &inherited.returns)
        && stores_refine(&own.normal, &inherited.normal)
        && stores_refine(&own.panic, &inherited.panic)
        && stores_refine(&own.cancel, &inherited.cancel)
}

fn frame_subset(own: &Option<Vec<String>>, inherited: &Option<Vec<String>>) -> bool {
    inherited.as_ref().is_none_or(|allowed| {
        own.as_ref().is_some_and(|paths| {
            paths.iter().all(|path| {
                allowed.iter().any(|root| {
                    path == root
                        || path
                            .strip_prefix(root)
                            .is_some_and(|tail| tail.starts_with('.'))
                })
            })
        })
    })
}

fn stores_refine(own: &[ReferenceStore], inherited: &[ReferenceStore]) -> bool {
    inherited.iter().all(|promise| {
        own.iter().any(|value| {
            value.target == promise.target
                && (!promise.definite || value.definite)
                && value
                    .sources
                    .iter()
                    .all(|source| promise.sources.contains(source))
        })
    })
}

fn is_contract_attribute(name: &str) -> bool {
    matches!(
        name,
        "effects"
            | "nosuspend"
            | "nocancel"
            | "nopanic"
            | "noalloc"
            | "nopreempt"
            | "pure"
            | "thread_bound"
    )
}

fn parse(
    program: &mut hir::Program,
    definition: hir::DefId,
    names: &[Symbol],
    symbols: &Interner,
    sources: &SourceMap,
) -> Result<Contract, String> {
    let item = program.definitions[definition].clone();
    let mut contract = Contract::conservative(item.span);
    for attribute in &item.attributes {
        let name = symbols.get(attribute.name);
        if name == "effects" {
            contract.explicit = true;
            let parts = chunks(&attribute.arguments)?;
            let positive = parts.iter().any(|part| {
                part.first().is_some_and(|token|
                matches!(token.kind, T::Ident(name) if effect(symbols.get(name)).is_some()))
            });
            if positive || parts.is_empty() {
                contract.upper.clear();
            }
            for part in parts {
                clause(
                    program,
                    definition,
                    names,
                    &mut contract,
                    part,
                    symbols,
                    sources,
                )?;
            }
        } else if is_contract_attribute(name) {
            contract.explicit = true;
            qualifier(&mut contract, name)?;
        }
    }
    Ok(contract)
}

fn chunks(tokens: &[Token]) -> Result<Vec<&[Token]>, String> {
    let mut depth = 0usize;
    let mut start = 0;
    let mut output = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        match token.kind {
            T::LeftParen | T::LeftBracket => {
                depth += 1;
                if depth > 32 {
                    return Err("effect contract nesting limit exceeded".into());
                }
            }
            T::RightParen | T::RightBracket => {
                depth = depth.checked_sub(1).ok_or("unbalanced effect contract")?
            }
            T::Comma | T::Pipe if depth == 0 => {
                if start != index {
                    output.push(&tokens[start..index]);
                }
                start = index + 1;
            }
            _ => {}
        }
    }
    if depth != 0 {
        return Err("unbalanced effect contract".into());
    }
    if start < tokens.len() {
        output.push(&tokens[start..]);
    }
    Ok(output)
}

fn clause(
    program: &mut hir::Program,
    definition: hir::DefId,
    names: &[Symbol],
    contract: &mut Contract,
    tokens: &[Token],
    symbols: &Interner,
    sources: &SourceMap,
) -> Result<(), String> {
    let Some(Token {
        kind: T::Ident(name),
        ..
    }) = tokens.first()
    else {
        return Err("effect contract requires a named clause".into());
    };
    let name = symbols.get(*name);
    if tokens.len() == 1 {
        if let Some(effect) = effect(name) {
            contract.upper.insert(effect);
            return Ok(());
        }
        return qualifier(contract, name);
    }
    if tokens.get(1).is_none_or(|t| t.kind != T::LeftParen)
        || tokens.last().is_none_or(|t| t.kind != T::RightParen)
    {
        return Err("effect arguments require parentheses".into());
    }
    let parts = chunks(&tokens[2..tokens.len() - 1])?;
    match name {
        "reads" | "writes" | "returns" => {
            let values = parts
                .into_iter()
                .map(|part| path(program, definition, names, part, symbols, sources))
                .collect::<Result<_, _>>()?;
            match name {
                "reads" => contract.reads = Some(values),
                "writes" => contract.writes = Some(values),
                _ => contract.returns = Some(values),
            }
        }
        "normal" | "panic" | "cancel" | "maybe_normal" => {
            let values = parts
                .into_iter()
                .map(|part| {
                    store(
                        program,
                        definition,
                        names,
                        part,
                        symbols,
                        sources,
                        name != "maybe_normal",
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            match name {
                "panic" => contract.panic.extend(values),
                "cancel" => contract.cancel.extend(values),
                _ => contract.normal.extend(values),
            }
        }
        _ => return Err(format!("unknown effect contract clause `{name}`")),
    }
    Ok(())
}

fn qualifier(contract: &mut Contract, name: &str) -> Result<(), String> {
    let forbidden: &[Effect] = match name {
        "nosuspend" => &[Effect::Park],
        "nocancel" => &[Effect::Cancel],
        "nopanic" => &[Effect::Panic],
        "noalloc" => &[Effect::Allocate],
        "nopreempt" => &[
            Effect::Poll,
            Effect::AsyncPreempt,
            Effect::Park,
            Effect::Cancel,
        ],
        "pure" => {
            contract.pure = true;
            contract.no_callback = true;
            contract.no_retain = true;
            contract.no_free = true;
            contract.writes = Some(Vec::new());
            &[
                Effect::MemoryWrite,
                Effect::MemoryFree,
                Effect::Allocate,
                Effect::Ffi,
                Effect::Thread,
                Effect::Block,
                Effect::Park,
                Effect::Cancel,
                Effect::Panic,
                Effect::Poll,
            ]
        }
        "no_free" => {
            contract.no_free = true;
            &[Effect::MemoryFree]
        }
        "no_retain" => {
            contract.no_retain = true;
            &[]
        }
        "no_callback" => {
            contract.no_callback = true;
            &[]
        }
        "bounded" => {
            contract.bounded = true;
            &[]
        }
        "thread_bound" => {
            contract.affinity = true;
            &[]
        }
        _ => return Err(format!("unknown effect contract qualifier `{name}`")),
    };
    for effect in forbidden {
        contract.upper.remove(effect);
    }
    Ok(())
}

pub(crate) fn effect(name: &str) -> Option<Effect> {
    Some(match name {
        "poll" => Effect::Poll,
        "async_preempt" => Effect::AsyncPreempt,
        "park" => Effect::Park,
        "cancel" => Effect::Cancel,
        "panic" => Effect::Panic,
        "alloc" => Effect::Allocate,
        "ffi" => Effect::Ffi,
        "block" => Effect::Block,
        "thread" => Effect::Thread,
        "write_memory" => Effect::MemoryWrite,
        "free_memory" => Effect::MemoryFree,
        _ => return None,
    })
}

fn store(
    program: &mut hir::Program,
    definition: hir::DefId,
    names: &[Symbol],
    tokens: &[Token],
    symbols: &Interner,
    sources: &SourceMap,
    definite: bool,
) -> Result<ReferenceStore, String> {
    let equals = tokens
        .iter()
        .position(|t| t.kind == T::Equal)
        .ok_or("a post-state store requires `target = source` (entry-relative)")?;
    let target = path(
        program,
        definition,
        names,
        &tokens[..equals],
        symbols,
        sources,
    )?;
    let sources = tokens[equals + 1..]
        .split(|t| t.kind == T::Pipe)
        .map(|part| path(program, definition, names, part, symbols, sources))
        .collect::<Result<_, _>>()?;
    Ok(ReferenceStore {
        target,
        sources,
        definite,
    })
}

fn path(
    program: &mut hir::Program,
    definition: hir::DefId,
    names: &[Symbol],
    tokens: &[Token],
    symbols: &Interner,
    sources: &SourceMap,
) -> Result<String, String> {
    let Some(first) = tokens.first() else {
        return Err("empty effect path".into());
    };
    let root = match first.kind {
        T::Ident(name) if symbols.get(name) == "static" => return Ok("static".into()),
        T::Ident(name) => names
            .iter()
            .position(|candidate| *candidate == name)
            .ok_or("effect path names no parameter")? as u32,
        T::Integer => sources
            .file(first.span.file)
            .slice(first.span)
            .parse()
            .map_err(|_| "effect parameter index must be a decimal u32")?,
        _ => return Err("effect paths start with a parameter name or index".into()),
    };
    let Ty::Function { parameters, .. } = program.types.get(program.definitions[definition].ty)
    else {
        return Err("effect declaration is not callable".into());
    };
    let mut ty = *parameters
        .get(root as usize)
        .ok_or("effect parameter index is out of range")?;
    let mut output = root.to_string();
    let mut rest = &tokens[1..];
    while !rest.is_empty() {
        if rest[0].kind == T::Dot {
            rest = &rest[1..];
        }
        let Some(token) = rest.first() else {
            return Err("incomplete effect path".into());
        };
        if token.kind == T::Star {
            ty = match program.types.get(ty) {
                Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                _ => return Err("effect dereference requires a pointer or reference".into()),
            };
            output.push_str(".*");
        } else {
            let (index, inner) = field(program, ty, token, symbols, sources)?;
            output.push_str(&format!(".{index}"));
            ty = inner;
        }
        rest = &rest[1..];
    }
    Ok(output)
}

fn field(
    program: &mut hir::Program,
    ty: TyId,
    token: &Token,
    symbols: &Interner,
    sources: &SourceMap,
) -> Result<(usize, TyId), String> {
    let Ty::Named {
        definition,
        arguments,
    } = program.types.get(ty).clone()
    else {
        return Err("effect field requires a known record value".into());
    };
    let record = program
        .records
        .iter()
        .find(|record| record.definition == definition)
        .ok_or("effect field is not a record")?;
    let index = match token.kind {
        T::Integer => sources
            .file(token.span.file)
            .slice(token.span)
            .parse()
            .map_err(|_| "invalid effect field index")?,
        T::Ident(name) => record
            .fields
            .iter()
            .position(|field| field.name == name)
            .ok_or_else(|| format!("unknown effect field `{}`", symbols.get(name)))?,
        _ => return Err("effect fields require a name or decimal index".into()),
    };
    let ty = record
        .fields
        .get(index)
        .ok_or("effect field index is out of range")?
        .ty;
    Ok((index, program.types.substitute(ty, definition, &arguments)))
}
