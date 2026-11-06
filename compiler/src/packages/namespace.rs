use super::{Graph, Package, Source};
use crate::{
    Compilation,
    syntax::{
        lexer,
        token::{Keyword, TokenKind as T},
    },
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn sources(graph: &Graph) -> Result<Vec<Source>, String> {
    let mut output = Vec::new();
    let mut namespaces = BTreeMap::new();
    for package in &graph.packages {
        if namespaces
            .insert(&package.namespace, &package.id)
            .is_some_and(|previous| previous != &package.id)
        {
            return Err("distinct package identities have the same namespace".into());
        }
        let mut compilation = Compilation::default();
        for source in &package.sources {
            let id = compilation
                .sources
                .add(&source.name, source.text.clone())
                .map_err(str::to_owned)?;
            compilation.parse(id);
        }
        if !compilation.diagnostics.is_empty() {
            return Err("package source has parse errors before namespace resolution".into());
        }
        let roots: BTreeSet<_> = compilation
            .ast
            .modules
            .iter()
            .filter_map(|m| m.name.first())
            .map(|name| compilation.symbols.get(name.symbol).to_owned())
            .collect();
        let aliases: BTreeMap<_, _> = package
            .dependencies
            .iter()
            .map(|(alias, index)| (alias.clone(), graph.packages[*index].namespace.clone()))
            .collect();
        if roots.iter().any(|root| aliases.contains_key(root)) {
            return Err("a package module root conflicts with a dependency alias".into());
        }
        for source in &package.sources {
            let text = rewrite(source, package, &roots, &aliases)?;
            output.push(Source {
                name: format!("{}/{}", package.namespace, source.name),
                text,
            });
        }
    }
    output.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(output)
}

fn rewrite(
    source: &Source,
    package: &Package,
    roots: &BTreeSet<String>,
    aliases: &BTreeMap<String, String>,
) -> Result<String, String> {
    let mut compilation = Compilation::default();
    let id = compilation
        .sources
        .add(&source.name, source.text.clone())
        .map_err(str::to_owned)?;
    let tokens = lexer::lex(
        compilation.sources.file(id),
        &mut compilation.symbols,
        &mut compilation.diagnostics,
    );
    let mut edits = BTreeMap::new();
    let mut declaration = None;
    let mut has_module = false;
    for (index, token) in tokens.iter().enumerate() {
        if matches!(token.kind, T::Keyword(Keyword::Module | Keyword::Import)) {
            declaration = Some(token.kind);
            continue;
        }
        let T::Ident(symbol) = token.kind else {
            if token.kind == T::Semicolon {
                declaration = None;
            }
            continue;
        };
        let name = compilation.symbols.get(symbol);
        if name.starts_with("__cavo_pkg_") {
            return Err("__cavo_pkg_ is a reserved package namespace".into());
        }
        let first = index == 0 || tokens[index - 1].kind != T::ColonColon;
        if !first {
            continue;
        }
        if declaration == Some(T::Keyword(Keyword::Module)) {
            has_module = true;
        }
        let path = tokens
            .get(index + 1)
            .is_some_and(|token| token.kind == T::ColonColon);
        let replacement = replacement(name, declaration, path, package, roots, aliases);
        if let Some(replacement) = replacement {
            edits.insert((token.span.start, token.span.end), replacement);
        }
        declaration = None;
    }
    let mut text = source.text.clone();
    for ((start, end), replacement) in edits.into_iter().rev() {
        text.replace_range(start as usize..end as usize, &replacement);
    }
    if !has_module {
        text.insert_str(0, &format!("module {};\n", package.namespace));
    }
    Ok(text)
}

fn replacement(
    name: &str,
    declaration: Option<T>,
    path: bool,
    package: &Package,
    roots: &BTreeSet<String>,
    aliases: &BTreeMap<String, String>,
) -> Option<String> {
    if declaration == Some(T::Keyword(Keyword::Module)) {
        return Some(format!("{}::{name}", package.namespace));
    }
    if declaration == Some(T::Keyword(Keyword::Import)) {
        return Some(
            aliases
                .get(name)
                .cloned()
                .unwrap_or_else(|| format!("{}::{name}", package.namespace)),
        );
    }
    if path {
        aliases.get(name).cloned().or_else(|| {
            roots
                .contains(name)
                .then(|| format!("{}::{name}", package.namespace))
        })
    } else {
        None
    }
}
