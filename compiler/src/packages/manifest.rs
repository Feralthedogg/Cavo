use crate::external::json::{self, Json};
use std::{collections::BTreeMap, path::Path};

#[derive(Clone, Debug)]
pub enum Dependency {
    Path(String),
    Git { url: String, revision: String },
}
#[derive(Clone, Debug)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    pub sources: Vec<String>,
    pub dependencies: BTreeMap<String, Dependency>,
}

pub(crate) fn read(path: &Path) -> Result<(Manifest, String), String> {
    let text = super::resolve::read_bounded(path, 256 * 1024)?;
    Ok((parse(&text)?, text))
}

pub fn parse(text: &str) -> Result<Manifest, String> {
    let mut section = "";
    let mut package = BTreeMap::new();
    let mut dependencies = BTreeMap::new();
    for line in text.lines() {
        let line = without_comment(line).trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            section = &line[1..line.len() - 1];
            if !matches!(section, "package" | "dependencies") {
                return Err(format!("unsupported manifest section [{section}]"));
            }
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .ok_or("manifest entry requires key = value")?;
        let key = key.trim();
        let value = value.trim();
        if !identifier(key) {
            return Err("manifest keys must be identifiers".into());
        }
        match section {
            "package" => {
                if package.insert(key.to_owned(), value.to_owned()).is_some() {
                    return Err("duplicate package member".into());
                }
            }
            "dependencies" => {
                if dependencies
                    .insert(key.to_owned(), dependency(value)?)
                    .is_some()
                {
                    return Err("duplicate dependency alias".into());
                }
            }
            _ => return Err("manifest values require [package] or [dependencies]".into()),
        }
    }
    finish(package, dependencies)
}

fn finish(
    mut values: BTreeMap<String, String>,
    dependencies: BTreeMap<String, Dependency>,
) -> Result<Manifest, String> {
    let name = string(&values.remove("name").ok_or("package requires name")?)?;
    let version = string(&values.remove("version").ok_or("package requires version")?)?;
    if !identifier(&name)
        || version.split('.').count() != 3
        || !version
            .split('.')
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
    {
        return Err(
            "package name must be an identifier and version must be numeric major.minor.patch"
                .into(),
        );
    }
    if let Some(edition) = values.remove("edition")
        && string(&edition)? != "0.1"
    {
        return Err("unsupported Cavo edition".into());
    }
    let sources = if let Some(value) = values.remove("sources") {
        let Json::Array(values) = json::parse_bounded(&value, 262_144, 4096)? else {
            return Err("sources requires an array of relative paths".into());
        };
        values
            .into_iter()
            .map(|value| match value {
                Json::String(s) => Ok(s),
                _ => Err("source path must be a string".into()),
            })
            .collect::<Result<_, String>>()?
    } else {
        Vec::new()
    };
    if !values.is_empty() {
        return Err(
            "unsupported package field (build scripts and registries are not executed)".into(),
        );
    }
    if dependencies.len() > 128 {
        return Err("package dependency limit exceeded".into());
    }
    Ok(Manifest {
        name,
        version,
        sources,
        dependencies,
    })
}

fn dependency(value: &str) -> Result<Dependency, String> {
    let body = value
        .strip_prefix('{')
        .and_then(|v| v.strip_suffix('}'))
        .ok_or("dependencies require { path = ... } or { git = ..., rev = ... }")?;
    let mut fields = BTreeMap::new();
    for field in split_fields(body) {
        let (key, value) = field.split_once('=').ok_or("dependency field requires =")?;
        if fields.insert(key.trim(), string(value.trim())?).is_some() {
            return Err("duplicate dependency member".into());
        }
    }
    let dependency = if let Some(path) = fields.remove("path") {
        Dependency::Path(path)
    } else {
        let url = fields
            .remove("git")
            .ok_or("dependency requires path or git")?;
        let revision = fields
            .remove("rev")
            .ok_or("Git dependency requires an exact revision")?;
        if !url.starts_with("https://")
            || url[8..].contains(['@', '?', '#', '\\'])
            || url.bytes().any(|b| b.is_ascii_whitespace())
            || !matches!(revision.len(), 40 | 64)
            || !revision
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err("Git dependencies require an HTTPS URL without credentials and a full lowercase commit ID".into());
        }
        Dependency::Git { url, revision }
    };
    if !fields.is_empty() {
        return Err("unknown or conflicting dependency source member".into());
    }
    Ok(dependency)
}

fn string(text: &str) -> Result<String, String> {
    match json::parse_bounded(text, 262_144, 4096)? {
        Json::String(value) => Ok(value),
        _ => Err("manifest value must be a quoted string".into()),
    }
}

fn identifier(text: &str) -> bool {
    let mut bytes = text.bytes();
    bytes
        .next()
        .is_some_and(|b| b == b'_' || b.is_ascii_alphabetic())
        && bytes.all(|b| b == b'_' || b.is_ascii_alphanumeric())
}

fn without_comment(text: &str) -> &str {
    let mut quoted = false;
    let mut escaped = false;
    for (index, ch) in text.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' && quoted {
            escaped = true;
            continue;
        }
        if ch == '"' {
            quoted = !quoted;
        }
        if ch == '#' && !quoted {
            return &text[..index];
        }
    }
    text
}

fn split_fields(text: &str) -> Vec<&str> {
    let mut quoted = false;
    let mut escaped = false;
    let mut start = 0;
    let mut fields = Vec::new();
    for (index, ch) in text.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' && quoted {
            escaped = true;
            continue;
        }
        if ch == '"' {
            quoted = !quoted;
        }
        if ch == ',' && !quoted {
            fields.push(text[start..index].trim());
            start = index + 1;
        }
    }
    if !text[start..].trim().is_empty() {
        fields.push(text[start..].trim());
    }
    fields
}
