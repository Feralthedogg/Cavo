use super::{Digest, digest::sha256};
use crate::arena::Access as _;
use crate::{
    hir,
    source::SourceMap,
    symbol::Interner,
    types::{ConstKind, ConstValue, GenericArg, Region, Ty, TyId},
};
use std::collections::{BTreeMap, HashMap, HashSet};
mod copy;
pub use copy::{CopyPermission, permissions as copy_permissions};

#[derive(Debug)]
pub struct InterfaceFunction {
    pub name: String,
    pub abi: String,
    pub signature: Digest,
}

pub fn qualified(program: &hir::Program, symbols: &Interner, definition: hir::DefId) -> String {
    let def = &program.definitions[definition];
    program.modules[def.module]
        .path
        .iter()
        .copied()
        .chain([def.name])
        .map(|s| symbols.get(s))
        .collect::<Vec<_>>()
        .join("::")
}
pub fn abi(def: &hir::Definition) -> &str {
    def.foreign_abi.as_deref().unwrap_or("cavo")
}

struct Encoder<'a> {
    program: &'a hir::Program,
    symbols: &'a Interner,
    sources: &'a SourceMap,
    bytes: Vec<u8>,
    regions: HashMap<Region, u32>,
    nominals: BTreeMap<String, hir::DefId>,
    remaining: usize,
}
impl Encoder<'_> {
    fn new<'a>(
        program: &'a hir::Program,
        symbols: &'a Interner,
        sources: &'a SourceMap,
    ) -> Encoder<'a> {
        Encoder {
            program,
            symbols,
            sources,
            bytes: Vec::new(),
            regions: HashMap::new(),
            nominals: BTreeMap::new(),
            remaining: 4096,
        }
    }
    fn finish(mut self) -> Option<Digest> {
        let mut seen = HashSet::new();
        while let Some((name, definition)) = self.nominals.pop_first() {
            if !seen.insert(definition) {
                continue;
            }
            if seen.len() > 128 {
                return None;
            }
            self.nominal_declaration(&name, definition)?;
        }
        (self.bytes.len() <= 1_048_576).then(|| sha256(&self.bytes))
    }
    fn nominal_declaration(&mut self, name: &str, definition: hir::DefId) -> Option<()> {
        let def = &self.program.definitions[definition];
        self.token(name);
        self.number(u64::from(def.type_parameter_count));
        self.token(match def.kind {
            hir::DefinitionKind::Record => "record",
            hir::DefinitionKind::Union => "union",
            hir::DefinitionKind::Enum => "enum",
            _ => "opaque",
        });
        self.attrs(def)?;
        self.copy_permissions(definition)?;
        if let Some(record) = self
            .program
            .records
            .iter()
            .find(|record| record.definition == definition)
        {
            self.number(record.fields.len() as u64);
            for field in &record.fields {
                self.token(self.symbols.get(field.name));
                self.ty(field.ty, 0)?;
            }
        } else {
            self.number(0);
        }
        if let Some(enumeration) = self
            .program
            .enums
            .iter()
            .find(|item| item.definition == definition)
        {
            self.number(enumeration.variants.len() as u64);
            for (index, &variant) in enumeration.variants.iter().enumerate() {
                self.token(self.symbols.get(self.program.definitions[variant].name));
                self.ty(self.program.definitions[variant].ty, 0)?;
                if self
                    .program
                    .types
                    .const_usize(enumeration.discriminants[index])
                    != Some(index as u64)
                {
                    self.token("explicit-tag");
                    self.constant(enumeration.discriminants[index], 0)?;
                }
            }
        } else {
            self.number(0);
        }
        Some(())
    }

    fn token(&mut self, text: &str) {
        self.bytes
            .extend_from_slice(&(text.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(text.as_bytes());
    }
    fn number(&mut self, n: u64) {
        self.bytes.extend_from_slice(&n.to_le_bytes());
    }
    fn attrs(&mut self, def: &hir::Definition) -> Option<()> {
        self.remaining = self.remaining.checked_sub(def.attributes.len())?;
        self.number(def.attributes.len() as u64);
        for attr in &def.attributes {
            self.remaining = self.remaining.checked_sub(attr.arguments.len())?;
            self.token(self.symbols.get(attr.name));
            self.number(attr.arguments.len() as u64);
            for arg in &attr.arguments {
                if self
                    .bytes
                    .len()
                    .saturating_add(arg.span.end.saturating_sub(arg.span.start) as usize)
                    > 1_048_576
                {
                    return None;
                }
                self.token(self.sources.file(arg.span.file).slice(arg.span));
            }
        }
        for attr in &def.attributes {
            if let Some(value) = attr.constant
                && !matches!(attr.arguments.as_slice(), [token] if token.kind == crate::syntax::token::TokenKind::Integer)
            {
                self.token("resolved-attribute");
                self.constant(value, 0)?;
            }
        }
        self.remaining = self.remaining.checked_sub(def.declaration_clauses.len())?;
        self.number(def.declaration_clauses.len() as u64);
        for &(kind, span) in &def.declaration_clauses {
            self.token(match kind {
                crate::syntax::ast::ClauseKind::Requires => "requires",
                crate::syntax::ast::ClauseKind::Ensures => "ensures",
            });
            if self
                .bytes
                .len()
                .saturating_add(span.end.saturating_sub(span.start) as usize)
                > 1_048_576
            {
                return None;
            }
            self.token(self.sources.file(span.file).slice(span));
        }
        (self.bytes.len() <= 1_048_576).then_some(())
    }
    fn generic(&mut self, argument: GenericArg, depth: usize) -> Option<()> {
        match argument {
            GenericArg::Type(ty) => self.ty(ty, depth),
            GenericArg::Const(value) => {
                self.token("const-argument");
                self.constant(value, depth)
            }
            GenericArg::Lifetime(region) => {
                self.token("lifetime-argument");
                self.region(region)
            }
        }
    }
    fn region(&mut self, region: Region) -> Option<()> {
        match region {
            Region::Static => self.token("static"),
            Region::Named { owner, name } => {
                self.token("declared");
                self.token(&qualified(self.program, self.symbols, owner));
                let position = self
                    .program
                    .definitions
                    .get(owner.0 as usize)?
                    .lifetime_parameters
                    .iter()
                    .position(|&n| n == name)?;
                self.number(position as u64);
            }
            Region::Infer(_) => {
                self.token("elided");
                let next = self.regions.len() as u32;
                let index = *self.regions.entry(region).or_insert(next);
                self.number(index as u64);
            }
            Region::Bound { depth, index } => {
                self.token("bound");
                self.number(depth as u64);
                self.number(index as u64);
            }
        }
        Some(())
    }
    fn constant(&mut self, id: crate::types::ConstId, depth: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(1)?;
        if depth > 128 {
            return None;
        }
        match &self.program.types.const_term(id).kind {
            ConstKind::Value(ConstValue::Usize(value)) => {
                self.token("usize");
                self.number(*value);
            }
            ConstKind::Value(ConstValue::Bool(value)) => {
                self.token("bool");
                self.number(u64::from(*value));
            }
            ConstKind::Parameter { owner, index } => {
                self.token("const-parameter");
                self.token(&qualified(self.program, self.symbols, *owner));
                self.number(*index as u64);
            }
            // Unresolved queries are not a stable external ABI identity.
            _ => return None,
        }
        Some(())
    }
    fn ty(&mut self, ty: TyId, depth: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(1)?;
        if depth > 128 || self.bytes.len() > 1_048_576 {
            return None;
        }
        match self.program.types.get(ty) {
            Ty::Error => return None,
            Ty::Void => self.token("void"),
            Ty::Bool => self.token("bool"),
            Ty::Char => self.token("char"),
            Ty::Str => self.token("str"),
            Ty::Integer { signed, bits } => {
                self.token(if *signed { "signed" } else { "unsigned" });
                self.number(u64::from(*bits));
            }
            Ty::Float { bits } => {
                self.token("float");
                self.number(u64::from(*bits));
            }
            Ty::Parameter { owner, index } => {
                self.token("parameter");
                self.token(&qualified(self.program, self.symbols, *owner));
                self.number(u64::from(*index));
            }
            Ty::Named {
                definition,
                arguments,
            } => {
                self.token("nominal");
                let name = qualified(self.program, self.symbols, *definition);
                self.token(&name);
                self.nominals.insert(name, *definition);
                self.number(arguments.len() as u64);
                for &ty in arguments {
                    self.generic(ty, depth + 1)?;
                }
            }
            Ty::Reference {
                region,
                mutable,
                inner,
            } => {
                self.token(if *mutable { "exclusive" } else { "shared" });
                self.region(*region)?;
                self.ty(*inner, depth + 1)?;
            }
            Ty::Pointer { constant, inner } => {
                self.token(if *constant { "ptr-const" } else { "ptr" });
                self.ty(*inner, depth + 1)?;
            }
            Ty::Array { inner, length } => {
                self.token("array");
                self.number(*length);
                self.ty(*inner, depth + 1)?;
            }
            Ty::SymbolicArray { inner, length } => {
                self.token("symbolic-array");
                self.constant(*length, depth + 1)?;
                self.ty(*inner, depth + 1)?;
            }
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => {
                self.token("dynamic");
                self.token(&qualified(self.program, self.symbols, *trait_definition));
                self.number(arguments.len() as u64);
                for &argument in arguments {
                    self.generic(argument, depth + 1)?;
                }
            }
            Ty::Slice(inner) => {
                self.token("slice");
                self.ty(*inner, depth + 1)?;
            }
            Ty::Function { parameters, result } => {
                self.token("function");
                self.number(parameters.len() as u64);
                for &ty in parameters {
                    self.ty(ty, depth + 1)?;
                }
                self.ty(*result, depth + 1)?;
            }
            Ty::ForAll { parameters, inner } => {
                self.token("forall");
                self.number(u64::from(*parameters));
                self.ty(*inner, depth + 1)?;
            }
        }
        Some(())
    }
}

pub fn fingerprint(
    program: &hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
    definition: hir::DefId,
) -> Option<Digest> {
    let def = program.definitions.get_id(definition)?;
    if def.kind != hir::DefinitionKind::Function {
        return None;
    }
    let mut e = Encoder::new(program, symbols, sources);
    e.token("cavo.interface.v1");
    e.token(&qualified(program, symbols, definition));
    e.token(abi(def));
    e.number(def.lifetime_parameters.len() as u64);
    e.number(u64::from(def.type_parameter_count));
    if def
        .generic_parameter_kinds
        .contains(&crate::types::GenericParamKind::Const)
    {
        e.token("generic-kinds");
        for kind in &def.generic_parameter_kinds {
            e.token(&format!("{kind:?}"));
        }
    }
    e.attrs(def)?;
    e.ty(def.ty, 0)?;
    e.finish()
}

pub fn interfaces(
    program: &hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
) -> Option<Vec<InterfaceFunction>> {
    let bodies: HashSet<_> = program.functions.iter().map(|f| f.definition).collect();
    let mut result = Vec::new();
    let internal = program.internal_definitions();
    for (index, def) in program.definitions.iter().enumerate() {
        let id = hir::DefId(index as u32);
        if def.kind == hir::DefinitionKind::Function
            && !bodies.contains(&id)
            && !internal.contains(&id)
        {
            result.push(InterfaceFunction {
                name: qualified(program, symbols, id),
                abi: abi(def).into(),
                signature: fingerprint(program, symbols, sources, id)?,
            });
        }
    }
    result.sort_by(|a, b| a.name.cmp(&b.name));
    Some(result)
}

pub fn render(functions: &[InterfaceFunction]) -> String {
    render_with_copy(functions, &[])
}

pub fn render_with_copy(functions: &[InterfaceFunction], permissions: &[CopyPermission]) -> String {
    fn quoted(text: &str) -> String {
        use std::fmt::Write;
        let mut result = String::from("\"");
        for ch in text.chars() {
            match ch {
                '"' => result.push_str("\\\""),
                '\\' => result.push_str("\\\\"),
                ch if ch < ' ' => {
                    write!(result, "\\u{:04x}", ch as u32).expect("string write");
                }
                ch => result.push(ch),
            }
        }
        result.push('"');
        result
    }
    let entries = functions
        .iter()
        .map(|f| {
            format!(
                "    {{\"name\": {}, \"abi\": {}, \"signature\": \"{}\"}}",
                quoted(&f.name),
                quoted(&f.abi),
                f.signature
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");
    let permissions = permissions
        .iter()
        .map(|permission| {
            format!(
                "{{\"type\":{},\"explicit_impls\":[{}]}}",
                quoted(&permission.name),
                permission
                    .explicit_impls
                    .iter()
                    .map(|digest| quoted(&digest.to_string()))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\n  \"schema\": 1,\n  \"functions\": [\n{entries}\n  ],\n  \"copy_permissions\": [{permissions}]\n}}\n"
    )
}
