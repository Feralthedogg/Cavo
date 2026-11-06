use crate::{
    hir::{DefId, Definition},
    symbol::{Interner, Symbol},
};
use std::collections::HashMap;
mod consts;
mod region_map;
mod regions;
pub use consts::{ConstError, ConstId, ConstKind, ConstTerm, ConstValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TyId(pub u32);
impl TyId {
    pub const ERROR: Self = Self(0);
    pub const VOID: Self = Self(1);
    pub const BOOL: Self = Self(2);
    pub const CHAR: Self = Self(3);
    pub const STR: Self = Self(4);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Region {
    Static,
    Named { owner: DefId, name: Symbol },
    Infer(u32),
    Bound { depth: u16, index: u16 },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GenericParamKind {
    Type,
    Const,
    Lifetime,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Type(TyId),
    Const(ConstId),
    Lifetime(Region),
}
impl GenericArg {
    pub fn ty(self) -> Option<TyId> {
        match self {
            Self::Type(ty) => Some(ty),
            Self::Const(_) | Self::Lifetime(_) => None,
        }
    }
    pub fn kind(self) -> GenericParamKind {
        match self {
            Self::Type(_) => GenericParamKind::Type,
            Self::Const(_) => GenericParamKind::Const,
            Self::Lifetime(_) => GenericParamKind::Lifetime,
        }
    }
    pub fn region(self) -> Option<Region> {
        match self {
            Self::Lifetime(region) => Some(region),
            _ => None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Error,
    Void,
    Bool,
    Char,
    Str,
    Integer {
        signed: bool,
        bits: u16,
    }, // zero means pointer-sized (all current targets: 64 bits)
    Float {
        bits: u16,
    },
    Parameter {
        owner: DefId,
        index: u32,
    },
    Named {
        definition: DefId,
        arguments: Vec<GenericArg>,
    },
    Dynamic {
        trait_definition: DefId,
        arguments: Vec<GenericArg>,
    },
    Reference {
        region: Region,
        mutable: bool,
        inner: TyId,
    },
    Pointer {
        constant: bool,
        inner: TyId,
    },
    Array {
        inner: TyId,
        length: u64,
    },
    SymbolicArray {
        inner: TyId,
        length: ConstId,
    },
    Slice(TyId),
    Function {
        parameters: Vec<TyId>,
        result: TyId,
    },
    ForAll {
        parameters: u16,
        inner: TyId,
    },
}

#[derive(Clone, Debug)]
pub struct TypeContext {
    values: Vec<Ty>,
    indices: HashMap<Ty, TyId>,
    depths: Vec<u16>,
    bound_regions: Vec<bool>,
    next_region: u32,
    constants: consts::Constants,
    generic_parameters: HashMap<DefId, Vec<(Symbol, GenericParamKind)>>,
}
impl Default for TypeContext {
    fn default() -> Self {
        Self::new()
    }
}
impl TypeContext {
    pub fn new() -> Self {
        let mut context = Self {
            values: Vec::new(),
            indices: HashMap::new(),
            depths: Vec::new(),
            bound_regions: Vec::new(),
            next_region: 0,
            constants: consts::Constants::default(),
            generic_parameters: HashMap::new(),
        };
        for ty in [Ty::Error, Ty::Void, Ty::Bool, Ty::Char, Ty::Str] {
            context.intern(ty);
        }
        context
    }
    pub fn intern(&mut self, ty: Ty) -> TyId {
        if let Some(&id) = self.indices.get(&ty) {
            return id;
        }
        let id = TyId(self.values.len().try_into().expect("type table exhausted"));
        self.depths.push(self.depth(&ty));
        self.bound_regions.push(self.contains_bound(&ty));
        self.values.push(ty.clone());
        self.indices.insert(ty, id);
        id
    }
    fn contains_bound(&self, ty: &Ty) -> bool {
        let child = |id: TyId| {
            self.bound_regions
                .get(id.0 as usize)
                .copied()
                .unwrap_or(false)
        };
        match ty {
            Ty::Reference {
                region: Region::Bound { .. },
                ..
            } => true,
            Ty::Reference { inner, .. }
            | Ty::Pointer { inner, .. }
            | Ty::Array { inner, .. }
            | Ty::Slice(inner)
            | Ty::ForAll { inner, .. } => child(*inner),
            Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                arguments.iter().any(|&arg| self.argument_has_bound(arg))
            }
            Ty::Function { parameters, result } => {
                child(*result) || parameters.iter().copied().any(child)
            }
            Ty::SymbolicArray { inner, length } => {
                child(*inner) || self.argument_has_bound(GenericArg::Const(*length))
            }
            _ => false,
        }
    }
    fn depth(&self, ty: &Ty) -> u16 {
        let child = |id: TyId| self.depths.get(id.0 as usize).copied().unwrap_or(0);
        let depth = match ty {
            Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => arguments
                .iter()
                .map(|&arg| self.argument_depth(arg))
                .max()
                .unwrap_or(0),
            Ty::Reference { inner, .. }
            | Ty::Pointer { inner, .. }
            | Ty::Array { inner, .. }
            | Ty::Slice(inner)
            | Ty::ForAll { inner, .. } => child(*inner),
            Ty::SymbolicArray { inner, length } => {
                child(*inner).max(self.argument_depth(GenericArg::Const(*length)))
            }
            Ty::Function { parameters, result } => parameters
                .iter()
                .copied()
                .map(child)
                .max()
                .unwrap_or(0)
                .max(child(*result)),
            _ => 0,
        };
        depth.saturating_add(1)
    }
    pub(crate) fn nesting(&self, ty: TyId) -> u16 {
        self.depths[ty.0 as usize]
    }
    pub(crate) fn instantiate_alias(
        &mut self,
        ty: TyId,
        owner: DefId,
        arguments: &[GenericArg],
    ) -> Result<TyId, ConstError> {
        let mut instantiation = AliasInstantiation {
            types: self,
            owner,
            arguments,
            memo: HashMap::new(),
            regions: HashMap::new(),
            remaining: 4096,
            error: None,
            binders: 0,
        };
        instantiation
            .visit(ty)
            .ok_or_else(|| instantiation.error.unwrap_or(ConstError::Limit))
    }
    pub fn get(&self, id: TyId) -> &Ty {
        &self.values[id.0 as usize]
    }
    pub fn values(&self) -> &[Ty] {
        &self.values
    }
    pub fn fresh_region(&mut self) -> Region {
        let region = Region::Infer(self.next_region);
        self.next_region += 1;
        region
    }

    /// Freshen the signature before substituting type arguments: regions inside
    /// the caller's actual generic types must not be rebound to the callee.
    pub(crate) fn instantiate_function_regions(&mut self, ty: TyId, owner: DefId) -> Option<TyId> {
        let mut replacements = HashMap::new();
        for region in self.regions_in(ty)? {
            let replace = match region {
                Region::Infer(_) => true,
                Region::Named { owner: found, name } if found == owner => !self
                    .generic_parameters(owner)
                    .iter()
                    .any(|&(symbol, kind)| symbol == name && kind == GenericParamKind::Lifetime),
                _ => false,
            };
            if replace {
                replacements.insert(region, self.fresh_region());
            }
        }
        self.map_regions(ty, &mut |region, _| {
            replacements.get(&region).copied().unwrap_or(region)
        })
    }
    pub fn builtin(&mut self, name: &str) -> Option<TyId> {
        Some(match name {
            "void" => TyId::VOID,
            "bool" => TyId::BOOL,
            "char" => TyId::CHAR,
            "str" => TyId::STR,
            "byte" => self.intern(Ty::Integer {
                signed: false,
                bits: 8,
            }),
            "usize" => self.intern(Ty::Integer {
                signed: false,
                bits: 0,
            }),
            "isize" => self.intern(Ty::Integer {
                signed: true,
                bits: 0,
            }),
            "f32" => self.intern(Ty::Float { bits: 32 }),
            "f64" => self.intern(Ty::Float { bits: 64 }),
            name if name.starts_with(['i', 'u']) => {
                let bits: u16 = name[1..].parse().ok()?;
                if !matches!(bits, 8 | 16 | 32 | 64 | 128) {
                    return None;
                }
                self.intern(Ty::Integer {
                    signed: name.starts_with('i'),
                    bits,
                })
            }
            _ => return None,
        })
    }
    pub fn numeric(&self, ty: TyId) -> bool {
        matches!(self.get(ty), Ty::Integer { .. } | Ty::Float { .. })
    }
    pub fn integer(&self, ty: TyId) -> bool {
        matches!(self.get(ty), Ty::Integer { .. })
    }
    pub fn compatible(&self, actual: TyId, expected: TyId) -> bool {
        if actual == expected || actual == TyId::ERROR || expected == TyId::ERROR {
            return true;
        }
        match (self.get(actual), self.get(expected)) {
            (Ty::Function { .. } | Ty::ForAll { .. }, Ty::Function { .. } | Ty::ForAll { .. }) => {
                self.callable_compatible(actual, expected)
            }
            (
                Ty::Reference {
                    mutable: a,
                    inner: x,
                    ..
                },
                Ty::Reference {
                    mutable: b,
                    inner: y,
                    ..
                },
            ) => a == b && self.compatible(*x, *y),
            (
                Ty::Pointer {
                    constant: a,
                    inner: x,
                },
                Ty::Pointer {
                    constant: b,
                    inner: y,
                },
            ) => a == b && self.compatible(*x, *y),
            (
                Ty::Array {
                    inner: x,
                    length: a,
                },
                Ty::Array {
                    inner: y,
                    length: b,
                },
            ) => a == b && self.compatible(*x, *y),
            (Ty::Slice(x), Ty::Slice(y)) => self.compatible(*x, *y),
            (
                Ty::SymbolicArray {
                    inner: x,
                    length: a,
                },
                Ty::SymbolicArray {
                    inner: y,
                    length: b,
                },
            ) => a == b && self.compatible(*x, *y),
            (
                Ty::Dynamic {
                    trait_definition: a,
                    arguments: x,
                },
                Ty::Dynamic {
                    trait_definition: b,
                    arguments: y,
                },
            ) => {
                a == b
                    && x.len() == y.len()
                    && x.iter()
                        .zip(y)
                        .all(|(&x, &y)| self.generic_compatible(x, y))
            }
            (
                Ty::Named {
                    definition: a,
                    arguments: x,
                },
                Ty::Named {
                    definition: b,
                    arguments: y,
                },
            ) => {
                a == b
                    && x.len() == y.len()
                    && x.iter()
                        .zip(y)
                        .all(|(&x, &y)| self.generic_compatible(x, y))
            }
            _ => false,
        }
    }
    pub fn generic_compatible(&self, actual: GenericArg, expected: GenericArg) -> bool {
        match (actual, expected) {
            (GenericArg::Type(a), GenericArg::Type(b)) => self.compatible(a, b),
            (GenericArg::Const(a), GenericArg::Const(b)) => a == b,
            (GenericArg::Lifetime(a), GenericArg::Lifetime(b)) => {
                a == b || matches!(a, Region::Infer(_)) || matches!(b, Region::Infer(_))
            }
            _ => false,
        }
    }
    pub fn substitute(&mut self, ty: TyId, owner: DefId, arguments: &[GenericArg]) -> TyId {
        self.substitute_generics(ty, owner, arguments)
            .unwrap_or(TyId::ERROR)
    }
    /// Region equality in mutable storage. Fresh call variables may be inferred;
    /// a declared lifetime cannot be weakened by covariance here.
    pub(crate) fn region_invariant(&self, actual: TyId, expected: TyId) -> bool {
        let mut pending = vec![(actual, expected)];
        let mut variables = HashMap::new();
        let mut remaining = 4096usize;
        while let Some((actual, expected)) = pending.pop() {
            if remaining == 0 {
                return false;
            }
            remaining -= 1;
            match (self.get(actual), self.get(expected)) {
                (
                    Ty::Reference {
                        region: a,
                        mutable: am,
                        inner: ai,
                    },
                    Ty::Reference {
                        region: b,
                        mutable: bm,
                        inner: bi,
                    },
                ) => {
                    if am != bm {
                        return false;
                    }
                    if matches!(b, Region::Infer(_)) {
                        // A call variable may match the caller's free region,
                        // but may not capture an inner universal placeholder.
                        if matches!(a, Region::Bound { .. }) {
                            return false;
                        }
                        if let Some(bound) = variables.get(b) {
                            if bound != a {
                                return false;
                            }
                        } else {
                            variables.insert(*b, *a);
                        }
                    } else if a != b {
                        return false;
                    }
                    pending.push((*ai, *bi));
                }
                (
                    Ty::Pointer {
                        constant: a,
                        inner: ai,
                    },
                    Ty::Pointer {
                        constant: b,
                        inner: bi,
                    },
                ) => {
                    if a != b {
                        return false;
                    }
                    pending.push((*ai, *bi));
                }
                (
                    Ty::Array {
                        inner: ai,
                        length: a,
                    },
                    Ty::Array {
                        inner: bi,
                        length: b,
                    },
                ) => {
                    if a != b {
                        return false;
                    }
                    pending.push((*ai, *bi));
                }
                (Ty::Array { inner: ai, .. } | Ty::Slice(ai), Ty::Slice(bi)) => {
                    pending.push((*ai, *bi))
                }
                (
                    Ty::Named {
                        definition: a,
                        arguments: aa,
                    },
                    Ty::Named {
                        definition: b,
                        arguments: ba,
                    },
                )
                | (
                    Ty::Dynamic {
                        trait_definition: a,
                        arguments: aa,
                    },
                    Ty::Dynamic {
                        trait_definition: b,
                        arguments: ba,
                    },
                ) => {
                    if a != b || aa.len() != ba.len() {
                        return false;
                    }
                    for (&a, &b) in aa.iter().zip(ba) {
                        match (a, b) {
                            (GenericArg::Type(a), GenericArg::Type(b)) => pending.push((a, b)),
                            (GenericArg::Lifetime(a), GenericArg::Lifetime(b))
                                if invariant_region(a, b, &mut variables) => {}
                            _ if a == b => {}
                            _ => return false,
                        }
                    }
                }
                (
                    Ty::SymbolicArray {
                        inner: ai,
                        length: a,
                    },
                    Ty::SymbolicArray {
                        inner: bi,
                        length: b,
                    },
                ) => {
                    if a != b {
                        return false;
                    }
                    pending.push((*ai, *bi));
                }
                (
                    Ty::Function {
                        parameters: a,
                        result: ar,
                    },
                    Ty::Function {
                        parameters: b,
                        result: br,
                    },
                ) => {
                    if a.len() != b.len() {
                        return false;
                    }
                    pending.push((*ar, *br));
                    pending.extend(a.iter().copied().zip(b.iter().copied()));
                }
                (
                    Ty::ForAll {
                        parameters: a,
                        inner: ai,
                    },
                    Ty::ForAll {
                        parameters: b,
                        inner: bi,
                    },
                ) => {
                    if a != b {
                        return false;
                    }
                    pending.push((*ai, *bi));
                }
                _ => {
                    if actual != expected {
                        return false;
                    }
                }
            }
        }
        true
    }
    pub fn display(&self, ty: TyId, symbols: &Interner, definitions: &[Definition]) -> String {
        match self.get(ty) {
            Ty::Error => "<error>".into(),
            Ty::Void => "void".into(),
            Ty::Bool => "bool".into(),
            Ty::Char => "char".into(),
            Ty::Str => "str".into(),
            Ty::Integer { signed, bits } => format!(
                "{}{}",
                if *signed { "i" } else { "u" },
                if *bits == 0 {
                    "size".into()
                } else {
                    bits.to_string()
                }
            ),
            Ty::Float { bits } => format!("f{bits}"),
            Ty::Parameter { index, .. } => format!("T{index}"),
            Ty::Named {
                definition,
                arguments,
            } => {
                let name = symbols.get(definitions[definition.0 as usize].name);
                if arguments.is_empty() {
                    name.to_owned()
                } else {
                    format!(
                        "{name}<{}>",
                        arguments
                            .iter()
                            .map(|&arg| self.display_argument(arg, symbols, definitions))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Ty::Reference {
                mutable,
                inner,
                region,
            } => format!(
                "&{}{}{}",
                match region {
                    Region::Static => "'static ".into(),
                    Region::Named { name, .. } => format!("'{} ", symbols.get(*name)),
                    Region::Bound { depth: 0, index } => format!("'r{index} "),
                    Region::Bound { depth, index } => format!("'outer{depth}_r{index} "),
                    Region::Infer(_) => String::new(),
                },
                if *mutable { "mut " } else { "" },
                self.display(*inner, symbols, definitions)
            ),
            Ty::Pointer { constant, inner } => format!(
                "ptr<{}{}>",
                if *constant { "const " } else { "" },
                self.display(*inner, symbols, definitions)
            ),
            Ty::Slice(inner) => format!("[{}]", self.display(*inner, symbols, definitions)),
            Ty::Array { inner, length } => {
                format!("{}[{length}]", self.display(*inner, symbols, definitions))
            }
            Ty::SymbolicArray { inner, length } => format!(
                "{}[{}]",
                self.display(*inner, symbols, definitions),
                self.display_const(*length)
            ),
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => {
                let name = symbols.get(definitions[trait_definition.0 as usize].name);
                if arguments.is_empty() {
                    format!("dyn {name}")
                } else {
                    format!(
                        "dyn {name}<{}>",
                        arguments
                            .iter()
                            .map(|&arg| self.display_argument(arg, symbols, definitions))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Ty::Function { parameters, result } => format!(
                "fn({}) -> {}",
                parameters
                    .iter()
                    .map(|&ty| self.display(ty, symbols, definitions))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.display(*result, symbols, definitions)
            ),
            Ty::ForAll { parameters, inner } => format!(
                "for<{}> {}",
                (0..*parameters)
                    .map(|i| format!("'r{i}"))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.display(*inner, symbols, definitions)
            ),
        }
    }
    pub fn display_argument(
        &self,
        argument: GenericArg,
        symbols: &Interner,
        definitions: &[Definition],
    ) -> String {
        match argument {
            GenericArg::Type(ty) => self.display(ty, symbols, definitions),
            GenericArg::Const(id) => self.display_const(id),
            GenericArg::Lifetime(region) => match region {
                Region::Static => "'static".into(),
                Region::Named { name, .. } => format!("'{}", symbols.get(name)),
                Region::Infer(_) => "'_".into(),
                Region::Bound { depth, index } => format!("'r{depth}_{index}"),
            },
        }
    }
}

fn invariant_region(
    actual: Region,
    expected: Region,
    variables: &mut HashMap<Region, Region>,
) -> bool {
    if !matches!(expected, Region::Infer(_)) {
        return actual == expected;
    }
    if matches!(actual, Region::Bound { .. }) {
        return false;
    }
    match variables.get(&expected) {
        Some(&bound) => bound == actual,
        None => {
            variables.insert(expected, actual);
            true
        }
    }
}

// Alias targets are cached templates. Each use substitutes once per DAG node
// and gets fresh inferred regions without changing regions in actual arguments.
struct AliasInstantiation<'a> {
    types: &'a mut TypeContext,
    owner: DefId,
    arguments: &'a [GenericArg],
    memo: HashMap<(TyId, u16), TyId>,
    regions: HashMap<u32, Region>,
    remaining: usize,
    error: Option<ConstError>,
    binders: u16,
}

impl AliasInstantiation<'_> {
    fn constant(&mut self, id: ConstId) -> Option<ConstId> {
        match self
            .types
            .const_substitute_binders(id, self.owner, self.arguments, self.binders)
        {
            Ok(value) => Some(value),
            Err(error) => {
                self.error = Some(error);
                None
            }
        }
    }
    fn argument(&mut self, argument: GenericArg) -> Option<GenericArg> {
        Some(match argument {
            GenericArg::Type(ty) => GenericArg::Type(self.visit(ty)?),
            GenericArg::Const(id) => GenericArg::Const(self.constant(id)?),
            GenericArg::Lifetime(region) => GenericArg::Lifetime(self.region(region)?),
        })
    }
    fn region(&mut self, region: Region) -> Option<Region> {
        if matches!(region, Region::Bound { .. } | Region::Static) {
            return Some(region);
        }
        if let Region::Infer(index) = region {
            return Some(
                *self
                    .regions
                    .entry(index)
                    .or_insert_with(|| self.types.fresh_region()),
            );
        }
        match self
            .types
            .substitute_arg(GenericArg::Lifetime(region), self.owner, self.arguments)
            .ok()?
        {
            GenericArg::Lifetime(Region::Bound { depth, index }) => Some(Region::Bound {
                depth: depth.checked_add(self.binders)?,
                index,
            }),
            GenericArg::Lifetime(region) => Some(region),
            _ => None,
        }
    }
    fn visit(&mut self, ty: TyId) -> Option<TyId> {
        if self.types.depths[ty.0 as usize] > 128 {
            return None;
        }
        if let Some(&resolved) = self.memo.get(&(ty, self.binders)) {
            return Some(resolved);
        }
        self.remaining = self.remaining.checked_sub(1)?;
        let resolved = match self.types.get(ty).clone() {
            Ty::Parameter { owner, index } if owner == self.owner => {
                let argument = self.arguments.get(index as usize)?.ty()?;
                if self.types.depths[argument.0 as usize] > 128 {
                    return None;
                }
                return self.types.shift_bound_regions(argument, self.binders);
            }
            Ty::Named {
                definition,
                arguments,
            } => Ty::Named {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|arg| self.argument(arg))
                    .collect::<Option<_>>()?,
            },
            Ty::Reference {
                region,
                mutable,
                inner,
            } => {
                let region = self.region(region)?;
                Ty::Reference {
                    region,
                    mutable,
                    inner: self.visit(inner)?,
                }
            }
            Ty::Pointer { constant, inner } => Ty::Pointer {
                constant,
                inner: self.visit(inner)?,
            },
            Ty::Array { inner, length } => Ty::Array {
                inner: self.visit(inner)?,
                length,
            },
            Ty::SymbolicArray { inner, length } => {
                let inner = self.visit(inner)?;
                let length = self.constant(length)?;
                match self.types.const_usize(length) {
                    Some(length) => Ty::Array { inner, length },
                    None => Ty::SymbolicArray { inner, length },
                }
            }
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => Ty::Dynamic {
                trait_definition,
                arguments: arguments
                    .into_iter()
                    .map(|arg| self.argument(arg))
                    .collect::<Option<_>>()?,
            },
            Ty::Slice(inner) => Ty::Slice(self.visit(inner)?),
            Ty::ForAll { parameters, inner } => {
                self.binders = self.binders.checked_add(1)?;
                let inner = self.visit(inner);
                self.binders -= 1;
                Ty::ForAll {
                    parameters,
                    inner: inner?,
                }
            }
            Ty::Function { parameters, result } => Ty::Function {
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.visit(ty))
                    .collect::<Option<_>>()?,
                result: self.visit(result)?,
            },
            _ => return Some(ty),
        };
        if self.types.depth(&resolved) > 128 {
            return None;
        }
        let resolved = self.types.intern(resolved);
        self.memo.insert((ty, self.binders), resolved);
        Some(resolved)
    }
}
