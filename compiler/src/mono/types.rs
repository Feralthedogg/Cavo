use super::*;
use crate::types::{ConstId, ConstKind, ConstValue, Ty, TypeContext};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Domain {
    Template,
    Argument,
}

#[derive(Default)]
pub(super) struct Mapping {
    types: HashMap<(TyId, Domain), TyId>,
    regions: HashMap<u32, Region>,
}

pub(super) struct Substitution<'a> {
    pub owner: hir::DefId,
    pub arguments: &'a [GenericArg],
    pub destination: hir::DefId,
}

pub(super) struct Mapper<'a, 'b> {
    pub program: &'a mut hir::Program,
    substitution: Substitution<'b>,
    constants: ctfe::Limits,
    mapping: &'a mut Mapping,
    remaining: usize,
}
impl<'a, 'b> Mapper<'a, 'b> {
    pub fn new(
        program: &'a mut hir::Program,
        substitution: Substitution<'b>,
        constants: ctfe::Limits,
        mapping: &'a mut Mapping,
    ) -> Self {
        Self {
            program,
            substitution,
            constants,
            mapping,
            remaining: 200_000,
        }
    }
    pub fn ty(&mut self, ty: TyId) -> Result<TyId, String> {
        self.visit(ty, Domain::Template, 0)
    }
    pub fn argument(&mut self, argument: GenericArg) -> Result<GenericArg, String> {
        self.map_argument(argument, Domain::Template, 0)
    }
    pub fn normalize_argument(&mut self, argument: GenericArg) -> Result<GenericArg, String> {
        let argument = self.map_argument(argument, Domain::Argument, 0)?;
        if let GenericArg::Type(ty) = argument {
            require_concrete(&self.program.types, ty)?;
        }
        if let GenericArg::Const(value) = argument
            && self.program.types.const_usize(value).is_none()
        {
            return Err("const generic arguments require concrete target usize values".into());
        }
        Ok(argument)
    }
    pub fn constant(&mut self, id: ConstId) -> Result<ConstId, String> {
        let id = self
            .program
            .types
            .const_substitute(id, self.substitution.owner, self.substitution.arguments)
            .map_err(|error| error.to_string())?;
        ctfe::evaluate_term(self.program, id, self.constants).map_err(|error| error.to_string())
    }
    fn visit(&mut self, ty: TyId, domain: Domain, depth: usize) -> Result<TyId, String> {
        if let Some(&mapped) = self.mapping.types.get(&(ty, domain)) {
            return Ok(mapped);
        }
        if depth >= 128 || self.remaining == 0 {
            return Err("monomorphic type substitution limit exceeded".into());
        }
        self.remaining -= 1;
        let kind = self
            .program
            .types
            .values()
            .get(ty.0 as usize)
            .cloned()
            .ok_or("invalid monomorphic type ID")?;
        let value = self.kind(kind, domain, depth + 1)?;
        let mapped = self.program.types.intern(value);
        self.mapping.types.insert((ty, domain), mapped);
        Ok(mapped)
    }
    fn kind(&mut self, kind: Ty, domain: Domain, depth: usize) -> Result<Ty, String> {
        Ok(match kind {
            Ty::Parameter { owner, index }
                if domain == Domain::Template && owner == self.substitution.owner =>
            {
                let Some(GenericArg::Type(actual)) =
                    self.substitution.arguments.get(index as usize)
                else {
                    return Err("missing concrete type argument".into());
                };
                let actual = self.visit(*actual, Domain::Argument, depth)?;
                self.program.types.get(actual).clone()
            }
            Ty::Reference {
                region,
                mutable,
                inner,
            } => Ty::Reference {
                region: self.region(region, domain),
                mutable,
                inner: self.visit(inner, domain, depth)?,
            },
            Ty::Pointer { constant, inner } => Ty::Pointer {
                constant,
                inner: self.visit(inner, domain, depth)?,
            },
            Ty::Array { inner, length } => Ty::Array {
                inner: self.visit(inner, domain, depth)?,
                length,
            },
            Ty::SymbolicArray { inner, length } => self.array(inner, length, domain, depth)?,
            Ty::Slice(inner) => Ty::Slice(self.visit(inner, domain, depth)?),
            Ty::Function { parameters, result } => Ty::Function {
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.visit(ty, domain, depth))
                    .collect::<Result<_, _>>()?,
                result: self.visit(result, domain, depth)?,
            },
            Ty::ForAll { parameters, inner } => Ty::ForAll {
                parameters,
                inner: self.visit(inner, domain, depth)?,
            },
            Ty::Named {
                definition,
                arguments,
            } => Ty::Named {
                definition,
                arguments: self.arguments(arguments, domain, depth)?,
            },
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => Ty::Dynamic {
                trait_definition,
                arguments: self.arguments(arguments, domain, depth)?,
            },
            other => other,
        })
    }
    fn array(
        &mut self,
        inner: TyId,
        length: ConstId,
        domain: Domain,
        depth: usize,
    ) -> Result<Ty, String> {
        let length = self.map_constant(length, domain)?;
        let length = self
            .program
            .types
            .const_usize(length)
            .ok_or("array length did not resolve to usize")?;
        Ok(Ty::Array {
            inner: self.visit(inner, domain, depth)?,
            length,
        })
    }
    fn region(&mut self, region: Region, domain: Domain) -> Region {
        if domain == Domain::Argument {
            return region;
        }
        match region {
            Region::Infer(index) => *self
                .mapping
                .regions
                .entry(index)
                .or_insert_with(|| self.program.types.fresh_region()),
            Region::Named { owner, name } if owner == self.substitution.owner => {
                let slot = self
                    .program
                    .types
                    .generic_parameters(owner)
                    .iter()
                    .position(|(found, kind)| {
                        *found == name && *kind == GenericParamKind::Lifetime
                    });
                if let Some(GenericArg::Lifetime(actual)) =
                    slot.and_then(|slot| self.substitution.arguments.get(slot))
                {
                    return *actual;
                }
                Region::Named {
                    owner: self.substitution.destination,
                    name,
                }
            }
            other => other,
        }
    }
    fn arguments(
        &mut self,
        arguments: Vec<GenericArg>,
        domain: Domain,
        depth: usize,
    ) -> Result<Vec<GenericArg>, String> {
        arguments
            .into_iter()
            .map(|argument| self.map_argument(argument, domain, depth))
            .collect()
    }
    fn map_argument(
        &mut self,
        argument: GenericArg,
        domain: Domain,
        depth: usize,
    ) -> Result<GenericArg, String> {
        Ok(match argument {
            GenericArg::Type(ty) => GenericArg::Type(self.visit(ty, domain, depth)?),
            GenericArg::Const(value) => GenericArg::Const(self.map_constant(value, domain)?),
            GenericArg::Lifetime(region) => GenericArg::Lifetime(self.region(region, domain)),
        })
    }
    fn map_constant(&mut self, value: ConstId, domain: Domain) -> Result<ConstId, String> {
        if domain == Domain::Template {
            return self.constant(value);
        }
        ctfe::evaluate_term(self.program, value, self.constants).map_err(|error| error.to_string())
    }
}

pub(super) fn kind_matches(argument: GenericArg, kind: GenericParamKind) -> bool {
    argument.kind() == kind
}

pub(super) fn require_concrete(types: &TypeContext, root: TyId) -> Result<(), String> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) {
            continue;
        }
        if seen.len() > 200_000 {
            return Err("concrete type verification limit exceeded".into());
        }
        let ty = types
            .values()
            .get(ty.0 as usize)
            .ok_or("invalid concrete type ID")?;
        match ty {
            Ty::Parameter { .. } | Ty::SymbolicArray { .. } | Ty::Error => {
                return Err(
                    "unresolved type or array length remains after monomorphization".into(),
                );
            }
            Ty::Reference { inner, .. }
            | Ty::Pointer { inner, .. }
            | Ty::Array { inner, .. }
            | Ty::Slice(inner)
            | Ty::ForAll { inner, .. } => pending.push(*inner),
            Ty::Function { parameters, result } => {
                pending.extend(parameters);
                pending.push(*result);
            }
            Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                concrete_arguments(types, arguments, &mut pending)?
            }
            _ => {}
        }
    }
    Ok(())
}
fn concrete_arguments(
    types: &TypeContext,
    arguments: &[GenericArg],
    pending: &mut Vec<TyId>,
) -> Result<(), String> {
    for &argument in arguments {
        match argument {
            GenericArg::Type(ty) => pending.push(ty),
            GenericArg::Const(value) => {
                if !matches!(
                    types
                        .constant_terms()
                        .get(value.0 as usize)
                        .map(|term| &term.kind),
                    Some(ConstKind::Value(ConstValue::Usize(_)))
                ) {
                    return Err("generic const argument is not a concrete usize".into());
                }
            }
            GenericArg::Lifetime(_) => {}
        }
    }
    Ok(())
}
