//! One binder-aware visitor for runtime types and their constant arguments.
use super::*;

pub(super) fn map_type(
    types: &mut TypeContext,
    ty: TyId,
    map: &mut impl FnMut(Region, u16) -> Region,
) -> Option<TyId> {
    Mapper::new(types, map).ty(ty, 0)
}
pub(super) fn map_constant(
    types: &mut TypeContext,
    id: ConstId,
    map: &mut impl FnMut(Region, u16) -> Region,
) -> Option<ConstId> {
    Mapper::new(types, map).constant(id, 0)
}
struct Mapper<'a, F> {
    types: &'a mut TypeContext,
    map: &'a mut F,
    types_memo: HashMap<(TyId, u16), TyId>,
    const_memo: HashMap<(ConstId, u16), ConstId>,
    remaining: usize,
}
impl<'a, F: FnMut(Region, u16) -> Region> Mapper<'a, F> {
    fn new(types: &'a mut TypeContext, map: &'a mut F) -> Self {
        Self {
            types,
            map,
            types_memo: HashMap::new(),
            const_memo: HashMap::new(),
            remaining: 4096,
        }
    }
    fn ty(&mut self, ty: TyId, depth: u16) -> Option<TyId> {
        if let Some(&id) = self.types_memo.get(&(ty, depth)) {
            return Some(id);
        }
        self.remaining = self.remaining.checked_sub(1)?;
        if self.types.nesting(ty) > 128 || depth > 128 {
            return None;
        }
        let value = self.types.get(ty).clone();
        let value = self.shape(value, depth)?;
        let id = self.types.intern(value);
        self.types_memo.insert((ty, depth), id);
        Some(id)
    }
    fn shape(&mut self, value: Ty, depth: u16) -> Option<Ty> {
        Some(match value {
            Ty::Reference {
                region,
                mutable,
                inner,
            } => Ty::Reference {
                region: (self.map)(region, depth),
                mutable,
                inner: self.ty(inner, depth)?,
            },
            Ty::Pointer { constant, inner } => Ty::Pointer {
                constant,
                inner: self.ty(inner, depth)?,
            },
            Ty::Array { inner, length } => Ty::Array {
                inner: self.ty(inner, depth)?,
                length,
            },
            Ty::SymbolicArray { inner, length } => Ty::SymbolicArray {
                inner: self.ty(inner, depth)?,
                length: self.constant(length, depth)?,
            },
            Ty::Slice(inner) => Ty::Slice(self.ty(inner, depth)?),
            Ty::Named {
                definition,
                arguments,
            } => Ty::Named {
                definition,
                arguments: self.arguments(arguments, depth)?,
            },
            Ty::Dynamic {
                trait_definition,
                arguments,
            } => Ty::Dynamic {
                trait_definition,
                arguments: self.arguments(arguments, depth)?,
            },
            Ty::Function { parameters, result } => Ty::Function {
                parameters: parameters
                    .into_iter()
                    .map(|ty| self.ty(ty, depth))
                    .collect::<Option<_>>()?,
                result: self.ty(result, depth)?,
            },
            Ty::ForAll { parameters, inner } => Ty::ForAll {
                parameters,
                inner: self.ty(inner, depth.checked_add(1)?)?,
            },
            other => other,
        })
    }
    fn arguments(&mut self, arguments: Vec<GenericArg>, depth: u16) -> Option<Vec<GenericArg>> {
        arguments
            .into_iter()
            .map(|argument| self.argument(argument, depth))
            .collect()
    }
    fn argument(&mut self, argument: GenericArg, depth: u16) -> Option<GenericArg> {
        Some(match argument {
            GenericArg::Type(ty) => GenericArg::Type(self.ty(ty, depth)?),
            GenericArg::Const(id) => GenericArg::Const(self.constant(id, depth)?),
            GenericArg::Lifetime(region) => GenericArg::Lifetime((self.map)(region, depth)),
        })
    }
    fn constant(&mut self, id: ConstId, depth: u16) -> Option<ConstId> {
        if let Some(&value) = self.const_memo.get(&(id, depth)) {
            return Some(value);
        }
        self.remaining = self.remaining.checked_sub(1)?;
        if depth > 128 {
            return None;
        }
        let term = self.types.constant_terms().get(id.0 as usize)?.clone();
        let kind = match term.kind {
            ConstKind::Unary { op, operand } => ConstKind::Unary {
                op,
                operand: self.constant(operand, depth)?,
            },
            ConstKind::Binary { op, left, right } => ConstKind::Binary {
                op,
                left: self.constant(left, depth)?,
                right: self.constant(right, depth)?,
            },
            ConstKind::Call {
                definition,
                type_arguments,
                arguments,
            } => ConstKind::Call {
                definition,
                type_arguments: self.arguments(type_arguments, depth)?,
                arguments: arguments
                    .into_iter()
                    .map(|id| self.constant(id, depth))
                    .collect::<Option<_>>()?,
            },
            other => other,
        };
        let value = self
            .types
            .intern_const(ConstTerm { ty: term.ty, kind })
            .ok()?;
        self.const_memo.insert((id, depth), value);
        Some(value)
    }
}
