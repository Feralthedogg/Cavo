//! Normalize required constant arguments without instantiating function bodies.
use super::{Error, Limits, evaluate_term};
use crate::{
    hir,
    source::{FileId, Span},
    types::{GenericArg, Ty, TyId},
};
use std::collections::HashMap;

pub fn normalize_type_constants(
    program: &mut hir::Program,
    ty: TyId,
    limits: Limits,
) -> Result<TyId, Error> {
    let span = program
        .definitions
        .first()
        .map_or(Span::new(FileId(0), 0, 0), |definition| definition.span);
    if limits.pointer_bits != 64 {
        return Err(Error::new(
            "E-CONST-CONTEXT",
            "type-level constant terms require the selected 64-bit target",
            span,
        ));
    }
    Normalize {
        program,
        limits,
        span,
        remaining: 4096,
        memo: HashMap::new(),
        constants: HashMap::new(),
    }
    .ty(ty, 0)
}

struct Normalize<'a> {
    program: &'a mut hir::Program,
    limits: Limits,
    span: Span,
    remaining: usize,
    memo: HashMap<TyId, TyId>,
    constants: HashMap<crate::types::ConstId, crate::types::ConstId>,
}
impl Normalize<'_> {
    fn ty(&mut self, ty: TyId, depth: usize) -> Result<TyId, Error> {
        if let Some(&value) = self.memo.get(&ty) {
            return Ok(value);
        }
        if depth >= 128 || self.remaining == 0 {
            return Err(Error::new(
                "E-CONST-LIMIT",
                "constant type normalization exceeds its work limit",
                self.span,
            ));
        }
        self.remaining -= 1;
        let kind = self
            .program
            .types
            .values()
            .get(ty.0 as usize)
            .cloned()
            .ok_or_else(|| {
                Error::new(
                    "E-CONST-CONTEXT",
                    "constant type normalization received an invalid type",
                    self.span,
                )
            })?;
        let kind = self.children(kind, depth + 1)?;
        let value = self.program.types.intern(kind);
        self.memo.insert(ty, value);
        Ok(value)
    }
    fn children(&mut self, kind: Ty, depth: usize) -> Result<Ty, Error> {
        Ok(match kind {
            Ty::Reference {
                region,
                mutable,
                inner,
            } => Ty::Reference {
                region,
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
            Ty::SymbolicArray { inner, length } => {
                let inner = self.ty(inner, depth)?;
                let length = self.constant(length)?;
                match self.program.types.const_usize(length) {
                    Some(length) => Ty::Array { inner, length },
                    None => Ty::SymbolicArray { inner, length },
                }
            }
            Ty::Slice(inner) => Ty::Slice(self.ty(inner, depth)?),
            Ty::ForAll { parameters, inner } => Ty::ForAll {
                parameters,
                inner: self.ty(inner, depth)?,
            },
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
                    .collect::<Result<_, _>>()?,
                result: self.ty(result, depth)?,
            },
            other => other,
        })
    }
    fn arguments(
        &mut self,
        arguments: Vec<GenericArg>,
        depth: usize,
    ) -> Result<Vec<GenericArg>, Error> {
        arguments
            .into_iter()
            .map(|argument| match argument {
                GenericArg::Type(ty) => self.ty(ty, depth).map(GenericArg::Type),
                GenericArg::Const(value) => self.constant(value).map(GenericArg::Const),
                GenericArg::Lifetime(_) => Ok(argument),
            })
            .collect()
    }
    fn constant(&mut self, id: crate::types::ConstId) -> Result<crate::types::ConstId, Error> {
        if let Some(&value) = self.constants.get(&id) {
            return Ok(value);
        }
        if matches!(
            self.program.types.const_term(id).kind,
            crate::types::ConstKind::Value(_)
        ) {
            return Ok(id);
        }
        let concrete = self
            .program
            .types
            .generic_arguments_concrete(&[GenericArg::Const(id)])
            .map_err(|error| Error::new("E-CONST-LIMIT", error.to_string(), self.span))?;
        let value = if concrete {
            evaluate_term(self.program, id, self.limits)?
        } else {
            id
        };
        self.constants.insert(id, value);
        Ok(value)
    }
}
