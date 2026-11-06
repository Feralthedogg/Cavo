use super::*;

impl Verifier<'_> {
    pub(super) fn extended_value(
        &self,
        value: &Rvalue,
        expected: TyId,
    ) -> Result<(), InvariantError> {
        match value {
            Rvalue::IsVariant { place, variant } => {
                self.variant_fields(self.value_place(place)?, *variant)?;
                self.compatible(TyId::BOOL, expected)
            }
            Rvalue::RepeatConst { value, count } => {
                let element = self.operand(value)?;
                require(
                    self.properties.get(element).copy,
                    "repeat requires Copy elements",
                )?;
                let term = self
                    .program
                    .types
                    .constant_terms()
                    .get(count.0 as usize)
                    .ok_or_else(|| InvariantError::new("invalid repeat constant".into()))?;
                require(
                    matches!(
                        self.ty(term.ty)?,
                        Ty::Integer {
                            signed: false,
                            bits: 0
                        }
                    ),
                    "repeat count is not usize",
                )?;
                let inner = match self.ty(expected)? {
                    Ty::Array { inner, length }
                        if self.program.types.const_usize(*count) == Some(*length) =>
                    {
                        *inner
                    }
                    Ty::SymbolicArray { inner, length } if length == count => *inner,
                    _ => return fail("repeat constant disagrees with its array type"),
                };
                self.compatible(element, inner)
            }
            Rvalue::DynCoerce { value, vtable } => self.dynamic_coercion(value, *vtable, expected),
            _ => fail("unexpected extended rvalue"),
        }
    }

    fn dynamic_coercion(
        &self,
        value: &Operand,
        table: u32,
        expected: TyId,
    ) -> Result<(), InvariantError> {
        let actual = self.operand(value)?;
        let (
            Ty::Reference {
                inner: source,
                mutable: a,
                ..
            },
            Ty::Reference {
                inner: target,
                mutable: b,
                ..
            },
        ) = (self.ty(actual)?, self.ty(expected)?)
        else {
            return fail("dynamic coercion requires reference operands");
        };
        require(a == b, "dynamic coercion changes reference mutability")?;
        let Ty::Dynamic {
            trait_definition,
            arguments,
        } = self.ty(*target)?
        else {
            return fail("dynamic coercion has non-dynamic target");
        };
        let table = self
            .program
            .vtables
            .get(table as usize)
            .ok_or_else(|| InvariantError::new("invalid vtable ID".into()))?;
        require(
            table.trait_ref.definition == *trait_definition
                && table.trait_ref.arguments == *arguments,
            "dynamic coercion uses a different trait witness",
        )?;
        self.compatible(*source, table.concrete)?;
        require(
            self.program.types.region_invariant(*source, table.concrete),
            "dynamic coercion changes concrete storage regions",
        )
    }

    pub(super) fn value_place(&self, place: &Place) -> Result<TyId, InvariantError> {
        require(
            !matches!(
                self.local(place.local)?.kind,
                LocalKind::ArrayIterator | LocalKind::TaskRegistry
            ),
            "owned iterator storage is not an ordinary value",
        )?;
        self.place(place)
    }

    pub(super) fn variant_fields(
        &self,
        ty: TyId,
        variant: hir::DefId,
    ) -> Result<&[TyId], InvariantError> {
        self.properties.variant_fields(ty, variant).ok_or_else(|| {
            InvariantError::new("variant projection does not belong to this enum".into())
        })
    }

    pub(super) fn iterator_element(&self, iterator: LocalId) -> Result<TyId, InvariantError> {
        let local = self.local(iterator)?;
        require(
            local.kind == LocalKind::ArrayIterator,
            "iterator operation requires owned iterator storage",
        )?;
        match self.ty(local.ty)? {
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => Ok(*inner),
            _ => fail("owned iterator storage must contain an array"),
        }
    }

    pub(super) fn iterator_structure(
        &self,
        iterator: LocalId,
        destination: &Place,
        some: BlockId,
        none: BlockId,
    ) -> Result<(), InvariantError> {
        let inner = self.iterator_element(iterator)?;
        require(
            destination.projection.is_empty() && destination.local != iterator,
            "iterator result requires separate local storage",
        )?;
        self.compatible(self.value_place(destination)?, inner)?;
        self.block(some)?;
        self.block(none)?;
        Ok(())
    }
}
