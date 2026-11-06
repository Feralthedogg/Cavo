use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Tracking {
    Drops,
    Initialization,
}

pub(super) struct Owner {
    pub flag: FlagId,
    pub dependencies: Range<usize>,
}
pub(super) struct Paths {
    pub(super) flags: Vec<Flag>,
    locals: Vec<Range<usize>>,
    captures: Vec<Option<Place>>,
    droppable: HashSet<Place>,
    owners: Vec<Owner>,
}
impl Paths {
    pub(super) fn build(core: &super::super::Body, glue: &mut Glues<'_>) -> Result<Self, Error> {
        let mut paths = Self {
            flags: Vec::new(),
            locals: Vec::with_capacity(core.locals.len()),
            captures: captures(core)?,
            droppable: droppable_places(core, glue)?,
            owners: Vec::new(),
        };
        for (index, local) in core.locals.iter().enumerate() {
            let start = paths.flags.len();
            if local.kind != LocalKind::Address && glue.properties.get(local.ty).may_drop {
                glue.resolve(local.ty, 0)?;
            }
            let place = Place::local(super::super::LocalId(index as u32));
            match local.kind {
                LocalKind::Address => {}
                LocalKind::ArrayIterator if glue.properties.get(local.ty).may_drop => {
                    let plan = glue.tail(local.ty)?;
                    paths.push(place, local.ty, plan, FlagKind::Value, &[])?;
                }
                _ => {
                    paths.add(place, local.ty, glue, &[], Tracking::Drops, 0)?;
                }
            }
            paths.locals.push(start..paths.flags.len());
        }
        Ok(paths)
    }
    fn add(
        &mut self,
        place: Place,
        ty: TyId,
        glue: &mut Glues<'_>,
        guards: &[VariantGuard],
        tracking: Tracking,
        depth: usize,
    ) -> Result<(), Error> {
        if !glue.properties.get(ty).may_drop && tracking == Tracking::Drops {
            return Ok(());
        }
        if depth >= 64 {
            return Err(Error("drop path nesting limit exceeded".into()));
        }
        // User destructors use a separate flag from structural fields. A field
        // assignment cannot accidentally call or initialize the entire owner.
        let owner = if let Some(plan) = glue.destructor(ty)? {
            Some(self.push(place.clone(), ty, plan, FlagKind::UserDestructor, guards)?)
        } else {
            None
        };
        let start = self.flags.len();
        self.children(
            place.clone(),
            ty,
            glue,
            guards,
            if owner.is_some() {
                Tracking::Initialization
            } else {
                tracking
            },
            depth,
        )?;
        if let Some(flag) = owner {
            self.owners.push(Owner {
                flag,
                dependencies: start..self.flags.len(),
            });
        } else if self.flags.len() == start && tracking == Tracking::Initialization {
            let plan = glue.resolve(ty, depth)?;
            self.push(place, ty, plan, FlagKind::Initialization, guards)?;
        }
        Ok(())
    }
    fn children(
        &mut self,
        place: Place,
        ty: TyId,
        glue: &mut Glues<'_>,
        guards: &[VariantGuard],
        tracking: Tracking,
        depth: usize,
    ) -> Result<(), Error> {
        let properties = glue.properties;
        if let Some(fields) = properties.fields(ty) {
            for (index, &field) in fields.iter().enumerate() {
                self.add(
                    place.clone().project(Projection::Field(index as u32)),
                    field,
                    glue,
                    guards,
                    tracking,
                    depth + 1,
                )?;
            }
            return Ok(());
        }
        if let Ty::Named { definition, .. } = glue.hir.types.get(ty)
            && let Some(enumeration) = glue
                .hir
                .enums
                .iter()
                .find(|enumeration| enumeration.definition == *definition)
        {
            let variants = enumeration.variants.clone();
            for variant in variants {
                self.variant(
                    VariantGuard {
                        place: place.clone(),
                        variant,
                    },
                    ty,
                    glue,
                    guards,
                    tracking,
                    depth,
                )?;
            }
            return Ok(());
        }
        let plan = glue.resolve(ty, depth)?;
        let kind = if glue.properties.get(ty).may_drop {
            FlagKind::Value
        } else {
            FlagKind::Initialization
        };
        self.push(place, ty, plan, kind, guards)?;
        Ok(())
    }
    fn variant(
        &mut self,
        projection: VariantGuard,
        ty: TyId,
        glue: &mut Glues<'_>,
        guards: &[VariantGuard],
        tracking: Tracking,
        depth: usize,
    ) -> Result<(), Error> {
        let properties = glue.properties;
        let fields = properties
            .variant_fields(ty, projection.variant)
            .ok_or_else(|| Error("invalid enum cleanup variant".into()))?;
        let mut conditions = guards.to_vec();
        let base = projection
            .place
            .clone()
            .project(Projection::Downcast(projection.variant));
        conditions.push(projection);
        for (index, &field) in fields.iter().enumerate() {
            self.add(
                base.clone().project(Projection::Field(index as u32)),
                field,
                glue,
                &conditions,
                tracking,
                depth + 1,
            )?;
        }
        Ok(())
    }
    fn push(
        &mut self,
        place: Place,
        ty: TyId,
        plan: GlueId,
        kind: FlagKind,
        guards: &[VariantGuard],
    ) -> Result<FlagId, Error> {
        if self.flags.len() >= LIMIT {
            return Err(Error("drop flag resource limit exceeded".into()));
        }
        let id = FlagId(self.flags.len() as u32);
        self.flags.push(Flag {
            place,
            ty,
            glue: plan,
            kind,
            guards: guards.to_vec(),
        });
        Ok(id)
    }
    fn resolve(&self, place: &Place, depth: usize) -> Result<Place, Error> {
        if depth >= 64 {
            return Err(Error("drop capture depth limit exceeded".into()));
        }
        if place.projection.first() == Some(&Projection::Deref)
            && let Some(captured) = &self.captures[place.local.0 as usize]
        {
            let mut target = captured.clone();
            target.projection.extend_from_slice(&place.projection[1..]);
            return self.resolve(&target, depth + 1);
        }
        Ok(place.clone())
    }
    pub(super) fn affected(&self, place: &Place, change: FlagValue) -> Result<Vec<FlagId>, Error> {
        let target = self.resolve(place, 0)?;
        let mut flags = Vec::new();
        for index in self.locals[target.local.0 as usize].clone() {
            let owned = &self.flags[index];
            if owned.place.projection.starts_with(&target.projection) {
                flags.push(FlagId(index as u32));
            } else if target.projection.starts_with(&owned.place.projection)
                && owned.kind != FlagKind::UserDestructor
                && !(change == FlagValue::Set && owned.kind == FlagKind::Initialization)
            {
                return Err(Error(
                    "indexed or indirect partial ownership needs finer drop flags".into(),
                ));
            }
        }
        if flags.is_empty() && self.droppable.contains(place) {
            return Err(Error("indirect ownership needs a verified caller-owned drop flag or initialized-pointee contract".into()));
        }
        Ok(flags)
    }
    pub(super) fn ancestors(&self, place: &Place) -> Result<Vec<&Owner>, Error> {
        let target = self.resolve(place, 0)?;
        // Owners were appended after their children, giving inner-to-outer
        // dependency order. Recompute inner completeness before its parent.
        Ok(self
            .owners
            .iter()
            .filter(|owner| {
                let owned = &self.flags[owner.flag.0 as usize].place;
                owned.local == target.local
                    && owned.projection != target.projection
                    && target.projection.starts_with(&owned.projection)
            })
            .collect())
    }
    pub(super) fn ensure_movable(&self, place: &Place) -> Result<(), Error> {
        if !self.ancestors(place)?.is_empty() {
            return Err(Error(
                "a type with user Drop cannot be partially moved".into(),
            ));
        }
        Ok(())
    }
}
