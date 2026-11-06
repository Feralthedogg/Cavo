use super::{GenericArg, Region, Ty, TyId, TypeContext};
use crate::hir::DefId;
use std::collections::{HashMap, HashSet};

impl TypeContext {
    pub(super) fn shift_bound_regions(&mut self, ty: TyId, amount: u16) -> Option<TyId> {
        if amount == 0 {
            return Some(ty);
        }
        let mut overflow = false;
        let mapped = self.map_regions(ty, &mut |region, nesting| match region {
            Region::Bound { depth, index } if depth >= nesting => match depth.checked_add(amount) {
                Some(depth) => Region::Bound { depth, index },
                None => {
                    overflow = true;
                    region
                }
            },
            _ => region,
        })?;
        (!overflow).then_some(mapped)
    }
    pub(super) fn regions_in(&self, root: TyId) -> Option<HashSet<Region>> {
        let mut pending = vec![GenericArg::Type(root)];
        let mut seen = HashSet::new();
        let mut regions = HashSet::new();
        while let Some(argument) = pending.pop() {
            if !seen.insert(argument) {
                continue;
            }
            if seen.len() > 4096 {
                return None;
            }
            if let GenericArg::Lifetime(region) = argument {
                regions.insert(region);
            }
            self.region_children(argument, &mut pending)?;
        }
        Some(regions)
    }
    fn region_children(&self, argument: GenericArg, children: &mut Vec<GenericArg>) -> Option<()> {
        match argument {
            GenericArg::Lifetime(_) => {}
            GenericArg::Const(id) => self
                .constant_terms()
                .get(id.0 as usize)?
                .visit_arguments(|arg| children.push(arg)),
            GenericArg::Type(ty) => match self.values().get(ty.0 as usize)? {
                Ty::Reference { region, inner, .. } => {
                    children.push(GenericArg::Lifetime(*region));
                    children.push(GenericArg::Type(*inner));
                }
                Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                    children.extend(arguments)
                }
                Ty::Pointer { inner, .. }
                | Ty::Array { inner, .. }
                | Ty::Slice(inner)
                | Ty::ForAll { inner, .. } => children.push(GenericArg::Type(*inner)),
                Ty::SymbolicArray { inner, length } => {
                    children.push(GenericArg::Type(*inner));
                    children.push(GenericArg::Const(*length));
                }
                Ty::Function { parameters, result } => {
                    children.extend(parameters.iter().copied().map(GenericArg::Type));
                    children.push(GenericArg::Type(*result));
                }
                _ => {}
            },
        }
        Some(())
    }
    /// Anonymous lifetimes in a callable type are late bound. Alias expansion
    /// must not turn two uses of `fn(&mut T)` into unrelated monomorphic types.
    pub(crate) fn close_callable_elision(&mut self, ty: TyId) -> Option<TyId> {
        let (explicit, inner) = match *self.get(ty) {
            Ty::ForAll { parameters, inner } => (parameters, inner),
            Ty::Function { .. } => (0, ty),
            _ => return Some(ty),
        };
        let mut inferred = HashMap::new();
        self.map_regions(inner, &mut |region, _| {
            if matches!(region, Region::Infer(_)) {
                let next = inferred.len() as u16;
                inferred.entry(region).or_insert(next);
            }
            region
        })?;
        if inferred.is_empty() {
            return Some(ty);
        }
        let parameters = usize::from(explicit) + inferred.len();
        if parameters > 64 {
            return None;
        }
        let inner = self.map_regions(inner, &mut |region, nesting| match region {
            Region::Infer(_) => Region::Bound {
                depth: nesting,
                index: explicit + inferred[&region],
            },
            Region::Bound { depth, index } if explicit == 0 && depth >= nesting => Region::Bound {
                depth: depth + 1,
                index,
            },
            _ => region,
        })?;
        Some(self.intern(Ty::ForAll {
            parameters: parameters as u16,
            inner,
        }))
    }
    pub(crate) fn valid_region_scope(&self, root: TyId) -> bool {
        let mut pending = vec![(GenericArg::Type(root), Vec::<u16>::new())];
        let mut seen = HashSet::new();
        while let Some((argument, mut binders)) = pending.pop() {
            if !self.argument_has_bound(argument) {
                continue;
            }
            if !seen.insert((argument, binders.clone())) {
                continue;
            }
            if seen.len() > 4096 || binders.len() > 128 {
                return false;
            }
            match argument {
                GenericArg::Lifetime(Region::Bound { depth, index })
                    if binders
                        .iter()
                        .rev()
                        .nth(depth as usize)
                        .is_none_or(|&count| index >= count) =>
                {
                    return false;
                }
                GenericArg::Type(ty) => {
                    if let Some(Ty::ForAll { parameters, inner }) = self.values().get(ty.0 as usize)
                    {
                        if *parameters == 0
                            || *parameters > 64
                            || !matches!(self.get(*inner), Ty::Function { .. })
                        {
                            return false;
                        }
                        binders.push(*parameters);
                    }
                }
                _ => {}
            }
            let mut children = Vec::new();
            if self.region_children(argument, &mut children).is_none() {
                return false;
            }
            pending.extend(children.into_iter().map(|child| (child, binders.clone())));
        }
        true
    }
    pub(super) fn map_regions(
        &mut self,
        ty: TyId,
        map: &mut impl FnMut(Region, u16) -> Region,
    ) -> Option<TyId> {
        super::region_map::map_type(self, ty, map)
    }
    pub(super) fn shift_const_regions(
        &mut self,
        id: super::ConstId,
        amount: u16,
    ) -> Option<super::ConstId> {
        if amount == 0 {
            return Some(id);
        }
        let mut overflow = false;
        let result =
            super::region_map::map_constant(self, id, &mut |region, nesting| match region {
                Region::Bound { depth, index } if depth >= nesting => {
                    match depth.checked_add(amount) {
                        Some(depth) => Region::Bound { depth, index },
                        None => {
                            overflow = true;
                            region
                        }
                    }
                }
                _ => region,
            })?;
        (!overflow).then_some(result)
    }

    /// Only the outer binder is opened. Inner binders and the caller's free
    /// lifetimes keep their scope; no bound placeholder escapes into a call.
    pub(crate) fn open_callable(&mut self, ty: TyId) -> Option<TyId> {
        let (parameters, inner, opened) = match *self.get(ty) {
            Ty::ForAll { parameters, inner } => (parameters, inner, true),
            _ => (0, ty, false),
        };
        let replacements: Vec<_> = (0..parameters).map(|_| self.fresh_region()).collect();
        let mut inferred = HashMap::new();
        for region in self.regions_in(inner)? {
            if matches!(region, Region::Infer(_)) {
                inferred.insert(region, self.fresh_region());
            }
        }
        let mut pending = vec![inner];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > 4096 {
                return None;
            }
            match self.get(ty).clone() {
                Ty::Reference { region, inner, .. } => {
                    if matches!(region, Region::Infer(_)) && !inferred.contains_key(&region) {
                        let fresh = self.fresh_region();
                        inferred.insert(region, fresh);
                    }
                    pending.push(inner);
                }
                Ty::Pointer { inner, .. }
                | Ty::Array { inner, .. }
                | Ty::SymbolicArray { inner, .. }
                | Ty::Slice(inner)
                | Ty::ForAll { inner, .. } => pending.push(inner),
                Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                    pending.extend(arguments.iter().filter_map(|arg| arg.ty()))
                }
                Ty::Function { parameters, result } => {
                    pending.extend(parameters);
                    pending.push(result);
                }
                _ => {}
            }
        }
        self.map_regions(inner, &mut |region, nesting| match region {
            Region::Infer(_) => inferred[&region],
            Region::Bound { depth, index } if opened && depth == nesting => {
                replacements.get(index as usize).copied().unwrap_or(region)
            }
            Region::Bound { depth, index } if opened && depth > nesting => Region::Bound {
                depth: depth - 1,
                index,
            },
            _ => region,
        })
    }

    pub(crate) fn elide_callable_result(&mut self, ty: TyId) -> Option<TyId> {
        let Ty::Function { parameters, result } = self.get(ty).clone() else {
            return Some(ty);
        };
        let Ty::Reference {
            region: Region::Infer(id),
            ..
        } = *self.get(result)
        else {
            return Some(ty);
        };
        let mut pending = parameters;
        let mut inputs = Vec::new();
        let mut remaining = 4096usize;
        while let Some(ty) = pending.pop() {
            remaining = remaining.checked_sub(1)?;
            match self.get(ty) {
                Ty::Reference { region, inner, .. } => {
                    inputs.push(*region);
                    pending.push(*inner);
                }
                Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                    pending.extend(arguments.iter().filter_map(|arg| arg.ty()));
                    inputs.extend(arguments.iter().filter_map(|arg| arg.region()));
                }
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    pending.push(*inner)
                }
                _ => {}
            }
        }
        let replacement = match inputs.as_slice() {
            [] => Region::Static,
            [region] => *region,
            _ => return None,
        };
        self.map_regions(ty, &mut |region, nesting| {
            if region == Region::Infer(id) {
                match replacement {
                    Region::Bound { depth, index } => Region::Bound {
                        depth: depth + nesting,
                        index,
                    },
                    _ => replacement,
                }
            } else {
                region
            }
        })
    }

    pub(crate) fn generalize_callable(&mut self, ty: TyId, owner: DefId) -> Option<TyId> {
        let Ty::Function { parameters, result } = self.get(ty).clone() else {
            return Some(ty);
        };
        let mut regions = HashMap::new();
        let mut inputs = HashSet::new();
        let mut pending = parameters;
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > 4096 {
                return None;
            }
            match self.get(ty) {
                Ty::Reference { region, inner, .. } => {
                    if matches!(region, Region::Infer(_))
                        || matches!(region, Region::Named { owner: found, .. } if *found == owner)
                    {
                        inputs.insert(*region);
                    }
                    pending.push(*inner);
                }
                Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                    pending.extend(arguments.iter().filter_map(|arg| arg.ty()));
                    inputs.extend(arguments.iter().filter_map(|arg| arg.region()).filter(|region| {
                        matches!(region, Region::Infer(_)) || matches!(region, Region::Named { owner: found, .. } if *found == owner)
                    }));
                }
                Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
                    pending.push(*inner)
                }
                // Callable-local binders are separate universes.
                _ => {}
            }
        }
        let elided_result = if let Ty::Reference {
            region: Region::Infer(id),
            ..
        } = *self.get(result)
        {
            Some(Region::Infer(id))
        } else {
            None
        };
        let sole = (inputs.len() == 1).then(|| *inputs.iter().next().unwrap());
        let inner = self.map_regions(ty, &mut |mut region, depth| {
            if Some(region) == elided_result {
                if let Some(input) = sole {
                    region = input;
                } else if inputs.is_empty() {
                    return Region::Static;
                }
            }
            if matches!(region, Region::Infer(_))
                || matches!(region, Region::Named { owner: found, .. } if found == owner)
            {
                let next = regions.len() as u16;
                let index = *regions.entry(region).or_insert(next);
                Region::Bound { depth, index }
            } else {
                region
            }
        })?;
        if regions.len() > 64 {
            return None;
        }
        Some(if regions.is_empty() {
            inner
        } else {
            self.intern(Ty::ForAll {
                parameters: regions.len() as u16,
                inner,
            })
        })
    }

    /// A deliberately bounded subtyping check. Shared references are covariant,
    /// function arguments contravariant, and mutable pointees invariant. Nested
    /// universal callable values currently require alpha-equivalent binders.
    pub(crate) fn callable_compatible(&self, actual: TyId, expected: TyId) -> bool {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        enum Term {
            Flexible(u16),
            Rigid(u16, u16),
            Free(Region),
        }
        struct Relation<'a> {
            types: &'a TypeContext,
            actual_bound: u16,
            expected_bound: u16,
            bindings: HashMap<u16, Term>,
            remaining: usize,
            nesting: u16,
        }
        impl Relation<'_> {
            fn argument(&mut self, a: GenericArg, b: GenericArg, depth: usize) -> bool {
                match (a, b) {
                    (GenericArg::Type(a), GenericArg::Type(b)) => self.visit(a, b, 0, depth),
                    (GenericArg::Const(a), GenericArg::Const(b)) => a == b,
                    (GenericArg::Lifetime(a), GenericArg::Lifetime(b)) => self.region(a, b, 0),
                    _ => false,
                }
            }
            fn term(&self, region: Region, actual: bool) -> Term {
                if let Region::Bound { depth, index } = region {
                    if depth < self.nesting {
                        return Term::Rigid(self.nesting - depth, index);
                    }
                    if depth != self.nesting {
                        return Term::Free(region);
                    }
                    if actual && index < self.actual_bound {
                        return Term::Flexible(index);
                    }
                    if !actual && index < self.expected_bound {
                        return Term::Rigid(0, index);
                    }
                }
                Term::Free(region)
            }
            fn region(&mut self, a: Region, b: Region, variance: i8) -> bool {
                let mut a = self.term(a, true);
                let mut b = self.term(b, false);
                if let Term::Flexible(index) = a {
                    if let Some(bound) = self.bindings.get(&index) {
                        a = *bound;
                    } else {
                        if matches!(b,Term::Rigid(depth,_) if depth>0) {
                            return false;
                        }
                        self.bindings.insert(index, b);
                        a = b;
                    }
                }
                if let Term::Flexible(index) = b {
                    if let Some(bound) = self.bindings.get(&index) {
                        b = *bound;
                    } else {
                        if matches!(a,Term::Rigid(depth,_) if depth>0) {
                            return false;
                        }
                        self.bindings.insert(index, a);
                        b = a;
                    }
                }
                a == b
                    || variance > 0 && a == Term::Free(Region::Static)
                    || variance < 0 && b == Term::Free(Region::Static)
            }
            fn visit(&mut self, a: TyId, b: TyId, variance: i8, depth: usize) -> bool {
                if self.remaining == 0 || depth >= 128 {
                    return false;
                }
                self.remaining -= 1;
                match (self.types.get(a), self.types.get(b)) {
                    (
                        Ty::Reference {
                            region: ar,
                            mutable: am,
                            inner: ai,
                        },
                        Ty::Reference {
                            region: br,
                            mutable: bm,
                            inner: bi,
                        },
                    ) => {
                        am == bm
                            && self.region(*ar, *br, variance)
                            && self.visit(*ai, *bi, if *am { 0 } else { variance }, depth + 1)
                    }
                    (
                        Ty::Function {
                            parameters: ap,
                            result: ar,
                        },
                        Ty::Function {
                            parameters: bp,
                            result: br,
                        },
                    ) => {
                        ap.len() == bp.len()
                            && ap
                                .iter()
                                .zip(bp)
                                .all(|(&a, &b)| self.visit(a, b, -variance, depth + 1))
                            && self.visit(*ar, *br, variance, depth + 1)
                    }
                    (
                        Ty::Named {
                            definition: ad,
                            arguments: aa,
                        },
                        Ty::Named {
                            definition: bd,
                            arguments: ba,
                        },
                    )
                    | (
                        Ty::Dynamic {
                            trait_definition: ad,
                            arguments: aa,
                        },
                        Ty::Dynamic {
                            trait_definition: bd,
                            arguments: ba,
                        },
                    ) => {
                        ad == bd
                            && aa.len() == ba.len()
                            && aa
                                .iter()
                                .zip(ba)
                                .all(|(&a, &b)| self.argument(a, b, depth + 1))
                    }
                    (
                        Ty::Array {
                            inner: ai,
                            length: al,
                        },
                        Ty::Array {
                            inner: bi,
                            length: bl,
                        },
                    ) => al == bl && self.visit(*ai, *bi, variance, depth + 1),
                    (
                        Ty::SymbolicArray {
                            inner: ai,
                            length: al,
                        },
                        Ty::SymbolicArray {
                            inner: bi,
                            length: bl,
                        },
                    ) => al == bl && self.visit(*ai, *bi, variance, depth + 1),
                    (Ty::Slice(a), Ty::Slice(b)) => self.visit(*a, *b, variance, depth + 1),
                    (
                        Ty::Pointer {
                            constant: ac,
                            inner: ai,
                        },
                        Ty::Pointer {
                            constant: bc,
                            inner: bi,
                        },
                    ) => ac == bc && self.visit(*ai, *bi, 0, depth + 1),
                    (
                        Ty::ForAll {
                            parameters: ac,
                            inner: ai,
                        },
                        Ty::ForAll {
                            parameters: bc,
                            inner: bi,
                        },
                    ) => {
                        if ac != bc {
                            return false;
                        }
                        self.nesting += 1;
                        let result = self.visit(*ai, *bi, variance, depth + 1);
                        self.nesting -= 1;
                        result
                    }
                    _ => a == b,
                }
            }
        }
        let (actual_bound, actual) = match *self.get(actual) {
            Ty::ForAll { parameters, inner } => (parameters, inner),
            _ => (0, actual),
        };
        let (expected_bound, expected) = match *self.get(expected) {
            Ty::ForAll { parameters, inner } => (parameters, inner),
            _ => (0, expected),
        };
        Relation {
            types: self,
            actual_bound,
            expected_bound,
            bindings: HashMap::new(),
            remaining: 4096,
            nesting: 0,
        }
        .visit(actual, expected, 1, 0)
    }
}
