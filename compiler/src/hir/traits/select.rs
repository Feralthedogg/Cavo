use super::*;
use crate::{
    hir::Program,
    types::{ConstId, ConstKind, Region, Ty},
};
use std::{collections::HashSet, fmt};

#[derive(Clone, Debug)]
pub struct SelectionError(pub String);
impl fmt::Display for SelectionError {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        out.write_str(&self.0)
    }
}
impl std::error::Error for SelectionError {}

pub fn select_method(
    program: &Program,
    method: DefId,
    arguments: &[GenericArg],
) -> Result<Option<MethodSelection>, SelectionError> {
    let Some((trait_, declaration)) = program.traits.iter().find_map(|trait_| {
        trait_
            .methods
            .iter()
            .find(|found| found.definition == method)
            .map(|found| (trait_, found))
    }) else {
        return Ok(None);
    };
    let Some(GenericArg::Type(target)) = arguments.first() else {
        return Err(error("trait method requires a Self type argument"));
    };
    let count = declaration.inherited_parameters as usize;
    if arguments.len() < count {
        return Err(error("trait method generic arguments are incomplete"));
    }
    let reference = TraitRef {
        definition: trait_.definition,
        arguments: arguments[1..count].to_vec(),
    };
    if let Some(selected) = closure_selection(program, *target, &reference) {
        return Ok(Some(selected));
    }
    let Some((index, mut inferred)) = select_trait(program, *target, &reference)? else {
        return Ok(None);
    };
    let implementation = &program.implementations[index];
    let Some(target) = implementation
        .methods
        .iter()
        .find(|target| target.declaration == Some(method))
    else {
        return Err(error("implementation has no required method"));
    };
    if target.implementation == method && declaration.has_default {
        return Ok(Some(MethodSelection {
            definition: method,
            type_arguments: arguments.to_vec(),
        }));
    }
    inferred.extend_from_slice(&arguments[count..]);
    Ok(Some(MethodSelection {
        definition: target.implementation,
        type_arguments: inferred,
    }))
}

pub fn select_drop(program: &Program, ty: TyId) -> Result<Option<MethodSelection>, SelectionError> {
    let Some(trait_) = program
        .traits
        .iter()
        .find(|trait_| trait_.language_item == Some(LanguageItem::Drop))
    else {
        return Ok(None);
    };
    let Some(method) = trait_.methods.first() else {
        return Err(error("Drop trait has no destructor method"));
    };
    select_method(program, method.definition, &[GenericArg::Type(ty)])
}

/// Returns an implementation witness and its inferred arguments. Its bounds
/// remain obligations: callers must run `check_bounds` before using the witness.
pub fn select_trait(
    program: &Program,
    target: TyId,
    reference: &TraitRef,
) -> Result<Option<(usize, Vec<GenericArg>)>, SelectionError> {
    let mut selected = None;
    for (index, implementation) in program.implementations.iter().enumerate() {
        if implementation.negative {
            continue;
        }
        let Some(found) = &implementation.trait_ref else {
            continue;
        };
        if found.definition != reference.definition
            || found.arguments.len() != reference.arguments.len()
        {
            continue;
        }
        let mut matcher = Matcher::new(program, implementation.definition);
        if !matcher.ty(implementation.target, target, 0)?
            || !matcher.arguments(&found.arguments, &reference.arguments, 0)?
        {
            continue;
        }
        let Some(arguments) = matcher.complete() else {
            return Err(error(
                "implementation arguments cannot be uniquely inferred",
            ));
        };
        if selected.replace((index, arguments)).is_some() {
            return Err(error("more than one trait implementation matches"));
        }
    }
    Ok(selected)
}

pub fn check_bounds(
    program: &mut Program,
    owner: DefId,
    arguments: &[GenericArg],
) -> Result<(), SelectionError> {
    let mut checker = Bounds {
        program,
        active: HashSet::new(),
        remaining: 4096,
    };
    checker.definition(owner, arguments, 0)
}

pub fn require_trait(
    program: &mut Program,
    target: TyId,
    reference: &TraitRef,
) -> Result<(), SelectionError> {
    Bounds {
        program,
        active: HashSet::new(),
        remaining: 4096,
    }
    .obligation(target, reference.clone(), 0)
}

pub(super) fn copy(program: &mut Program, target: TyId) -> bool {
    Bounds {
        program,
        active: HashSet::new(),
        remaining: 4096,
    }
    .copy_type(target, 0)
    .is_ok()
}

pub fn supertraits(
    program: &mut Program,
    reference: &TraitRef,
) -> Result<Vec<TraitRef>, SelectionError> {
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    let mut pending = std::collections::VecDeque::from([(reference.clone(), 0usize)]);
    while let Some((current, depth)) = pending.pop_front() {
        if depth >= 64 || found.len() >= 4096 {
            return Err(error("supertrait expansion exceeds its resource limit"));
        }
        if !seen.insert(current.clone()) {
            continue;
        }
        let trait_ = program
            .traits
            .iter()
            .find(|trait_| trait_.definition == current.definition)
            .ok_or_else(|| error("supertrait reference does not name a trait"))?;
        let parents = trait_.supertraits.clone();
        for mut parent in parents {
            for argument in &mut parent.arguments {
                *argument = program
                    .types
                    .substitute_arg(*argument, current.definition, &current.arguments)
                    .map_err(|problem| error(&problem.to_string()))?;
            }
            pending.push_back((parent, depth + 1));
        }
        found.push(current);
    }
    Ok(found)
}

struct Bounds<'a> {
    program: &'a mut Program,
    active: HashSet<(TyId, TraitRef)>,
    remaining: usize,
}
impl Bounds<'_> {
    fn definition(
        &mut self,
        owner: DefId,
        arguments: &[GenericArg],
        depth: usize,
    ) -> Result<(), SelectionError> {
        self.charge(depth)?;
        let bounds = self.program.definitions[owner].bounds.clone();
        for bound in bounds {
            let Some(GenericArg::Type(target)) = arguments.get(bound.parameter as usize) else {
                return Err(error("trait bound requires a type argument"));
            };
            let mut required = bound.trait_ref;
            for argument in &mut required.arguments {
                *argument = self
                    .program
                    .types
                    .substitute_arg(*argument, owner, arguments)
                    .map_err(|problem| error(&problem.to_string()))?;
            }
            self.obligation(*target, required, depth + 1)?;
        }
        Ok(())
    }
    fn obligation(
        &mut self,
        target: TyId,
        required: TraitRef,
        depth: usize,
    ) -> Result<(), SelectionError> {
        self.charge(depth)?;
        if let Ty::Parameter { owner, index } = *self.program.types.get(target) {
            let bounds = self.program.definitions[owner].bounds.clone();
            for bound in bounds {
                if bound.parameter == index
                    && supertraits(self.program, &bound.trait_ref)?.contains(&required)
                {
                    return Ok(());
                }
            }
        }
        if self.program.traits.iter().any(|trait_| {
            trait_.definition == required.definition
                && trait_.language_item == Some(LanguageItem::Copy)
        }) {
            return self.copy_type(target, depth + 1);
        }
        if validate_closure_trait(self.program, target, &required)? {
            return self.parents(target, &required, depth + 1);
        }
        let property = self
            .program
            .traits
            .iter()
            .find(|trait_| trait_.definition == required.definition)
            .and_then(|trait_| trait_.language_item)
            .and_then(crate::tasks::transfer::Property::from_role);
        if let Some(property) = property {
            let properties = crate::local::properties::Structural::compute(self.program);
            crate::tasks::transfer::check_structural(self.program, &properties, target, property)
                .map_err(|message| error(&message.to_string()))?;
            return self.parents(target, &required, depth + 1);
        }
        self.implementation(target, required, depth)
    }

    fn copy_type(&mut self, target: TyId, depth: usize) -> Result<(), SelectionError> {
        self.charge(depth)?;
        match self.program.types.get(target).clone() {
            Ty::Void
            | Ty::Bool
            | Ty::Char
            | Ty::Integer { .. }
            | Ty::Float { .. }
            | Ty::Pointer { .. }
            | Ty::Function { .. }
            | Ty::ForAll { .. }
            | Ty::Reference { mutable: false, .. } => Ok(()),
            Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } => {
                self.copy_type(inner, depth + 1)
            }
            Ty::Parameter { owner, index }
                if parameter_has_role(self.program, owner, index, LanguageItem::Copy) =>
            {
                Ok(())
            }
            Ty::Named { .. } => {
                if crate::tasks::task_arguments(self.program, target).is_some()
                    || has_drop(self.program, target)
                {
                    return Err(error(
                        "owning task handles and types with user Drop cannot be Copy",
                    ));
                }
                let definition = self
                    .program
                    .traits
                    .iter()
                    .find(|item| item.language_item == Some(LanguageItem::Copy))
                    .map(|item| item.definition)
                    .ok_or_else(|| error("nominal type has no Copy declaration"))?;
                self.implementation(
                    target,
                    TraitRef {
                        definition,
                        arguments: Vec::new(),
                    },
                    depth + 1,
                )
            }
            _ => Err(error("type has no permission to copy its value")),
        }
    }

    fn implementation(
        &mut self,
        target: TyId,
        required: TraitRef,
        depth: usize,
    ) -> Result<(), SelectionError> {
        self.charge(depth)?;
        let key = (target, required.clone());
        if !self.active.insert(key.clone()) {
            return Err(error(
                "trait obligation cycle has no established implementation",
            ));
        }
        let Some((index, arguments)) = select_trait(self.program, target, &required)? else {
            return Err(error("required trait implementation is not established"));
        };
        let owner = self.program.implementations[index].definition;
        let result = self
            .definition(owner, &arguments, depth + 1)
            .and_then(|()| {
                for parent in supertraits(self.program, &required)?.into_iter().skip(1) {
                    self.obligation(target, parent, depth + 1)?;
                }
                Ok(())
            });
        self.active.remove(&key);
        result
    }
    fn charge(&mut self, depth: usize) -> Result<(), SelectionError> {
        if depth >= 64 || self.remaining == 0 {
            return Err(error("trait selection exceeds its resource limit"));
        }
        self.remaining -= 1;
        Ok(())
    }

    fn parents(
        &mut self,
        target: TyId,
        reference: &TraitRef,
        depth: usize,
    ) -> Result<(), SelectionError> {
        for parent in supertraits(self.program, reference)?.into_iter().skip(1) {
            self.obligation(target, parent, depth + 1)?;
        }
        Ok(())
    }
}

pub(crate) struct Matcher<'a> {
    program: &'a Program,
    owner: DefId,
    inferred: Vec<Option<GenericArg>>,
    remaining: usize,
}
impl<'a> Matcher<'a> {
    pub(crate) fn new(program: &'a Program, owner: DefId) -> Self {
        Self {
            program,
            owner,
            inferred: vec![None; program.definitions[owner].generic_parameter_kinds.len()],
            remaining: 4096,
        }
    }
    pub(crate) fn complete(self) -> Option<Vec<GenericArg>> {
        self.inferred.into_iter().collect()
    }
    pub(crate) fn with_arguments(
        program: &'a Program,
        owner: DefId,
        arguments: &[GenericArg],
    ) -> Self {
        Self {
            program,
            owner,
            inferred: arguments.iter().copied().map(Some).collect(),
            remaining: 4096,
        }
    }
    fn bind(&mut self, index: u32, argument: GenericArg) -> bool {
        let Some(slot) = self.inferred.get_mut(index as usize) else {
            return false;
        };
        match slot {
            Some(old) => *old == argument,
            None => {
                *slot = Some(argument);
                true
            }
        }
    }
    pub(crate) fn arguments(
        &mut self,
        pattern: &[GenericArg],
        actual: &[GenericArg],
        depth: usize,
    ) -> Result<bool, SelectionError> {
        if pattern.len() != actual.len() {
            return Ok(false);
        }
        for (&pattern, &actual) in pattern.iter().zip(actual) {
            let matches = match (pattern, actual) {
                (GenericArg::Type(pattern), GenericArg::Type(actual)) => {
                    self.ty(pattern, actual, depth + 1)?
                }
                (GenericArg::Const(pattern), GenericArg::Const(actual)) => {
                    self.constant(pattern, actual)
                }
                (GenericArg::Lifetime(pattern), GenericArg::Lifetime(actual)) => {
                    self.region(pattern, actual)
                }
                _ => false,
            };
            if !matches {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub(crate) fn ty(
        &mut self,
        pattern: TyId,
        actual: TyId,
        depth: usize,
    ) -> Result<bool, SelectionError> {
        if depth >= 128 || self.remaining == 0 {
            return Err(error("implementation matching exceeds its resource limit"));
        }
        self.remaining -= 1;
        if let Ty::Parameter { owner, index } = *self.program.types.get(pattern)
            && owner == self.owner
        {
            return Ok(self.bind(index, GenericArg::Type(actual)));
        }
        if pattern == actual {
            return Ok(true);
        }
        if let Some(matches) = self.arrays(pattern, actual, depth)? {
            return Ok(matches);
        }
        if let Some(matches) = self.functions(pattern, actual, depth)? {
            return Ok(matches);
        }
        let matches = match (
            self.program.types.get(pattern),
            self.program.types.get(actual),
        ) {
            (
                Ty::Named {
                    definition: a,
                    arguments: aa,
                },
                Ty::Named {
                    definition: b,
                    arguments: ba,
                },
            ) => a == b && self.arguments(aa, ba, depth + 1)?,
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
            ) => am == bm && self.region(*a, *b) && self.ty(*ai, *bi, depth + 1)?,
            (
                Ty::Pointer {
                    constant: a,
                    inner: ai,
                },
                Ty::Pointer {
                    constant: b,
                    inner: bi,
                },
            ) => a == b && self.ty(*ai, *bi, depth + 1)?,
            (Ty::Slice(a), Ty::Slice(b)) => self.ty(*a, *b, depth + 1)?,
            _ => false,
        };
        Ok(matches)
    }
    fn functions(
        &mut self,
        pattern: TyId,
        actual: TyId,
        depth: usize,
    ) -> Result<Option<bool>, SelectionError> {
        let matches = match (
            self.program.types.get(pattern),
            self.program.types.get(actual),
        ) {
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
                if ap.len() != bp.len() {
                    return Ok(Some(false));
                }
                for (&a, &b) in ap.iter().zip(bp) {
                    if !self.ty(a, b, depth + 1)? {
                        return Ok(Some(false));
                    }
                }
                self.ty(*ar, *br, depth + 1)?
            }
            (
                Ty::ForAll {
                    parameters: ap,
                    inner: a,
                },
                Ty::ForAll {
                    parameters: bp,
                    inner: b,
                },
            ) => ap == bp && self.ty(*a, *b, depth + 1)?,
            _ => return Ok(None),
        };
        Ok(Some(matches))
    }
    fn arrays(
        &mut self,
        pattern: TyId,
        actual: TyId,
        depth: usize,
    ) -> Result<Option<bool>, SelectionError> {
        let matches = match (
            self.program.types.get(pattern),
            self.program.types.get(actual),
        ) {
            (
                Ty::Array {
                    inner: a,
                    length: al,
                },
                Ty::Array {
                    inner: b,
                    length: bl,
                },
            ) => al == bl && self.ty(*a, *b, depth + 1)?,
            (
                Ty::SymbolicArray {
                    inner: a,
                    length: al,
                },
                Ty::SymbolicArray {
                    inner: b,
                    length: bl,
                },
            ) => self.constant(*al, *bl) && self.ty(*a, *b, depth + 1)?,
            (
                Ty::SymbolicArray { inner: a, length },
                Ty::Array {
                    inner: b,
                    length: actual_length,
                },
            ) => self.array_constant(*length, *actual_length) && self.ty(*a, *b, depth + 1)?,
            _ => return Ok(None),
        };
        Ok(Some(matches))
    }
    fn constant(&mut self, pattern: ConstId, actual: ConstId) -> bool {
        match self.program.types.const_term(pattern).kind {
            ConstKind::Parameter { owner, index } if owner == self.owner => {
                self.bind(index, GenericArg::Const(actual))
            }
            _ => pattern == actual,
        }
    }
    fn array_constant(&mut self, pattern: ConstId, actual: u64) -> bool {
        if let Some(value) = self.program.types.const_usize(pattern) {
            return value == actual;
        }
        let value = self.program.types.constant_terms().iter().position(|term| matches!(term.kind, ConstKind::Value(crate::types::ConstValue::Usize(value)) if value == actual));
        value.is_some_and(|index| self.constant(pattern, ConstId(index as u32)))
    }
    fn region(&mut self, pattern: Region, actual: Region) -> bool {
        if let Region::Named { owner, name } = pattern
            && owner == self.owner
            && let Some(index) = self
                .program
                .types
                .generic_parameters(owner)
                .iter()
                .position(|(candidate, _)| *candidate == name)
        {
            return self.bind(index as u32, GenericArg::Lifetime(actual));
        }
        matches!(pattern, Region::Infer(_)) || pattern == actual
    }
}

fn error(message: &str) -> SelectionError {
    SelectionError(message.into())
}
