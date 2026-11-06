use super::{DefId, GenericArg, GenericParamKind, Region, Symbol, Ty, TyId, TypeContext};
use crate::syntax::ast::{BinaryOp, UnaryOp};
use std::{collections::HashMap, fmt};

const LIMIT: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstValue {
    Usize(u64),
    Bool(bool),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstTerm {
    pub ty: TyId,
    pub kind: ConstKind,
}
impl ConstTerm {
    pub fn visit_arguments(&self, mut visit: impl FnMut(GenericArg)) {
        visit(GenericArg::Type(self.ty));
        match &self.kind {
            ConstKind::Unary { operand, .. } => visit(GenericArg::Const(*operand)),
            ConstKind::Binary { left, right, .. } => {
                visit(GenericArg::Const(*left));
                visit(GenericArg::Const(*right));
            }
            ConstKind::Call {
                type_arguments,
                arguments,
                ..
            } => {
                for &argument in type_arguments {
                    visit(argument);
                }
                for &argument in arguments {
                    visit(GenericArg::Const(argument));
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstKind {
    Value(ConstValue),
    Global(DefId),
    Parameter {
        owner: DefId,
        index: u32,
    },
    Unary {
        op: UnaryOp,
        operand: ConstId,
    },
    Binary {
        op: BinaryOp,
        left: ConstId,
        right: ConstId,
    },
    Call {
        definition: DefId,
        type_arguments: Vec<GenericArg>,
        arguments: Vec<ConstId>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstError {
    Limit,
    InvalidId,
    Kind,
    Overflow,
    DivideByZero,
    Shift,
    Unresolved,
}
impl fmt::Display for ConstError {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        out.write_str(match self {
            Self::Limit => "constant substitution exceeds its resource limit",
            Self::InvalidId => "constant expression contains an invalid ID",
            Self::Kind => "generic argument or constant expression has the wrong kind",
            Self::Overflow => "constant usize arithmetic overflows the target range",
            Self::DivideByZero => "constant arithmetic divides by zero",
            Self::Shift => "constant shift amount is outside the target integer width",
            Self::Unresolved => "constant value remains dependent on generic arguments",
        })
    }
}
impl std::error::Error for ConstError {}

#[derive(Clone, Debug, Default)]
pub(super) struct Constants {
    values: Vec<ConstTerm>,
    indices: HashMap<ConstTerm, ConstId>,
    bound: Vec<bool>,
    depths: Vec<u16>,
}
impl Constants {
    fn intern(&mut self, value: ConstTerm, bound: bool, depth: u16) -> ConstId {
        if let Some(&id) = self.indices.get(&value) {
            return id;
        }
        let id = ConstId(
            self.values
                .len()
                .try_into()
                .expect("constant table exhausted"),
        );
        self.values.push(value.clone());
        self.bound.push(bound);
        self.depths.push(depth);
        self.indices.insert(value, id);
        id
    }
}

impl TypeContext {
    pub fn const_term(&self, id: ConstId) -> &ConstTerm {
        &self.constants.values[id.0 as usize]
    }
    pub fn constant_terms(&self) -> &[ConstTerm] {
        &self.constants.values
    }
    pub fn intern_const(&mut self, term: ConstTerm) -> Result<ConstId, ConstError> {
        self.validate_const(&term)?;
        let mut bound = false;
        let mut depth = 0;
        term.visit_arguments(|argument| {
            bound |= self.argument_has_bound(argument);
            depth = depth.max(self.argument_depth(argument));
        });
        Ok(self.constants.intern(term, bound, depth.saturating_add(1)))
    }
    pub fn const_value(&mut self, value: u64) -> ConstId {
        let ty = self.builtin("usize").expect("usize type");
        self.constants.intern(
            ConstTerm {
                ty,
                kind: ConstKind::Value(ConstValue::Usize(value)),
            },
            false,
            2,
        )
    }
    pub fn const_bool(&mut self, value: bool) -> ConstId {
        self.constants.intern(
            ConstTerm {
                ty: TyId::BOOL,
                kind: ConstKind::Value(ConstValue::Bool(value)),
            },
            false,
            2,
        )
    }
    pub fn const_parameter(&mut self, owner: DefId, index: u32) -> ConstId {
        let ty = self.builtin("usize").expect("usize type");
        self.constants.intern(
            ConstTerm {
                ty,
                kind: ConstKind::Parameter { owner, index },
            },
            false,
            2,
        )
    }
    pub fn register_generic_parameters(
        &mut self,
        owner: DefId,
        parameters: &[(Symbol, GenericParamKind)],
    ) {
        self.generic_parameters.insert(owner, parameters.to_vec());
    }
    pub fn generic_parameters(&self, owner: DefId) -> &[(Symbol, GenericParamKind)] {
        self.generic_parameters
            .get(&owner)
            .map_or(&[], Vec::as_slice)
    }
    pub fn generic_arguments(&mut self, owner: DefId) -> Vec<GenericArg> {
        let parameters = self.generic_parameters(owner).to_vec();
        parameters
            .into_iter()
            .enumerate()
            .map(|(index, (name, kind))| match kind {
                GenericParamKind::Type => GenericArg::Type(self.intern(Ty::Parameter {
                    owner,
                    index: index as u32,
                })),
                GenericParamKind::Const => {
                    GenericArg::Const(self.const_parameter(owner, index as u32))
                }
                GenericParamKind::Lifetime => GenericArg::Lifetime(Region::Named { owner, name }),
            })
            .collect()
    }
    pub fn const_usize(&self, id: ConstId) -> Option<u64> {
        match self.constant_terms().get(id.0 as usize)?.kind {
            ConstKind::Value(ConstValue::Usize(value)) => Some(value),
            _ => None,
        }
    }
    pub fn array_type(&mut self, inner: TyId, length: ConstId) -> Result<TyId, ConstError> {
        let length = self.normalize_const(length)?;
        if !matches!(
            self.get(self.const_term(length).ty),
            Ty::Integer {
                signed: false,
                bits: 0
            }
        ) {
            return Err(ConstError::Kind);
        }
        Ok(self.intern(match self.const_usize(length) {
            Some(length) => Ty::Array { inner, length },
            None => Ty::SymbolicArray { inner, length },
        }))
    }
    fn validate_const(&self, term: &ConstTerm) -> Result<(), ConstError> {
        let ty = self
            .values()
            .get(term.ty.0 as usize)
            .ok_or(ConstError::InvalidId)?;
        let usize_type = matches!(
            ty,
            Ty::Integer {
                signed: false,
                bits: 0
            }
        );
        match &term.kind {
            ConstKind::Value(ConstValue::Usize(_)) | ConstKind::Parameter { .. } if usize_type => {
                Ok(())
            }
            ConstKind::Value(ConstValue::Bool(_)) if term.ty == TyId::BOOL => Ok(()),
            ConstKind::Unary { op, operand } => {
                let input = self
                    .constant_terms()
                    .get(operand.0 as usize)
                    .ok_or(ConstError::InvalidId)?;
                let valid = match op {
                    UnaryOp::Not => term.ty == TyId::BOOL,
                    UnaryOp::Negate | UnaryOp::Positive | UnaryOp::BitNot => usize_type,
                    _ => false,
                };
                if valid && input.ty == term.ty {
                    Ok(())
                } else {
                    Err(ConstError::Kind)
                }
            }
            ConstKind::Binary { op, left, right } => {
                self.validate_binary(*op, *left, *right, term.ty)
            }
            ConstKind::Global(_) if usize_type || term.ty == TyId::BOOL => Ok(()),
            ConstKind::Call {
                arguments,
                type_arguments,
                ..
            } => {
                for id in arguments {
                    self.constant_terms()
                        .get(id.0 as usize)
                        .ok_or(ConstError::InvalidId)?;
                }
                for argument in type_arguments {
                    self.validate_generic_arg(*argument)?;
                }
                if usize_type || term.ty == TyId::BOOL {
                    Ok(())
                } else {
                    Err(ConstError::Kind)
                }
            }
            _ => Err(ConstError::Kind),
        }
    }
    pub fn validate_generic_arg(&self, argument: GenericArg) -> Result<(), ConstError> {
        match argument {
            GenericArg::Type(ty) => self
                .values()
                .get(ty.0 as usize)
                .map(|_| ())
                .ok_or(ConstError::InvalidId),
            GenericArg::Const(id) => self
                .constant_terms()
                .get(id.0 as usize)
                .map(|_| ())
                .ok_or(ConstError::InvalidId),
            GenericArg::Lifetime(_) => Ok(()),
        }
    }
    fn validate_binary(
        &self,
        op: BinaryOp,
        left: ConstId,
        right: ConstId,
        output: TyId,
    ) -> Result<(), ConstError> {
        let left = self
            .constant_terms()
            .get(left.0 as usize)
            .ok_or(ConstError::InvalidId)?;
        let right = self
            .constant_terms()
            .get(right.0 as usize)
            .ok_or(ConstError::InvalidId)?;
        if left.ty != right.ty {
            return Err(ConstError::Kind);
        }
        let valid = match op {
            BinaryOp::And | BinaryOp::Or => left.ty == TyId::BOOL && output == TyId::BOOL,
            BinaryOp::Equal | BinaryOp::NotEqual => output == TyId::BOOL,
            BinaryOp::Less | BinaryOp::LessEqual | BinaryOp::Greater | BinaryOp::GreaterEqual => {
                self.integer(left.ty) && output == TyId::BOOL
            }
            _ => self.integer(left.ty) && output == left.ty,
        };
        if valid { Ok(()) } else { Err(ConstError::Kind) }
    }
    pub fn normalize_const(&mut self, id: ConstId) -> Result<ConstId, ConstError> {
        Normalizer {
            types: self,
            memo: HashMap::new(),
            remaining: LIMIT,
        }
        .visit(id, 0)
    }
    pub fn const_substitute(
        &mut self,
        id: ConstId,
        owner: DefId,
        arguments: &[GenericArg],
    ) -> Result<ConstId, ConstError> {
        self.const_substitute_binders(id, owner, arguments, 0)
    }
    pub(super) fn const_substitute_binders(
        &mut self,
        id: ConstId,
        owner: DefId,
        arguments: &[GenericArg],
        binders: u16,
    ) -> Result<ConstId, ConstError> {
        let mut instantiation = Instantiation::new(self, owner, arguments);
        instantiation.binders = binders;
        let id = instantiation.constant(id, 0)?;
        self.normalize_const(id)
    }
    pub fn substitute_generics(
        &mut self,
        ty: TyId,
        owner: DefId,
        arguments: &[GenericArg],
    ) -> Result<TyId, ConstError> {
        Instantiation::new(self, owner, arguments).ty(ty, 0)
    }
    pub fn substitute_arg(
        &mut self,
        arg: GenericArg,
        owner: DefId,
        arguments: &[GenericArg],
    ) -> Result<GenericArg, ConstError> {
        Instantiation::new(self, owner, arguments).argument(arg, 0)
    }
    pub fn display_const(&self, id: ConstId) -> String {
        match &self.const_term(id).kind {
            ConstKind::Value(ConstValue::Usize(value)) => value.to_string(),
            ConstKind::Value(ConstValue::Bool(value)) => value.to_string(),
            ConstKind::Parameter { index, .. } => format!("N{index}"),
            _ => format!("const#{}", id.0),
        }
    }
    pub(super) fn argument_has_bound(&self, argument: GenericArg) -> bool {
        match argument {
            GenericArg::Type(ty) => self
                .bound_regions
                .get(ty.0 as usize)
                .copied()
                .unwrap_or(true),
            GenericArg::Const(id) => self
                .constants
                .bound
                .get(id.0 as usize)
                .copied()
                .unwrap_or(true),
            GenericArg::Lifetime(region) => matches!(region, Region::Bound { .. }),
        }
    }
    pub(super) fn argument_depth(&self, argument: GenericArg) -> u16 {
        match argument {
            GenericArg::Type(ty) => self.depths.get(ty.0 as usize).copied().unwrap_or(u16::MAX),
            GenericArg::Const(id) => self
                .constants
                .depths
                .get(id.0 as usize)
                .copied()
                .unwrap_or(u16::MAX),
            GenericArg::Lifetime(_) => 1,
        }
    }
    pub fn generic_arguments_concrete(&self, arguments: &[GenericArg]) -> Result<bool, ConstError> {
        let mut pending = arguments.to_vec();
        let mut seen = std::collections::HashSet::new();
        let mut remaining = LIMIT;
        while let Some(argument) = pending.pop() {
            charge(&mut remaining, 0)?;
            if !seen.insert(argument) {
                continue;
            }
            match argument {
                GenericArg::Lifetime(_) => {}
                GenericArg::Type(ty) => match self
                    .values()
                    .get(ty.0 as usize)
                    .ok_or(ConstError::InvalidId)?
                {
                    Ty::Parameter { .. } => return Ok(false),
                    Ty::Named { arguments, .. } | Ty::Dynamic { arguments, .. } => {
                        pending.extend(arguments)
                    }
                    Ty::Reference { inner, .. }
                    | Ty::Pointer { inner, .. }
                    | Ty::Array { inner, .. }
                    | Ty::Slice(inner)
                    | Ty::ForAll { inner, .. } => pending.push(GenericArg::Type(*inner)),
                    Ty::SymbolicArray { inner, length } => {
                        pending.push(GenericArg::Type(*inner));
                        pending.push(GenericArg::Const(*length));
                    }
                    Ty::Function { parameters, result } => {
                        pending.extend(parameters.iter().copied().map(GenericArg::Type));
                        pending.push(GenericArg::Type(*result));
                    }
                    _ => {}
                },
                GenericArg::Const(id) => match &self
                    .constant_terms()
                    .get(id.0 as usize)
                    .ok_or(ConstError::InvalidId)?
                    .kind
                {
                    ConstKind::Parameter { .. } => return Ok(false),
                    ConstKind::Unary { operand, .. } => pending.push(GenericArg::Const(*operand)),
                    ConstKind::Binary { left, right, .. } => {
                        pending.push(GenericArg::Const(*left));
                        pending.push(GenericArg::Const(*right));
                    }
                    ConstKind::Call {
                        type_arguments,
                        arguments,
                        ..
                    } => {
                        pending.extend(type_arguments);
                        pending.extend(arguments.iter().copied().map(GenericArg::Const));
                    }
                    _ => {}
                },
            }
        }
        Ok(true)
    }
}

struct Normalizer<'a> {
    types: &'a mut TypeContext,
    memo: HashMap<ConstId, ConstId>,
    remaining: usize,
}
impl Normalizer<'_> {
    fn visit(&mut self, id: ConstId, depth: usize) -> Result<ConstId, ConstError> {
        charge(&mut self.remaining, depth)?;
        if let Some(&value) = self.memo.get(&id) {
            return Ok(value);
        }
        let term = self
            .types
            .constant_terms()
            .get(id.0 as usize)
            .cloned()
            .ok_or(ConstError::InvalidId)?;
        let kind = match term.kind {
            ConstKind::Unary { op, operand } => {
                let operand = self.visit(operand, depth + 1)?;
                match self.value(operand) {
                    Some(value) => ConstKind::Value(unary(op, value)?),
                    None => ConstKind::Unary { op, operand },
                }
            }
            ConstKind::Binary { op, left, right } => self.binary(op, left, right, depth + 1)?,
            // Calls require the separately verified typed CTFE body/effect query.
            other => other,
        };
        let result = self.types.intern_const(ConstTerm { ty: term.ty, kind })?;
        self.memo.insert(id, result);
        Ok(result)
    }
    fn value(&self, id: ConstId) -> Option<ConstValue> {
        match self.types.const_term(id).kind {
            ConstKind::Value(value) => Some(value),
            _ => None,
        }
    }
    fn binary(
        &mut self,
        op: BinaryOp,
        left: ConstId,
        right: ConstId,
        depth: usize,
    ) -> Result<ConstKind, ConstError> {
        let left = self.visit(left, depth)?;
        // Evaluation, unlike substitution, may not visit the unselected operand.
        match (op, self.value(left)) {
            (BinaryOp::And, Some(ConstValue::Bool(false))) => {
                return Ok(ConstKind::Value(ConstValue::Bool(false)));
            }
            (BinaryOp::Or, Some(ConstValue::Bool(true))) => {
                return Ok(ConstKind::Value(ConstValue::Bool(true)));
            }
            _ => {}
        }
        let right = self.visit(right, depth)?;
        Ok(match (self.value(left), self.value(right)) {
            (Some(left), Some(right)) => ConstKind::Value(binary(op, left, right)?),
            _ => ConstKind::Binary { op, left, right },
        })
    }
}

fn unary(op: UnaryOp, value: ConstValue) -> Result<ConstValue, ConstError> {
    Ok(match (op, value) {
        (UnaryOp::Positive, value @ ConstValue::Usize(_)) => value,
        (UnaryOp::Negate, ConstValue::Usize(value)) => {
            ConstValue::Usize(0u64.checked_sub(value).ok_or(ConstError::Overflow)?)
        }
        (UnaryOp::BitNot, ConstValue::Usize(value)) => ConstValue::Usize(!value),
        (UnaryOp::Not, ConstValue::Bool(value)) => ConstValue::Bool(!value),
        _ => return Err(ConstError::Kind),
    })
}
fn binary(op: BinaryOp, left: ConstValue, right: ConstValue) -> Result<ConstValue, ConstError> {
    if let (ConstValue::Bool(a), ConstValue::Bool(b)) = (left, right) {
        return Ok(ConstValue::Bool(match op {
            BinaryOp::And => a && b,
            BinaryOp::Or => a || b,
            BinaryOp::Equal => a == b,
            BinaryOp::NotEqual => a != b,
            _ => return Err(ConstError::Kind),
        }));
    }
    let (ConstValue::Usize(a), ConstValue::Usize(b)) = (left, right) else {
        return Err(ConstError::Kind);
    };
    if let Some(value) = comparison(op, a, b) {
        return Ok(ConstValue::Bool(value));
    }
    let value = match op {
        BinaryOp::Add => a.checked_add(b),
        BinaryOp::Subtract => a.checked_sub(b),
        BinaryOp::Multiply => a.checked_mul(b),
        BinaryOp::Divide | BinaryOp::Remainder if b == 0 => return Err(ConstError::DivideByZero),
        BinaryOp::Divide => Some(a / b),
        BinaryOp::Remainder => Some(a % b),
        BinaryOp::ShiftLeft | BinaryOp::ShiftRight if b >= 64 => return Err(ConstError::Shift),
        BinaryOp::ShiftLeft => Some(a << b),
        BinaryOp::ShiftRight => Some(a >> b),
        BinaryOp::BitAnd => Some(a & b),
        BinaryOp::BitOr => Some(a | b),
        BinaryOp::BitXor => Some(a ^ b),
        _ => return Err(ConstError::Kind),
    }
    .ok_or(ConstError::Overflow)?;
    Ok(ConstValue::Usize(value))
}
fn comparison(op: BinaryOp, a: u64, b: u64) -> Option<bool> {
    Some(match op {
        BinaryOp::Equal => a == b,
        BinaryOp::NotEqual => a != b,
        BinaryOp::Less => a < b,
        BinaryOp::LessEqual => a <= b,
        BinaryOp::Greater => a > b,
        BinaryOp::GreaterEqual => a >= b,
        _ => return None,
    })
}
fn charge(remaining: &mut usize, depth: usize) -> Result<(), ConstError> {
    if depth >= 128 {
        return Err(ConstError::Limit);
    }
    *remaining = remaining.checked_sub(1).ok_or(ConstError::Limit)?;
    Ok(())
}

struct Instantiation<'a> {
    types: &'a mut TypeContext,
    owner: DefId,
    arguments: &'a [GenericArg],
    types_memo: HashMap<(TyId, u16), TyId>,
    const_memo: HashMap<(ConstId, u16), ConstId>,
    remaining: usize,
    binders: u16,
}
impl<'a> Instantiation<'a> {
    fn new(types: &'a mut TypeContext, owner: DefId, arguments: &'a [GenericArg]) -> Self {
        Self {
            types,
            owner,
            arguments,
            types_memo: HashMap::new(),
            const_memo: HashMap::new(),
            remaining: LIMIT,
            binders: 0,
        }
    }
    fn argument(&mut self, arg: GenericArg, depth: usize) -> Result<GenericArg, ConstError> {
        Ok(match arg {
            GenericArg::Type(ty) => GenericArg::Type(self.ty(ty, depth)?),
            GenericArg::Const(id) => GenericArg::Const(self.constant(id, depth)?),
            GenericArg::Lifetime(region) => GenericArg::Lifetime(self.region(region)?),
        })
    }
    fn region(&self, region: Region) -> Result<Region, ConstError> {
        let Region::Named { owner, name } = region else {
            return Ok(region);
        };
        if owner != self.owner {
            return Ok(region);
        }
        let Some(index) = self
            .types
            .generic_parameters(owner)
            .iter()
            .position(|&(symbol, kind)| symbol == name && kind == GenericParamKind::Lifetime)
        else {
            return Ok(region);
        };
        match self.arguments.get(index) {
            Some(GenericArg::Lifetime(Region::Bound { depth, index })) => Ok(Region::Bound {
                depth: depth.checked_add(self.binders).ok_or(ConstError::Limit)?,
                index: *index,
            }),
            Some(GenericArg::Lifetime(value)) => Ok(*value),
            _ => Err(ConstError::Kind),
        }
    }
    fn ty(&mut self, ty: TyId, depth: usize) -> Result<TyId, ConstError> {
        charge(&mut self.remaining, depth)?;
        if let Some(&value) = self.types_memo.get(&(ty, self.binders)) {
            return Ok(value);
        }
        let value = self
            .types
            .values()
            .get(ty.0 as usize)
            .cloned()
            .ok_or(ConstError::InvalidId)?;
        if let Ty::Parameter { owner, index } = value
            && owner == self.owner
        {
            let argument = self
                .arguments
                .get(index as usize)
                .and_then(|arg| arg.ty())
                .ok_or(ConstError::Kind)?;
            return self
                .types
                .shift_bound_regions(argument, self.binders)
                .ok_or(ConstError::Limit);
        }
        let value = self.type_children(value, depth + 1)?;
        let result = self.types.intern(value);
        self.types_memo.insert((ty, self.binders), result);
        Ok(result)
    }
    fn type_children(&mut self, value: Ty, depth: usize) -> Result<Ty, ConstError> {
        Ok(match value {
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
            Ty::Reference {
                region,
                mutable,
                inner,
            } => Ty::Reference {
                region: self.region(region)?,
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
                let length = self.constant(length, depth)?;
                let length = self.types.normalize_const(length)?;
                match self.types.const_usize(length) {
                    Some(length) => Ty::Array { inner, length },
                    None => Ty::SymbolicArray { inner, length },
                }
            }
            Ty::Slice(inner) => Ty::Slice(self.ty(inner, depth)?),
            Ty::ForAll { parameters, inner } => {
                self.binders = self.binders.checked_add(1).ok_or(ConstError::Limit)?;
                let inner = self.ty(inner, depth);
                self.binders -= 1;
                Ty::ForAll {
                    parameters,
                    inner: inner?,
                }
            }
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
        values: Vec<GenericArg>,
        depth: usize,
    ) -> Result<Vec<GenericArg>, ConstError> {
        values
            .into_iter()
            .map(|arg| self.argument(arg, depth))
            .collect()
    }
    fn constant(&mut self, id: ConstId, depth: usize) -> Result<ConstId, ConstError> {
        charge(&mut self.remaining, depth)?;
        if let Some(&value) = self.const_memo.get(&(id, self.binders)) {
            return Ok(value);
        }
        let term = self
            .types
            .constant_terms()
            .get(id.0 as usize)
            .cloned()
            .ok_or(ConstError::InvalidId)?;
        if let ConstKind::Parameter { owner, index } = term.kind
            && owner == self.owner
        {
            return match self.arguments.get(index as usize) {
                Some(GenericArg::Const(value)) => self
                    .types
                    .shift_const_regions(*value, self.binders)
                    .ok_or(ConstError::Limit),
                _ => Err(ConstError::Kind),
            };
        }
        let kind = match term.kind {
            ConstKind::Unary { op, operand } => ConstKind::Unary {
                op,
                operand: self.constant(operand, depth + 1)?,
            },
            ConstKind::Binary { op, left, right } => ConstKind::Binary {
                op,
                left: self.constant(left, depth + 1)?,
                right: self.constant(right, depth + 1)?,
            },
            ConstKind::Call {
                definition,
                type_arguments,
                arguments,
            } => ConstKind::Call {
                definition,
                type_arguments: self.arguments(type_arguments, depth + 1)?,
                arguments: arguments
                    .into_iter()
                    .map(|id| self.constant(id, depth + 1))
                    .collect::<Result<_, _>>()?,
            },
            other => other,
        };
        let result = self.types.intern_const(ConstTerm { ty: term.ty, kind })?;
        self.const_memo.insert((id, self.binders), result);
        Ok(result)
    }
}
