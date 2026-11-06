use super::*;
mod calls;
mod flow;
mod operations;
use crate::{local::properties::Properties, types::Ty};
use std::{collections::HashSet, fmt};

const LIMIT: usize = 200_000;
const STATE_LIMIT: usize = 4_000_000;
// Retained states and transfer/edge work are different resources: even an
// acyclic CFG can copy a state onto several edges without retaining each copy.
const WORK_LIMIT: usize = 32_000_000;

#[derive(Debug, PartialEq, Eq)]
pub struct InvariantError {
    pub message: String,
    pub span: Option<Span>,
    kind: FailureKind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FailureKind {
    Invariant,
    ValueUnavailable,
}
impl InvariantError {
    pub fn new(message: String) -> Self {
        Self {
            message,
            span: None,
            kind: FailureKind::Invariant,
        }
    }
    fn unavailable(message: &str) -> Self {
        Self {
            message: message.into(),
            span: None,
            kind: FailureKind::ValueUnavailable,
        }
    }
    fn at(mut self, span: Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
    fn context(mut self, context: String) -> Self {
        self.message = format!("{context}: {}", self.message);
        self
    }
    pub fn user_code(&self) -> Option<&'static str> {
        (self.kind == FailureKind::ValueUnavailable).then_some("E-MOVE-USE")
    }
}

impl fmt::Display for InvariantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for InvariantError {}

impl Program {
    /// Checks executable structure, storage lifetimes and direct owned move paths.
    /// Indirect pointee initialization, loans, effects and Drop glue remain separate
    /// obligations; passing this verifier is not authorization for native codegen.
    pub fn validate(&self, program: &mut hir::Program) -> Result<(), InvariantError> {
        program
            .validate()
            .map_err(|error| InvariantError::new(format!("invalid HIR: {error}")))?;
        let callable_types = callable_types(program)?;
        let signatures = calls::Signatures::prepare(self, program)?;
        let properties = Properties::compute(program);
        let mut sources = vec![None; program.definitions.len()];
        for function in &program.functions {
            require(
                sources[function.definition.0 as usize]
                    .replace(function)
                    .is_none(),
                "duplicate HIR function body",
            )?;
        }
        let mut definitions = HashSet::new();
        for body in &self.functions {
            require(
                definitions.insert(body.definition),
                "duplicate MIR function",
            )?;
            let verifier = Verifier {
                body,
                program,
                properties: &properties,
                callable_types: &callable_types,
                signatures: &signatures,
                source: sources
                    .get(body.definition.0 as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(|| {
                        InvariantError::new("MIR body has no matching HIR function".into())
                    })?,
            };
            verifier
                .structure()
                .and_then(|()| verifier.flow())
                .map_err(|error| error.context(format!("function #{}", body.definition.0)))?;
        }
        require(
            definitions.len() == program.functions.len(),
            "MIR program is missing a HIR function body",
        )?;
        Ok(())
    }
}

fn callable_types(program: &mut hir::Program) -> Result<Vec<Option<TyId>>, InvariantError> {
    let mut values = Vec::with_capacity(program.definitions.len());
    for (index, definition) in program.definitions.iter().enumerate() {
        let ty = match definition.kind {
            hir::DefinitionKind::Function => {
                // A function value closes declaration lifetimes and applies
                // result elision. Comparing it with the unclosed declaration
                // would reject valid identity functions or lose binder scope.
                Some(
                    program
                        .types
                        .generalize_callable(definition.ty, hir::DefId(index as u32))
                        .ok_or_else(|| {
                            InvariantError::new("MIR callable generalization limit exceeded".into())
                        })?,
                )
            }
            hir::DefinitionKind::Variant { .. } => Some(definition.ty),
            _ => None,
        };
        values.push(ty);
    }
    Ok(values)
}

struct Verifier<'a> {
    body: &'a Body,
    program: &'a hir::Program,
    properties: &'a Properties,
    callable_types: &'a [Option<TyId>],
    signatures: &'a calls::Signatures,
    source: &'a hir::Function,
}

impl Verifier<'_> {
    fn ty(&self, id: TyId) -> Result<&Ty, InvariantError> {
        let ty = self
            .program
            .types
            .values()
            .get(id.0 as usize)
            .filter(|ty| !matches!(ty, Ty::Error))
            .ok_or_else(|| InvariantError::new("invalid MIR type ID".into()))?;
        require(
            self.program.types.nesting(id) <= 128,
            "MIR type depth limit exceeded",
        )?;
        require(
            match ty {
                Ty::Integer { bits, .. } => matches!(bits, 0 | 8 | 16 | 32 | 64 | 128),
                Ty::Float { bits } => matches!(bits, 32 | 64),
                _ => true,
            },
            "invalid numeric MIR type width",
        )?;
        Ok(ty)
    }
    fn local(&self, id: LocalId) -> Result<&Local, InvariantError> {
        self.body
            .locals
            .get(id.0 as usize)
            .ok_or_else(|| InvariantError::new("invalid MIR local ID".into()))
    }
    fn scope(&self, id: ScopeId) -> Result<&Scope, InvariantError> {
        self.body
            .scopes
            .get(id.0 as usize)
            .ok_or_else(|| InvariantError::new("invalid MIR scope ID".into()))
    }
    fn block(&self, id: BlockId) -> Result<&Block, InvariantError> {
        self.body
            .blocks
            .get(id.0 as usize)
            .ok_or_else(|| InvariantError::new("invalid MIR block ID".into()))
    }
    fn compatible(&self, actual: TyId, expected: TyId) -> Result<(), InvariantError> {
        self.ty(actual)?;
        self.ty(expected)?;
        if self.program.types.compatible(actual, expected) {
            return Ok(());
        }
        Err(InvariantError::new(format!(
            "MIR value type mismatch: {:?} versus {:?}",
            self.ty(actual)?,
            self.ty(expected)?
        )))
    }
    fn place(&self, place: &Place) -> Result<TyId, InvariantError> {
        require(
            place.projection.len() <= 128,
            "MIR projection depth limit exceeded",
        )?;
        let local = self.local(place.local)?;
        let mut ty = local.ty;
        let mut variant = None;
        for (index, projection) in place.projection.iter().enumerate() {
            ty = match projection {
                Projection::Deref if index == 0 && local.kind == LocalKind::Address => ty,
                Projection::Deref => match self.ty(ty)? {
                    Ty::Reference { inner, .. } | Ty::Pointer { inner, .. } => *inner,
                    _ => return fail("dereference projection requires a reference or pointer"),
                },
                Projection::Downcast(selected) => {
                    require(
                        variant.is_none(),
                        "nested downcast requires a payload field",
                    )?;
                    self.variant_fields(ty, *selected)?;
                    variant = Some(*selected);
                    ty
                }
                Projection::Field(field) => {
                    let fields = match variant.take() {
                        Some(selected) => self.variant_fields(ty, selected)?,
                        None => self.properties.fields(ty).ok_or_else(|| {
                            InvariantError::new("invalid record field projection".into())
                        })?,
                    };
                    *fields.get(*field as usize).ok_or_else(|| {
                        InvariantError::new("field projection is out of range".into())
                    })?
                }
                Projection::Index(index) => {
                    let index = self.local(*index)?;
                    require(
                        index.kind != LocalKind::Address
                            && matches!(
                                self.ty(index.ty)?,
                                Ty::Integer {
                                    signed: false,
                                    bits: 0
                                }
                            ),
                        "index must have usize value type",
                    )?;
                    match self.ty(ty)? {
                        Ty::Array { inner, .. }
                        | Ty::SymbolicArray { inner, .. }
                        | Ty::Slice(inner) => *inner,
                        _ => return fail("index projection requires an array or slice"),
                    }
                }
            };
        }
        if local.kind == LocalKind::Address {
            require(
                place.projection.first() == Some(&Projection::Deref),
                "internal place handle used as an ordinary value",
            )?;
        }
        require(variant.is_none(), "downcast must select a payload field")?;
        self.ty(ty)?;
        Ok(ty)
    }
    fn operand(&self, operand: &Operand) -> Result<TyId, InvariantError> {
        match operand {
            Operand::Copy(place) => {
                let ty = self.value_place(place)?;
                require(
                    self.properties.get(ty).copy,
                    "Copy operand has a non-Copy type",
                )?;
                Ok(ty)
            }
            Operand::Move(place) => self.value_place(place),
            Operand::ConstTerm { value, ty } => {
                let term = self
                    .program
                    .types
                    .constant_terms()
                    .get(value.0 as usize)
                    .ok_or_else(|| {
                        InvariantError::new("invalid symbolic constant operand".into())
                    })?;
                self.compatible(term.ty, *ty)?;
                Ok(*ty)
            }
            Operand::Unit => Ok(TyId::VOID),
            Operand::Function { definition, ty } => self.function_operand(*definition, *ty),
            Operand::Constant { value, ty } => {
                let kind = self.ty(*ty)?;
                let valid = match value {
                    hir::Constant::Integer {
                        magnitude,
                        negative,
                    } => match kind {
                        Ty::Integer { signed, bits } => {
                            let bits = if *bits == 0 { 64 } else { *bits };
                            if !signed && *negative {
                                false
                            } else if *signed {
                                let bound = 1u128
                                    .checked_shl(u32::from(bits.saturating_sub(1)))
                                    .unwrap_or(0);
                                if *negative {
                                    *magnitude <= bound
                                } else {
                                    *magnitude < bound
                                }
                            } else {
                                bits == 128 || *magnitude < (1u128 << bits)
                            }
                        }
                        _ => false,
                    },
                    hir::Constant::Float(_) => matches!(kind, Ty::Float { .. }),
                    hir::Constant::Bool(_) => matches!(kind, Ty::Bool),
                    hir::Constant::Char(_) => matches!(kind, Ty::Char),
                    hir::Constant::Null => matches!(kind, Ty::Pointer { .. }),
                    hir::Constant::String(_) => {
                        matches!(kind, Ty::Reference { mutable: false, inner, .. } if *inner == TyId::STR)
                    }
                };
                require(valid, "constant does not fit its MIR type")?;
                Ok(*ty)
            }
        }
    }
    fn function_operand(&self, definition: hir::DefId, ty: TyId) -> Result<TyId, InvariantError> {
        let expected = self
            .callable_types
            .get(definition.0 as usize)
            .copied()
            .flatten()
            .ok_or_else(|| {
                InvariantError::new("function operand does not name a callable definition".into())
            })?;
        self.compatible(ty, expected)?;
        require(
            matches!(self.ty(ty)?, Ty::Function { .. } | Ty::ForAll { .. }),
            "function operand has non-callable type",
        )?;
        Ok(ty)
    }
    fn rvalue(&self, value: &Rvalue, expected: TyId) -> Result<(), InvariantError> {
        match value {
            Rvalue::IsVariant { .. } | Rvalue::RepeatConst { .. } | Rvalue::DynCoerce { .. } => {
                self.extended_value(value, expected)
            }
            Rvalue::Use(value) => self.compatible(self.operand(value)?, expected),
            Rvalue::Unary { op, operand } => {
                let ty = self.operand(operand)?;
                self.compatible(ty, expected)?;
                let valid = match op {
                    UnaryOp::Negate | UnaryOp::Positive => self.program.types.numeric(ty),
                    UnaryOp::Not => ty == TyId::BOOL,
                    UnaryOp::BitNot => self.program.types.integer(ty),
                    _ => false,
                };
                require(valid, "invalid MIR unary operation")
            }
            Rvalue::Binary { op, left, right } => {
                let left = self.operand(left)?;
                let right = self.operand(right)?;
                self.compatible(left, right)?;
                let valid = match op {
                    BinaryOp::And | BinaryOp::Or => false,
                    BinaryOp::Equal | BinaryOp::NotEqual => {
                        expected == TyId::BOOL
                            && (self.program.types.numeric(left)
                                || matches!(self.ty(left)?, Ty::Bool | Ty::Char))
                    }
                    BinaryOp::Less
                    | BinaryOp::LessEqual
                    | BinaryOp::Greater
                    | BinaryOp::GreaterEqual => {
                        expected == TyId::BOOL && self.program.types.numeric(left)
                    }
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::ShiftLeft
                    | BinaryOp::ShiftRight
                    | BinaryOp::Remainder => expected == left && self.program.types.integer(left),
                    _ => expected == left && self.program.types.numeric(left),
                };
                require(valid, "invalid MIR binary operation")
            }
            Rvalue::Borrow { mutable, place } => {
                let actual = self.place(place)?;
                match self.ty(expected)? {
                    Ty::Reference {
                        inner,
                        mutable: target,
                        ..
                    } if mutable == target => self.compatible(actual, *inner),
                    _ => fail("borrow has an incompatible reference result type"),
                }
            }
            Rvalue::AddressOf(_) => fail("place capture must initialize an internal address local"),
            Rvalue::Array(values) => match self.ty(expected)? {
                Ty::Array { inner, length } if *length == values.len() as u64 => {
                    for value in values {
                        self.compatible(self.operand(value)?, *inner)?;
                    }
                    Ok(())
                }
                _ => fail("array aggregate has an incompatible type or length"),
            },
            Rvalue::Repeat { value, count } => match self.ty(expected)? {
                Ty::Array { inner, length } if length == count => {
                    let actual = self.operand(value)?;
                    self.compatible(actual, *inner)?;
                    require(
                        *count <= 1 || self.properties.get(actual).copy,
                        "repeated element is not Copy",
                    )
                }
                _ => fail("repeat aggregate has an incompatible type or length"),
            },
            Rvalue::Record { definition, fields } => {
                require(
                    matches!(self.ty(expected)?, Ty::Named { definition: actual, .. } if actual == definition),
                    "record aggregate has a different nominal type",
                )?;
                let expected_fields = self
                    .properties
                    .fields(expected)
                    .ok_or_else(|| InvariantError::new("aggregate is not a record".into()))?;
                require(
                    fields.len() == expected_fields.len(),
                    "record aggregate is incomplete",
                )?;
                let mut seen = HashSet::new();
                for (index, value) in fields {
                    let expected = expected_fields.get(*index as usize).ok_or_else(|| {
                        InvariantError::new("aggregate field index is out of range".into())
                    })?;
                    require(seen.insert(*index), "duplicate record aggregate field")?;
                    self.compatible(self.operand(value)?, *expected)?;
                }
                Ok(())
            }
            Rvalue::Variant { definition, fields } => {
                let parameters = self
                    .properties
                    .variant_fields(expected, *definition)
                    .ok_or_else(|| {
                        InvariantError::new(
                            "variant does not belong to the destination enum".into(),
                        )
                    })?;
                require(
                    fields.len() == parameters.len(),
                    "variant payload count mismatch",
                )?;
                for (value, &parameter) in fields.iter().zip(parameters) {
                    self.compatible(self.operand(value)?, parameter)?;
                }
                Ok(())
            }
            Rvalue::ArrayToSlice(value) => {
                let actual = self.operand(value)?;
                match (self.ty(actual)?, self.ty(expected)?) {
                    (
                        Ty::Reference {
                            inner: a,
                            mutable: am,
                            ..
                        },
                        Ty::Reference {
                            inner: b,
                            mutable: bm,
                            ..
                        },
                    ) if am == bm => match (self.ty(*a)?, self.ty(*b)?) {
                        (
                            Ty::Array { inner: a, .. } | Ty::SymbolicArray { inner: a, .. },
                            Ty::Slice(b),
                        ) => self.compatible(*a, *b),
                        _ => fail("invalid array-to-slice conversion"),
                    },
                    _ => fail("array-to-slice conversion requires matching reference types"),
                }
            }
            Rvalue::Length(place) => {
                let ty = self.value_place(place)?;
                require(
                    matches!(
                        self.ty(ty)?,
                        Ty::Array { .. } | Ty::SymbolicArray { .. } | Ty::Slice(_)
                    ),
                    "length requires an array or slice",
                )?;
                require(
                    matches!(
                        self.ty(expected)?,
                        Ty::Integer {
                            signed: false,
                            bits: 0
                        }
                    ),
                    "length result must be usize",
                )
            }
        }
    }
    fn assignment(&self, destination: &Place, value: &Rvalue) -> Result<(), InvariantError> {
        if let Rvalue::AddressOf(source) = value {
            let target = self.local(destination.local)?;
            require(
                target.kind == LocalKind::Address && destination.projection.is_empty(),
                "place capture requires an address local destination",
            )?;
            self.compatible(self.value_place(source)?, target.ty)
        } else {
            self.rvalue(value, self.value_place(destination)?)
        }
    }
    fn needs_checked(&self, value: &Rvalue) -> Result<bool, InvariantError> {
        let operand = match value {
            Rvalue::Unary {
                op: UnaryOp::Negate,
                operand,
            } => operand,
            Rvalue::Binary {
                op:
                    BinaryOp::Add
                    | BinaryOp::Subtract
                    | BinaryOp::Multiply
                    | BinaryOp::Divide
                    | BinaryOp::Remainder
                    | BinaryOp::ShiftLeft
                    | BinaryOp::ShiftRight,
                left,
                ..
            } => left,
            _ => return Ok(false),
        };
        Ok(self.program.types.integer(self.operand(operand)?))
    }
    fn structure(&self) -> Result<(), InvariantError> {
        require(
            self.body.blocks.len() <= LIMIT
                && self.body.locals.len() <= LIMIT
                && self.body.scopes.len() <= LIMIT,
            "MIR arena limit exceeded",
        )?;
        let source = self.source;
        self.compatible(self.body.result, source.result)?;
        self.block(self.body.entry)?;
        let returned = self.local(self.body.return_local)?;
        require(
            returned.kind == LocalKind::Return,
            "return local has the wrong kind",
        )?;
        self.compatible(returned.ty, self.body.result)?;
        let mut parameters = Vec::new();
        for (index, local) in self.body.locals.iter().enumerate() {
            self.ty(local.ty)?;
            self.scope(local.scope)?;
            require(
                local.kind != LocalKind::Return || index == self.body.return_local.0 as usize,
                "multiple return locals",
            )?;
            if local.kind == LocalKind::Parameter {
                parameters.push(local.ty);
            }
        }
        require(
            parameters.len() == source.parameters.len(),
            "MIR parameter count mismatch",
        )?;
        for (actual, expected) in parameters.into_iter().zip(&source.parameters) {
            self.compatible(actual, source.locals[expected.0 as usize].ty)?;
        }
        for (index, scope) in self.body.scopes.iter().enumerate() {
            require(
                if index == 0 {
                    scope.parent.is_none()
                } else {
                    scope
                        .parent
                        .is_some_and(|parent| (parent.0 as usize) < index)
                },
                "scope tree is not rooted or has a forward parent",
            )?;
        }
        let mut remaining = LIMIT;
        let mut arguments = vec![false; self.body.locals.len()];
        for (index, block) in self.body.blocks.iter().enumerate() {
            remaining = remaining
                .checked_sub(block.statements.len() + 1)
                .ok_or_else(|| InvariantError::new("MIR instruction limit exceeded".into()))?;
            self.block_structure(block)
                .map_err(|error| InvariantError::new(format!("bb{index}: {error}")))?;
            for statement in &block.statements {
                if let StatementKind::Argument(local) = statement.kind {
                    require(
                        index == self.body.entry.0 as usize && !arguments[local.0 as usize],
                        "parameter must be initialized exactly once in the entry block",
                    )?;
                    arguments[local.0 as usize] = true;
                }
            }
        }
        require(
            self.body
                .locals
                .iter()
                .zip(arguments)
                .all(|(local, initialized)| local.kind != LocalKind::Parameter || initialized),
            "parameter has no incoming argument initialization",
        )?;
        Ok(())
    }
    fn block_structure(&self, block: &Block) -> Result<(), InvariantError> {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::IteratorStart { iterator, value } => {
                    self.iterator_element(*iterator)?;
                    self.compatible(self.operand(value)?, self.local(*iterator)?.ty)?;
                }
                StatementKind::EnterScope(scope) | StatementKind::ExitScope(scope) => {
                    self.scope(*scope)?;
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    self.local(*local)?;
                }
                StatementKind::Argument(local) => require(
                    self.local(*local)?.kind == LocalKind::Parameter,
                    "argument instruction requires a parameter local",
                )?,
                StatementKind::Assign { destination, value } => {
                    require(
                        !self.needs_checked(value)?,
                        "integer arithmetic is missing its explicit trap edge",
                    )?;
                    self.assignment(destination, value)?
                }
            }
        }
        match &block.terminator {
            Terminator::Goto(target) => {
                self.block(*target)?;
            }
            Terminator::Switch { condition, yes, no } => {
                self.compatible(self.operand(condition)?, TyId::BOOL)?;
                self.block(*yes)?;
                self.block(*no)?;
            }
            Terminator::Call { .. } => self.call_structure(&block.terminator)?,
            Terminator::DynCall { .. } => self.dynamic_structure(&block.terminator)?,
            Terminator::IteratorNext {
                iterator,
                destination,
                some,
                none,
            } => self.iterator_structure(*iterator, destination, *some, *none)?,
            Terminator::Checked {
                value,
                destination,
                normal,
                trap,
            } => {
                require(
                    self.needs_checked(value)?,
                    "checked terminator requires a trapping integer operation",
                )?;
                self.assignment(destination, value)?;
                self.block(*normal)?;
                require(
                    matches!(self.block(*trap)?.terminator, Terminator::Abort),
                    "arithmetic trap must abort",
                )?;
            }
            Terminator::Bounds {
                base,
                index,
                normal,
                trap,
            } => {
                require(
                    matches!(
                        self.ty(self.place(base)?)?,
                        Ty::Array { .. } | Ty::SymbolicArray { .. } | Ty::Slice(_)
                    ),
                    "bounds check requires an array or slice",
                )?;
                let index = self.local(*index)?;
                require(
                    index.kind != LocalKind::Address
                        && matches!(
                            self.ty(index.ty)?,
                            Ty::Integer {
                                signed: false,
                                bits: 0
                            }
                        ),
                    "bounds index must be usize",
                )?;
                self.block(*normal)?;
                require(
                    matches!(self.block(*trap)?.terminator, Terminator::Abort),
                    "bounds trap must abort",
                )?;
            }
            Terminator::Drop {
                place,
                next,
                unwind,
            } => {
                self.place(place)?;
                require(
                    self.local(place.local)?.kind != LocalKind::ArrayIterator
                        || place.projection.is_empty(),
                    "owned iterator cleanup must drop its entire remaining tail",
                )?;
                self.block(*next)?;
                require(
                    matches!(self.block(*unwind)?.terminator, Terminator::Abort),
                    "Drop glue panic must abort",
                )?;
            }
            Terminator::Resume(reason) => require(
                *reason != ExitKind::Normal,
                "normal exit cannot resume unwinding",
            )?,
            Terminator::Return | Terminator::Abort | Terminator::Unreachable => {}
        }
        Ok(())
    }
    fn abnormal_target(&self, target: BlockId, kind: ExitKind) -> Result<(), InvariantError> {
        let block = self.block(target)?;
        require(
            block.cleanup == Some(kind) || matches!(block.terminator, Terminator::Abort),
            "abnormal edge does not enter matching cleanup",
        )
    }
}

fn require(condition: bool, message: &str) -> Result<(), InvariantError> {
    if condition { Ok(()) } else { fail(message) }
}
fn fail<T>(message: &str) -> Result<T, InvariantError> {
    Err(InvariantError::new(message.into()))
}
