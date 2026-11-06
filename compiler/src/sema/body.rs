use super::{Context, literal};
mod calls;
mod constants;
mod generics;
mod records;
use crate::{
    diagnostic::{Diagnostic, report},
    hir::{self, DefId, ExprId, ExprKind as H, LocalId, ModuleId, StmtId, StmtKind as S},
    source::Span,
    symbol::Symbol,
    syntax::ast::{
        self, BinaryOp as B, ExprKind as A, LiteralKind, StmtKind, TypeKind, UnaryOp as U,
    },
    types::{Ty, TyId},
};
use calls::ResolvedCall;
use std::collections::{HashMap, HashSet};

mod closures;
mod deferred;
mod methods;
mod patterns;
mod propagation;
pub(super) use propagation::result_item;

pub(super) fn check_function(
    context: &mut Context<'_>,
    module: ModuleId,
    definition: DefId,
    source: &ast::Function,
    body: &ast::Block,
) -> hir::Function {
    let parameters = match context.program.types.get(context.definition(definition).ty) {
        Ty::Function { parameters, .. } => parameters.clone(),
        _ => Vec::new(),
    };
    let mut checker = Body::new(context, module, definition, body.span);
    let result = checker.function.result;
    for (parameter, ty) in source.parameters.iter().zip(parameters) {
        let local = checker.bind(parameter.name, ty, true, Init::Initialized);
        checker.function.parameters.push(local);
    }
    for clause in &source.clauses {
        let clause = checker.clause(clause);
        checker.function.clauses.push(clause);
    }
    let (checked, falls_through) = checker.block(body);
    checker.function.body = checked;
    if falls_through && result != TyId::VOID && result != TyId::ERROR {
        checker.context.error(
            "E-RETURN-MISSING",
            "not every path returns a value",
            body.span,
        );
    }
    checker.function
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Init {
    Uninitialized,
    Initialized,
    Maybe,
}

#[derive(Clone, Copy)]
enum ReturnMode {
    Declared,
    InferClosure,
}

struct Body<'a, 'b> {
    context: &'b mut Context<'a>,
    module: ModuleId,
    definition: DefId,
    generic_types: HashMap<Symbol, TyId>,
    scopes: Vec<HashMap<Symbol, LocalId>>,
    states: Vec<Init>,
    loop_locals: Vec<usize>,
    depth: usize,
    expression_frames: usize,
    in_contract: bool,
    return_mode: ReturnMode,
    uncaptured: HashSet<Symbol>,
    constant_values: HashMap<LocalId, super::constants::ConstBinding>,
    function: hir::Function,
}

impl<'a, 'b> Body<'a, 'b> {
    fn new(context: &'b mut Context<'a>, module: ModuleId, definition: DefId, span: Span) -> Self {
        let result = match context.program.types.get(context.definition(definition).ty) {
            Ty::Function { result, .. } => *result,
            _ => TyId::ERROR,
        };
        let type_parameters = context
            .program
            .types
            .generic_parameters(definition)
            .iter()
            .filter_map(|&(name, kind)| {
                (kind == crate::types::GenericParamKind::Type).then_some(name)
            })
            .collect();
        let generic_types = context.parameters(definition);
        Self {
            context,
            module,
            definition,
            generic_types,
            scopes: vec![HashMap::new()],
            states: Vec::new(),
            loop_locals: Vec::new(),
            depth: 0,
            expression_frames: 0,
            in_contract: false,
            return_mode: ReturnMode::Declared,
            uncaptured: HashSet::new(),
            constant_values: HashMap::new(),
            function: hir::Function {
                definition,
                type_parameters,
                parameters: Vec::new(),
                result,
                locals: Vec::new(),
                clauses: Vec::new(),
                body: hir::Block {
                    statements: Vec::new(),
                    span,
                },
                expressions: Vec::new(),
                statements: Vec::new(),
            },
        }
    }
    fn clause(&mut self, clause: &ast::Clause) -> hir::Clause {
        self.in_contract = true;
        self.scopes.push(HashMap::new());
        let result_local =
            if clause.kind == ast::ClauseKind::Ensures && self.function.result != TyId::VOID {
                self.context.symbols.lookup("result").map(|symbol| {
                    let name = ast::Name {
                        symbol,
                        span: self.context.ast.expr(clause.predicate).span,
                    };
                    self.bind(name, self.function.result, false, Init::Initialized)
                })
            } else {
                None
            };
        let predicate = self.expression(clause.predicate, Some(TyId::BOOL));
        self.scopes.pop();
        self.in_contract = false;
        hir::Clause {
            kind: clause.kind,
            predicate,
            result_local,
        }
    }
    fn add_expr(&mut self, kind: H, ty: TyId, span: Span) -> ExprId {
        let id = ExprId(self.function.expressions.len() as u32);
        self.function.expressions.push(hir::Expr { kind, ty, span });
        id
    }
    fn add_stmt(&mut self, kind: S, span: Span) -> StmtId {
        let id = StmtId(self.function.statements.len() as u32);
        self.function.statements.push(hir::Stmt { kind, span });
        id
    }
    fn expr(&self, id: ExprId) -> &hir::Expr {
        &self.function.expressions[id.0 as usize]
    }
    fn ty(&self, id: ExprId) -> TyId {
        self.expr(id).ty
    }
    fn type_kind(&self, ty: TyId) -> &Ty {
        self.context.program.types.get(ty)
    }
    fn bind(&mut self, name: ast::Name, ty: TyId, mutable: bool, state: Init) -> LocalId {
        if let Some(previous) = self.scopes.last().and_then(|scope| scope.get(&name.symbol)) {
            report(
                self.context.diagnostics,
                Diagnostic::error("E-NAME-DUPLICATE", "duplicate local binding", name.span).label(
                    self.function.locals[previous.0 as usize].span,
                    "first binding",
                ),
            );
        }
        if ty == TyId::VOID
            || ty == TyId::STR
            || matches!(self.type_kind(ty), Ty::Slice(_) | Ty::Dynamic { .. })
        {
            self.context.error(
                "E-TYPE-SIZED",
                "a local must have a sized value type",
                name.span,
            );
        }
        let id = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(hir::Local {
            name: name.symbol,
            ty,
            mutable,
            span: name.span,
        });
        self.states.push(state);
        self.scopes
            .last_mut()
            .expect("function scope")
            .insert(name.symbol, id);
        id
    }
    fn find_local(&self, name: Symbol) -> Option<LocalId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(&name).copied())
    }
    fn resolve_type(&mut self, ty: ast::TypeId) -> TyId {
        let bindings = self.constant_bindings();
        self.context.resolve_type_with_bindings(
            ty,
            self.module,
            self.definition,
            &self.generic_types,
            &bindings,
        )
    }
    fn mismatch(&mut self, actual: TyId, expected: TyId, span: Span) {
        let types = &self.context.program.types;
        let actual = types.display(
            actual,
            self.context.symbols,
            &self.context.program.definitions,
        );
        let expected = types.display(
            expected,
            self.context.symbols,
            &self.context.program.definitions,
        );
        report(
            self.context.diagnostics,
            Diagnostic::error("E-TYPE-MISMATCH", "mismatched types", span)
                .primary_label(format!("expected `{expected}`, found `{actual}`")),
        );
    }
    fn coerce(&mut self, value: ExprId, expected: TyId) -> ExprId {
        let actual = self.ty(value);
        if self.context.program.types.compatible(actual, expected) {
            return value;
        }
        if let Some(value) = self.coerce_dynamic(value, expected) {
            return value;
        }
        let array_to_slice = match (self.type_kind(actual), self.type_kind(expected)) {
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
            ) if a == b => match (self.type_kind(*x), self.type_kind(*y)) {
                (
                    Ty::Array { inner: element, .. } | Ty::SymbolicArray { inner: element, .. },
                    Ty::Slice(expected_element),
                ) => self
                    .context
                    .program
                    .types
                    .compatible(*element, *expected_element),
                _ => false,
            },
            _ => false,
        };
        if array_to_slice {
            return self.add_expr(
                H::CoerceArrayToSlice(value),
                expected,
                self.expr(value).span,
            );
        }
        let span = self.expr(value).span;
        self.mismatch(actual, expected, span);
        self.add_expr(H::Error, TyId::ERROR, span)
    }
    fn block(&mut self, source: &ast::Block) -> (hir::Block, bool) {
        self.scopes.push(HashMap::new());
        let mut statements = Vec::new();
        let mut falls_through = true;
        for &statement in &source.statements {
            let (statement, falls) = self.statement(statement);
            statements.push(statement);
            falls_through &= falls;
        }
        self.scopes.pop();
        (
            hir::Block {
                statements,
                span: source.span,
            },
            falls_through,
        )
    }
    fn statement(&mut self, id: ast::StmtId) -> (StmtId, bool) {
        let ast = self.context.ast;
        let source = ast.stmt(id);
        let mut falls = true;
        let kind = match &source.kind {
            StmtKind::Variable(variable) => {
                let declared = if matches!(ast.ty(variable.ty).kind, TypeKind::Infer) {
                    None
                } else {
                    Some(self.resolve_type(variable.ty))
                };
                let initializer = variable
                    .initializer
                    .map(|value| self.expression(value, declared));
                let ty = declared
                    .or_else(|| initializer.map(|id| self.ty(id)))
                    .unwrap_or_else(|| {
                        self.context.error(
                            "E-TYPE-INFER",
                            "auto requires an initializer",
                            variable.name.span,
                        );
                        TyId::ERROR
                    });
                let constant = self.constant_initializer(variable, ty);
                let local = self.bind(
                    variable.name,
                    ty,
                    !variable.constant,
                    if initializer.is_some() {
                        Init::Initialized
                    } else {
                        Init::Uninitialized
                    },
                );
                if let Some(value) = constant {
                    self.constant_values.insert(local, value);
                }
                S::Declare { local, initializer }
            }
            StmtKind::Expression(expression) => {
                let value = self.expression(*expression, None);
                falls = !self.expression_diverges(value);
                S::Expression(value)
            }
            StmtKind::Assign { target, op, value } => {
                let target = self.place_expression(*target, op.is_some());
                let ty = self.ty(target);
                let value = self.expression(*value, Some(ty));
                if op.is_some_and(|op| !self.valid_operator(op, ty)) && ty != TyId::ERROR {
                    self.context.error(
                        "E-TYPE-OPERATOR",
                        "invalid operand type for compound assignment",
                        source.span,
                    );
                }
                if let Some(local) = self.assigned_local(target) {
                    let slot = local.0 as usize;
                    let binding = &self.function.locals[slot];
                    if !binding.mutable
                        && (self.states[slot] != Init::Uninitialized
                            || self.loop_locals.iter().any(|&base| slot < base))
                    {
                        self.context.error(
                            "E-ASSIGN-CONST",
                            "cannot assign this const binding again",
                            self.expr(target).span,
                        );
                    }
                    self.states[slot] = Init::Initialized;
                } else if !self.mutable_place(target) {
                    self.context.error(
                        "E-ASSIGN-PLACE",
                        "assignment requires a mutable place",
                        self.expr(target).span,
                    );
                }
                S::Assign {
                    target,
                    op: *op,
                    value,
                }
            }
            StmtKind::Return(value) => {
                let result = self.function.result;
                let expected = match self.return_mode {
                    ReturnMode::Declared => Some(result),
                    ReturnMode::InferClosure => None,
                };
                let value = value.map(|value| self.expression(value, expected));
                if value.is_none() && result != TyId::VOID && result != TyId::ERROR {
                    self.context
                        .error("E-RETURN-VALUE", "return requires a value", source.span);
                }
                falls = false;
                S::Return(value)
            }
            StmtKind::Block(body) => {
                let (block, fall) = self.block(body);
                falls = fall;
                S::Block(block)
            }
            StmtKind::If {
                condition,
                then_block,
                otherwise,
            } => {
                let condition = self.expression(*condition, Some(TyId::BOOL));
                let before = self.states.clone();
                let (then_block, then_falls) = self.block(then_block);
                let after_then = self.states.clone();
                self.restore(&before);
                let (otherwise, else_falls) = if let Some(statement) = otherwise {
                    let (statement, falls) = self.statement(*statement);
                    (Some(statement), falls)
                } else {
                    (None, true)
                };
                let after_else = self.states.clone();
                for index in 0..before.len() {
                    self.states[index] = match (then_falls, else_falls) {
                        (true, true) => merge(after_then[index], after_else[index]),
                        (true, false) => after_then[index],
                        (false, true) => after_else[index],
                        (false, false) => before[index],
                    };
                }
                falls = then_falls || else_falls;
                S::If {
                    condition,
                    then_block,
                    otherwise,
                }
            }
            StmtKind::While { condition, body } => {
                let condition = self.expression(*condition, Some(TyId::BOOL));
                let before = self.states.clone();
                self.loop_locals.push(self.function.locals.len());
                let (body, _) = self.block(body);
                self.loop_locals.pop();
                self.merge_loop(&before);
                S::While { condition, body }
            }
            StmtKind::For {
                initialize,
                condition,
                update,
                body,
            } => {
                self.scopes.push(HashMap::new());
                let initialize = initialize.map(|id| self.statement(id).0);
                let condition = condition.map(|id| self.expression(id, Some(TyId::BOOL)));
                let before = self.states.clone();
                self.loop_locals.push(self.function.locals.len());
                let (body, _) = self.block(body);
                let update = update.map(|id| self.statement(id).0);
                self.loop_locals.pop();
                self.merge_loop(&before);
                self.scopes.pop();
                S::For {
                    initialize,
                    condition,
                    update,
                    body,
                }
            }
            StmtKind::ForIn {
                variable,
                iterable,
                body,
            } => {
                let iterable = self.expression(*iterable, None);
                let mut ty = self.ty(iterable);
                if let Ty::Reference { inner, .. } = self.type_kind(ty) {
                    ty = *inner;
                }
                let element = match self.type_kind(ty) {
                    Ty::Array { inner, .. }
                    | Ty::SymbolicArray { inner, .. }
                    | Ty::Slice(inner) => *inner,
                    _ => {
                        self.context.error(
                            "E-TYPE-ITERABLE",
                            "for-in requires an array or slice",
                            source.span,
                        );
                        TyId::ERROR
                    }
                };
                if !matches!(ast.ty(variable.ty).kind, TypeKind::Infer) {
                    let declared = self.resolve_type(variable.ty);
                    if !self.context.program.types.compatible(element, declared) {
                        self.mismatch(element, declared, variable.name.span);
                    }
                }
                if variable.initializer.is_some() {
                    self.context.error(
                        "E-PARSE-FOR",
                        "for-in bindings cannot have initializers",
                        variable.name.span,
                    );
                }
                let before = self.states.clone();
                self.scopes.push(HashMap::new());
                let local = self.bind(
                    variable.name,
                    element,
                    !variable.constant,
                    Init::Initialized,
                );
                self.loop_locals.push(self.function.locals.len());
                let (body, _) = self.block(body);
                self.loop_locals.pop();
                self.scopes.pop();
                self.merge_loop(&before);
                S::ForIn {
                    local,
                    iterable,
                    body,
                }
            }
            StmtKind::Break | StmtKind::Continue => {
                if self.loop_locals.is_empty() {
                    self.context.error(
                        "E-CONTROL-LOOP",
                        "break/continue requires a loop",
                        source.span,
                    );
                }
                falls = false;
                if matches!(source.kind, StmtKind::Break) {
                    S::Break
                } else {
                    S::Continue
                }
            }
            StmtKind::StaticAssert(assertion) => self.static_assertion(assertion),
            StmtKind::Empty => S::Empty,
            StmtKind::Scope { .. } => {
                self.context
                    .unsupported("task scope lifetime/effect checking", source.span);
                S::Error
            }
            StmtKind::Contract(_) | StmtKind::Assume { .. } => {
                self.context
                    .unsupported("raw contract permission checking", source.span);
                S::Error
            }
            StmtKind::Defer(body) => self.deferred(body),
            StmtKind::Error => S::Error,
        };
        (self.add_stmt(kind, source.span), falls)
    }
    fn restore(&mut self, before: &[Init]) {
        self.states[..before.len()].copy_from_slice(before);
    }
    fn merge_loop(&mut self, before: &[Init]) {
        for (slot, &old) in self.states.iter_mut().zip(before) {
            *slot = merge(old, *slot);
        }
    }

    fn expression(&mut self, id: ast::ExprId, expected: Option<TyId>) -> ExprId {
        if self.depth >= 128 || self.expression_frames >= 256 {
            let span = self.context.ast.expr(id).span;
            self.context.error(
                "E-TYPE-DEPTH",
                "expression exceeds the 128-level nesting or 256-frame traversal budget",
                span,
            );
            return self.add_expr(H::Error, TyId::ERROR, span);
        }
        let nested = usize::from(!matches!(self.context.ast.expr(id).kind, A::Binary { .. }));
        self.depth += nested;
        self.expression_frames += 1;
        let value = self.expression_inner(id, expected);
        self.depth -= nested;
        self.expression_frames -= 1;
        if let Some(expected) = expected {
            self.coerce(value, expected)
        } else {
            value
        }
    }
    fn expression_inner(&mut self, id: ast::ExprId, expected: Option<TyId>) -> ExprId {
        let ast = self.context.ast;
        let source = ast.expr(id);
        let (kind, ty) = match &source.kind {
            A::Literal(kind) => {
                let text = self
                    .context
                    .sources
                    .file(source.span.file)
                    .slice(source.span);
                let (ty, value) = literal::check(
                    text,
                    *kind,
                    expected,
                    false,
                    source.span,
                    &mut self.context.program.types,
                    self.context.diagnostics,
                );
                (H::Constant(value), ty)
            }
            A::Path(path) => {
                if path.len() > 1 && self.find_local(path[0].symbol).is_some() {
                    report(
                        self.context.diagnostics,
                        Diagnostic::error(
                            "E-NAME-SEPARATOR",
                            "value members use '.', not '::'",
                            source.span,
                        )
                        .help("use `.` to access fields and methods on a local value"),
                    );
                    return self.add_expr(H::Error, TyId::ERROR, source.span);
                }
                if path.len() == 1
                    && let Some(local) = self.find_local(path[0].symbol)
                {
                    return self.read_local(local, source.span);
                }
                if path.len() == 1 && self.uncaptured.contains(&path[0].symbol) {
                    self.context.error(
                        "E-CLOSURE-CAPTURE",
                        "closure use requires an explicit capture",
                        source.span,
                    );
                    return self.add_expr(H::Error, TyId::ERROR, source.span);
                }
                if path.len() == 1
                    && let Some(value) = self.generic_constant(path[0])
                {
                    return value;
                }
                if let Ok(Some(value)) = self.context.integer_constant(path, source.span) {
                    return self.materialize_constant(value, source.span);
                }
                if let Some(definition) = self.context.resolve(self.module, path) {
                    if self.context.is_drop_method(definition) {
                        self.context.error(
                            "E-DROP-EXPLICIT",
                            "a destructor cannot be called or stored as a function value",
                            source.span,
                        );
                        return self.add_expr(H::Error, TyId::ERROR, source.span);
                    }
                    if self.context.definition(definition).kind == hir::DefinitionKind::Global {
                        return self.constant_expression(definition, source.span);
                    }
                    if !matches!(
                        self.context.definition(definition).kind,
                        hir::DefinitionKind::Function | hir::DefinitionKind::Variant { .. }
                    ) {
                        self.context
                            .error("E-TYPE-VALUE", "this name is not a value", source.span);
                    }
                    if let Some(ty) = self.unit_variant_type(definition, expected, source.span) {
                        return self.add_expr(H::Definition(definition), ty, source.span);
                    }
                    let ty = self.context.definition(definition).ty;
                    let ty = if self.context.definition(definition).kind
                        == hir::DefinitionKind::Function
                    {
                        self.context
                            .program
                            .types
                            .generalize_callable(ty, definition)
                            .unwrap_or_else(|| {
                                self.context.error(
                                    "E-REGION-LIMIT",
                                    "callable generalization exceeds its resource limit",
                                    source.span,
                                );
                                TyId::ERROR
                            })
                    } else {
                        ty
                    };
                    (H::Definition(definition), ty)
                } else {
                    (H::Error, TyId::ERROR)
                }
            }
            A::Group(inner) => {
                let inner = self.expression(*inner, expected);
                (H::Group(inner), self.ty(inner))
            }
            A::Unary {
                op: U::Negate,
                operand,
            } if matches!(
                ast.expr(*operand).kind,
                A::Literal(LiteralKind::Integer | LiteralKind::Float)
            ) =>
            {
                let node = ast.expr(*operand);
                let A::Literal(kind) = node.kind else {
                    unreachable!();
                };
                let text = self.context.sources.file(node.span.file).slice(node.span);
                let (ty, value) = literal::check(
                    text,
                    kind,
                    expected,
                    true,
                    source.span,
                    &mut self.context.program.types,
                    self.context.diagnostics,
                );
                (H::Constant(value), ty)
            }
            A::Unary { op, operand } => {
                if *op == U::Spawn {
                    self.context
                        .unsupported("spawn task/effect checking", source.span);
                    return self.add_expr(H::Error, TyId::ERROR, source.span);
                }
                let operand_expected = match op {
                    U::Not => Some(TyId::BOOL),
                    U::Positive | U::Negate | U::BitNot => expected,
                    U::Borrow | U::BorrowMut => {
                        match expected.and_then(|ty| match self.type_kind(ty) {
                            Ty::Reference { inner, .. } => Some(*inner),
                            _ => None,
                        }) {
                            Some(ty)
                                if matches!(
                                    self.type_kind(ty),
                                    Ty::Slice(_) | Ty::Dynamic { .. }
                                ) =>
                            {
                                None
                            }
                            other => other,
                        }
                    }
                    U::Dereference => None,
                    _ => expected,
                };
                let operand = self.expression(*operand, operand_expected);
                let ty = self.ty(operand);
                let result = match op {
                    U::Not => TyId::BOOL,
                    U::Positive | U::Negate | U::BitNot => {
                        let valid = match self.type_kind(ty) {
                            Ty::Integer { signed, .. } => *op != U::Negate || *signed,
                            Ty::Float { .. } => *op != U::BitNot,
                            Ty::Error => true,
                            _ => false,
                        };
                        if !valid {
                            self.context.error(
                                "E-TYPE-OPERATOR",
                                "invalid operand type for unary operator",
                                source.span,
                            );
                        }
                        ty
                    }
                    U::Borrow | U::BorrowMut => {
                        if *op == U::BorrowMut && !self.mutable_place(operand) {
                            self.context.error(
                                "E-BORROW-MUTABLE",
                                "mutable borrow requires a mutable place",
                                source.span,
                            );
                        }
                        let region = self.context.program.types.fresh_region();
                        self.context.program.types.intern(Ty::Reference {
                            region,
                            mutable: *op == U::BorrowMut,
                            inner: ty,
                        })
                    }
                    U::Dereference => match self.type_kind(ty) {
                        Ty::Reference { inner, .. } => *inner,
                        Ty::Pointer { .. } => {
                            self.context
                                .unsupported("raw dereference permission checking", source.span);
                            TyId::ERROR
                        }
                        Ty::Error => TyId::ERROR,
                        _ => {
                            self.context.error(
                                "E-TYPE-DEREF",
                                "dereference requires a reference",
                                source.span,
                            );
                            TyId::ERROR
                        }
                    },
                    U::Move => ty,
                    U::Spawn => unreachable!(),
                };
                (H::Unary { op: *op, operand }, result)
            }
            A::Binary { op, left, right } => {
                let logical = matches!(op, B::And | B::Or);
                let comparison = matches!(
                    op,
                    B::Less | B::LessEqual | B::Greater | B::GreaterEqual | B::Equal | B::NotEqual
                );
                let hint = if logical {
                    Some(TyId::BOOL)
                } else if comparison {
                    None
                } else {
                    expected
                };
                let left = self.expression(*left, hint);
                let operand_ty = self.ty(left);
                let right = self.expression(*right, Some(operand_ty));
                let valid = self.valid_operator(*op, operand_ty);
                if !valid && operand_ty != TyId::ERROR {
                    self.context.error(
                        "E-TYPE-OPERATOR",
                        "operator does not accept these operands",
                        source.span,
                    );
                }
                (
                    H::Binary {
                        op: *op,
                        left,
                        right,
                    },
                    if logical || comparison {
                        TyId::BOOL
                    } else {
                        operand_ty
                    },
                )
            }
            A::Call {
                callee,
                type_arguments,
                arguments,
            } => return self.call(*callee, type_arguments, arguments, expected, source.span),
            A::Field { base, name } => {
                if let A::Path(path) = &ast.expr(*base).kind
                    && !(path.len() == 1 && self.find_local(path[0].symbol).is_some())
                    && self.context.is_namespace(self.module, path)
                {
                    report(
                        self.context.diagnostics,
                        Diagnostic::error(
                            "E-NAME-SEPARATOR",
                            "type and module members use '::', not '.'",
                            name.span,
                        )
                        .help(format!(
                            "write `{}::{}`",
                            self.context.path_name(path),
                            self.context.symbols.get(name.symbol)
                        )),
                    );
                    return self.add_expr(H::Error, TyId::ERROR, source.span);
                }
                let base = self.expression(*base, None);
                let mut ty = self.ty(base);
                if let Ty::Reference { inner, .. } = self.type_kind(ty) {
                    ty = *inner;
                }
                let nominal = match self.type_kind(ty) {
                    Ty::Named {
                        definition,
                        arguments,
                    } => Some((*definition, arguments.clone())),
                    _ => None,
                };
                let field = nominal
                    .as_ref()
                    .and_then(|(definition, _)| {
                        self.context.record_indices[definition.0 as usize]
                            .map(|index| &self.context.program.records[index])
                    })
                    .and_then(|record| {
                        record
                            .fields
                            .iter()
                            .enumerate()
                            .find(|(_, field)| field.name == name.symbol)
                    })
                    .map(|(index, field)| (index as u32, field.ty, field.visibility, field.span));
                if let (Some((definition, arguments)), Some((index, ty, visibility, span))) =
                    (nominal, field)
                {
                    if self.context.definition(definition).module != self.module
                        && visibility == ast::Visibility::Private
                    {
                        report(
                            self.context.diagnostics,
                            Diagnostic::error("E-NAME-PRIVATE", "field is private", name.span)
                                .label(span, "private field"),
                        );
                    }
                    let ty = self
                        .context
                        .program
                        .types
                        .substitute(ty, definition, &arguments);
                    (H::Field { base, index }, ty)
                } else {
                    self.context.error(
                        "E-TYPE-FIELD",
                        format!("unknown field '{}'", self.context.symbols.get(name.symbol)),
                        name.span,
                    );
                    (H::Error, TyId::ERROR)
                }
            }
            A::Index { base, index } => {
                let base = self.expression(*base, None);
                let usize_ty = self
                    .context
                    .program
                    .types
                    .builtin("usize")
                    .expect("primitive");
                let index = self.expression(*index, Some(usize_ty));
                let mut ty = self.ty(base);
                if let Ty::Reference { inner, .. } = self.type_kind(ty) {
                    ty = *inner;
                }
                let element = match self.type_kind(ty) {
                    Ty::Array { inner, length } => {
                        let (inner, length) = (*inner, *length);
                        if let H::Constant(hir::Constant::Integer {
                            magnitude,
                            negative: false,
                        }) = self.expr(index).kind
                            && magnitude >= length as u128
                        {
                            self.context.error(
                                "E-INDEX-BOUNDS",
                                "constant index is outside the array",
                                self.expr(index).span,
                            );
                        }
                        inner
                    }
                    Ty::Slice(inner) | Ty::SymbolicArray { inner, .. } => *inner,
                    Ty::Error => TyId::ERROR,
                    _ => {
                        self.context.error(
                            "E-TYPE-INDEX",
                            "indexing requires an array or slice",
                            source.span,
                        );
                        TyId::ERROR
                    }
                };
                (H::Index { base, index }, element)
            }
            A::Array(elements) => {
                let hint = expected.and_then(|ty| match self.type_kind(ty) {
                    Ty::Array { inner, .. } => Some(*inner),
                    _ => None,
                });
                let mut values = Vec::new();
                let mut element_ty = hint;
                for &element in elements {
                    let value = self.expression(element, element_ty);
                    element_ty.get_or_insert(self.ty(value));
                    values.push(value);
                }
                let inner = element_ty.unwrap_or_else(|| {
                    self.context.error(
                        "E-TYPE-INFER",
                        "empty array requires a type annotation",
                        source.span,
                    );
                    TyId::ERROR
                });
                let ty = self.context.program.types.intern(Ty::Array {
                    inner,
                    length: elements.len() as u64,
                });
                (H::Array(values), ty)
            }
            A::Repeat { value, count } => {
                self.repeat_expression(*value, *count, expected, source.span)
            }
            A::Record { path, fields } => return self.record(path, fields, expected, source.span),
            A::Try(value) => return self.propagate(*value, expected, source.span),
            A::Match { value, arms } => {
                return self.match_expression(*value, arms, expected, source.span);
            }
            A::Closure {
                captures,
                parameters,
                result,
                body,
            } => {
                return self.closure(captures, parameters, *result, body, source.span);
            }
            A::Block(body) => return self.block_value(body, expected),
            A::Error => (H::Error, TyId::ERROR),
        };
        self.add_expr(kind, ty, source.span)
    }
    fn read_local(&mut self, local: LocalId, span: Span) -> ExprId {
        // Initialization at uses is checked on the CFG, including loop backedges.
        self.add_expr(
            H::Local(local),
            self.function.locals[local.0 as usize].ty,
            span,
        )
    }
    fn place_expression(&mut self, id: ast::ExprId, read: bool) -> ExprId {
        if let A::Group(inner) = self.context.ast.expr(id).kind {
            let inner = self.place_expression(inner, read);
            return self.add_expr(
                H::Group(inner),
                self.ty(inner),
                self.context.ast.expr(id).span,
            );
        }
        if let A::Path(path) = &self.context.ast.expr(id).kind
            && path.len() == 1
            && let Some(local) = self.find_local(path[0].symbol)
        {
            if read {
                return self.read_local(local, self.context.ast.expr(id).span);
            }
            return self.add_expr(
                H::Local(local),
                self.function.locals[local.0 as usize].ty,
                self.context.ast.expr(id).span,
            );
        }
        self.expression(id, None)
    }
    fn mutable_place(&self, id: ExprId) -> bool {
        match self.expr(id).kind {
            H::Local(local) => self.function.locals[local.0 as usize].mutable,
            H::Group(inner) => self.mutable_place(inner),
            H::Field { base, .. } | H::Index { base, .. } => match self.type_kind(self.ty(base)) {
                Ty::Reference { mutable, .. } => *mutable,
                _ => self.mutable_place(base),
            },
            H::Unary {
                op: U::Dereference,
                operand,
            } => matches!(
                self.type_kind(self.ty(operand)),
                Ty::Reference { mutable: true, .. }
            ),
            H::Error => true,
            _ => false,
        }
    }
    fn assigned_local(&self, id: ExprId) -> Option<LocalId> {
        match self.expr(id).kind {
            H::Local(local) => Some(local),
            H::Group(inner) => self.assigned_local(inner),
            _ => None,
        }
    }
    fn valid_operator(&self, op: B, ty: TyId) -> bool {
        match op {
            B::And | B::Or => ty == TyId::BOOL,
            B::Equal | B::NotEqual => {
                self.context.program.types.numeric(ty)
                    || matches!(self.type_kind(ty), Ty::Bool | Ty::Char)
            }
            B::BitAnd | B::BitOr | B::BitXor | B::ShiftLeft | B::ShiftRight | B::Remainder => {
                self.context.program.types.integer(ty)
            }
            _ => self.context.program.types.numeric(ty),
        }
    }
}

fn merge(left: Init, right: Init) -> Init {
    if left == right { left } else { Init::Maybe }
}
