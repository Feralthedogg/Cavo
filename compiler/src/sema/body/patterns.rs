//! Typed patterns keep tests separate from ownership commit. Guard evaluation
//! borrows candidate bindings; only the selected arm may consume their payloads.

use super::*;
use crate::{
    hir::{BindingMode, Pattern, PatternKind},
    local::properties::Properties,
};
use std::collections::HashSet;

mod coverage;

#[derive(Clone, Copy)]
struct Subject {
    ty: TyId,
    borrow: Option<(crate::types::Region, bool)>,
}

impl Body<'_, '_> {
    pub(super) fn match_expression(
        &mut self,
        value: ast::ExprId,
        arms: &[ast::MatchArm],
        expected: Option<TyId>,
        span: Span,
    ) -> ExprId {
        let subject = self.expression(value, None);
        let ty = self.ty(subject);
        let properties = Properties::compute(&mut self.context.program);
        let view = self.pattern_subject(ty);
        if view.borrow.is_none() && !properties.get(ty).copy && !self.explicit_match_move(value) {
            self.context.error(
                "E-MATCH-MOVE",
                "matching an owned non-Copy value requires `move`",
                span,
            );
        }
        let temporary = self.pattern_temporary(ty, span);
        let before = self.states.clone();
        let mut checked = Vec::with_capacity(arms.len());
        let mut exits = Vec::with_capacity(arms.len());
        let mut result = expected;
        for arm in arms {
            self.restore(&before);
            self.scopes.push(HashMap::new());
            let pattern = self.pattern(&arm.pattern, view, &properties, 0);
            let guard = arm
                .guard
                .map(|guard| self.expression(guard, Some(TyId::BOOL)));
            if let Some(guard) = guard {
                self.check_guard_moves(guard, &pattern);
            }
            let value = self.expression(arm.value, result);
            if !self.expression_diverges(value) {
                result.get_or_insert(self.ty(value));
                exits.push(self.states[..before.len()].to_vec());
            }
            checked.push(hir::MatchArm {
                pattern,
                guard,
                value,
            });
            self.scopes.pop();
        }
        self.merge_match_exits(&before, &exits);
        self.check_match_coverage(view.ty, &checked, span);
        let result = result.unwrap_or(TyId::VOID);
        for arm in &checked {
            if self.expression_diverges(arm.value) {
                self.retag_diverging(arm.value, result);
            }
        }
        self.add_expr(
            H::Match {
                subject,
                temporary,
                arms: checked,
            },
            result,
            span,
        )
    }

    fn retag_diverging(&mut self, value: ExprId, ty: TyId) {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            let expression = &mut self.function.expressions[value];
            expression.ty = ty;
            match &expression.kind {
                H::Group(inner) => pending.push(*inner),
                H::Match { arms, .. } => pending.extend(arms.iter().map(|arm| arm.value)),
                H::BlockValue { .. } => {}
                _ => unreachable!("only structurally diverging expressions are retagged"),
            }
        }
    }

    fn pattern_subject(&self, ty: TyId) -> Subject {
        match self.type_kind(ty) {
            Ty::Reference {
                inner,
                region,
                mutable,
            } => Subject {
                ty: *inner,
                borrow: Some((*region, *mutable)),
            },
            _ => Subject { ty, borrow: None },
        }
    }

    pub(super) fn pattern_temporary(&mut self, ty: TyId, span: Span) -> LocalId {
        let id = LocalId(self.function.locals.len() as u32);
        let name = self.context.definition(self.definition).name;
        self.function.locals.push(hir::Local {
            name,
            ty,
            mutable: false,
            span,
        });
        self.states.push(Init::Initialized);
        id
    }

    fn explicit_match_move(&self, mut value: ast::ExprId) -> bool {
        for _ in 0..256 {
            match self.context.ast.expr(value).kind {
                A::Group(inner) => value = inner,
                A::Unary { op: U::Move, .. } => return true,
                _ => return false,
            }
        }
        false
    }

    fn pattern(
        &mut self,
        source: &ast::Pattern,
        subject: Subject,
        properties: &Properties,
        depth: usize,
    ) -> Pattern {
        if depth >= 128 {
            self.context.error(
                "E-MATCH-LIMIT",
                "pattern exceeds its nesting limit",
                source.span,
            );
            return Pattern {
                kind: PatternKind::Wildcard,
                ty: subject.ty,
                span: source.span,
            };
        }
        let kind = match &source.kind {
            ast::PatternKind::Wildcard => PatternKind::Wildcard,
            ast::PatternKind::Error => {
                self.context.error(
                    "E-MATCH-PATTERN",
                    "an invalid pattern cannot be type checked",
                    source.span,
                );
                PatternKind::Wildcard
            }
            ast::PatternKind::Literal(kind) => self.pattern_literal(*kind, subject.ty, source.span),
            ast::PatternKind::Path { path, fields } => {
                self.pattern_path(path, fields, subject, properties, depth, source.span)
            }
        };
        Pattern {
            kind,
            ty: subject.ty,
            span: source.span,
        }
    }

    fn pattern_literal(&mut self, kind: LiteralKind, ty: TyId, span: Span) -> PatternKind {
        let text = self.context.sources.file(span.file).slice(span);
        let (_, value) = literal::check(
            text,
            kind,
            Some(ty),
            false,
            span,
            &mut self.context.program.types,
            self.context.diagnostics,
        );
        if !matches!(
            value,
            hir::Constant::Integer { .. } | hir::Constant::Bool(_) | hir::Constant::Char(_)
        ) {
            self.context.error(
                "E-MATCH-PATTERN",
                "patterns require integer, boolean, or character literals",
                span,
            );
        }
        PatternKind::Literal(value)
    }

    fn pattern_path(
        &mut self,
        path: &[ast::Name],
        fields: &[ast::Pattern],
        subject: Subject,
        properties: &Properties,
        depth: usize,
        span: Span,
    ) -> PatternKind {
        let variant = self.pattern_variant(path, subject.ty);
        if let Some(variant) = variant {
            let types = self.variant_fields(subject.ty, variant);
            if fields.len() != types.len() {
                self.context.error(
                    "E-MATCH-ARITY",
                    "variant pattern has the wrong number of fields",
                    span,
                );
            }
            let fields = fields
                .iter()
                .zip(types)
                .map(|(field, ty)| {
                    self.pattern(
                        field,
                        Subject {
                            ty,
                            borrow: subject.borrow,
                        },
                        properties,
                        depth + 1,
                    )
                })
                .collect();
            return PatternKind::Variant {
                definition: variant,
                fields,
            };
        }
        if path.len() == 1 && fields.is_empty() {
            let (ty, mode) = self.binding_type(subject, properties);
            let local = self.bind(path[0], ty, false, Init::Initialized);
            return PatternKind::Binding { local, mode };
        }
        self.context.error(
            "E-MATCH-VARIANT",
            "pattern does not name a variant of the matched enum",
            span,
        );
        PatternKind::Wildcard
    }

    fn binding_type(&mut self, subject: Subject, properties: &Properties) -> (TyId, BindingMode) {
        if let Some((region, mutable)) = subject.borrow {
            let ty = self.context.program.types.intern(Ty::Reference {
                region,
                mutable,
                inner: subject.ty,
            });
            return (
                ty,
                if mutable {
                    BindingMode::Mutable
                } else {
                    BindingMode::Shared
                },
            );
        }
        (
            subject.ty,
            if properties.get(subject.ty).copy {
                BindingMode::Copy
            } else {
                BindingMode::Move
            },
        )
    }

    fn pattern_variant(&mut self, path: &[ast::Name], ty: TyId) -> Option<DefId> {
        let Ty::Named { definition, .. } = self.type_kind(ty) else {
            return None;
        };
        let owner = *definition;
        if path.len() == 1 {
            return self.context.variants.get(&(owner, path[0].symbol)).copied();
        }
        let found = self.context.resolve(self.module, path)?;
        matches!(self.context.definition(found).kind, hir::DefinitionKind::Variant { parent, .. } if parent == owner).then_some(found)
    }

    pub(super) fn variant_fields(&mut self, ty: TyId, variant: DefId) -> Vec<TyId> {
        let Ty::Named {
            definition,
            arguments,
        } = self.type_kind(ty).clone()
        else {
            return Vec::new();
        };
        let fields = match self.type_kind(self.context.definition(variant).ty) {
            Ty::Function { parameters, .. } => parameters.clone(),
            _ => Vec::new(),
        };
        fields
            .into_iter()
            .map(|ty| {
                self.context
                    .program
                    .types
                    .substitute(ty, definition, &arguments)
            })
            .collect()
    }

    fn merge_match_exits(&mut self, before: &[Init], exits: &[Vec<Init>]) {
        self.restore(before);
        for (index, original) in before.iter().copied().enumerate() {
            self.states[index] = exits
                .iter()
                .map(|state| state[index])
                .reduce(merge)
                .unwrap_or(original);
        }
    }

    fn check_guard_moves(&mut self, guard: ExprId, pattern: &Pattern) {
        let mut bindings = HashSet::new();
        let mut patterns = vec![pattern];
        while let Some(pattern) = patterns.pop() {
            match &pattern.kind {
                PatternKind::Binding {
                    local,
                    mode: BindingMode::Move,
                } => {
                    bindings.insert(*local);
                }
                PatternKind::Variant { fields, .. } => patterns.extend(fields),
                _ => {}
            }
        }
        let mut pending = vec![guard];
        let mut seen = HashSet::new();
        let mut seen_statements = HashSet::new();
        while let Some(expression) = pending.pop() {
            if !seen.insert(expression) {
                continue;
            }
            if let H::Unary {
                op: U::Move,
                operand,
            } = self.expr(expression).kind
                && self.expression_uses_binding(operand, &bindings)
            {
                self.context.error(
                    "E-MATCH-GUARD-MOVE",
                    "a guard cannot consume a candidate pattern binding",
                    self.expr(expression).span,
                );
            }
            if let H::BlockValue { body, .. } = &self.expr(expression).kind {
                self.guard_block_children(body, &mut pending, &mut seen_statements);
            }
            expression_children(&self.expr(expression).kind, &mut pending);
        }
    }

    fn guard_block_children(
        &self,
        body: &hir::Block,
        expressions: &mut Vec<ExprId>,
        seen: &mut HashSet<StmtId>,
    ) {
        let mut statements = body.statements.clone();
        while let Some(id) = statements.pop() {
            if !seen.insert(id) {
                continue;
            }
            match &self.function.statements[id].kind {
                S::Declare { initializer, .. } | S::Return(initializer) => {
                    expressions.extend(initializer)
                }
                S::Expression(value) => expressions.push(*value),
                S::Assign { target, value, .. } => expressions.extend([*target, *value]),
                S::Block(body) | S::Defer { body, .. } => statements.extend(&body.statements),
                S::If {
                    condition,
                    then_block,
                    otherwise,
                } => {
                    expressions.push(*condition);
                    statements.extend(&then_block.statements);
                    statements.extend(otherwise);
                }
                S::While { condition, body } => {
                    expressions.push(*condition);
                    statements.extend(&body.statements);
                }
                S::For {
                    initialize,
                    condition,
                    update,
                    body,
                } => {
                    statements.extend(initialize);
                    statements.extend(update);
                    statements.extend(&body.statements);
                    expressions.extend(condition);
                }
                S::ForIn { iterable, body, .. } => {
                    expressions.push(*iterable);
                    statements.extend(&body.statements);
                }
                _ => {}
            }
        }
    }

    fn expression_uses_binding(&self, value: ExprId, bindings: &HashSet<LocalId>) -> bool {
        let mut pending = vec![value];
        let mut seen = HashSet::new();
        while let Some(value) = pending.pop() {
            if !seen.insert(value) {
                continue;
            }
            if matches!(self.expr(value).kind, H::Local(local) if bindings.contains(&local)) {
                return true;
            }
            expression_children(&self.expr(value).kind, &mut pending);
        }
        false
    }

    pub(super) fn block_value(&mut self, source: &ast::Block, expected: Option<TyId>) -> ExprId {
        let (body, falls) = self.block(source);
        let ty = if falls {
            TyId::VOID
        } else {
            expected.unwrap_or(TyId::VOID)
        };
        self.add_expr(H::BlockValue { body, value: None }, ty, source.span)
    }

    pub(super) fn expression_diverges(&self, value: ExprId) -> bool {
        match &self.expr(value).kind {
            H::BlockValue { body, .. } => self.block_diverges(body),
            H::Match { arms, .. } => arms.iter().all(|arm| self.expression_diverges(arm.value)),
            H::Group(value) => self.expression_diverges(*value),
            _ => false,
        }
    }

    fn block_diverges(&self, body: &hir::Block) -> bool {
        body.statements
            .iter()
            .any(|id| self.statement_diverges(*id))
    }

    fn statement_diverges(&self, statement: StmtId) -> bool {
        match &self.function.statements[statement].kind {
            S::Return(_) => true,
            S::Block(body) => self.block_diverges(body),
            S::Expression(value) => self.expression_diverges(*value),
            S::If {
                then_block,
                otherwise: Some(otherwise),
                ..
            } => self.block_diverges(then_block) && self.statement_diverges(*otherwise),
            _ => false,
        }
    }
}

fn expression_children(kind: &H, output: &mut Vec<ExprId>) {
    match kind {
        H::Unary { operand, .. }
        | H::Group(operand)
        | H::Old(operand)
        | H::CoerceArrayToSlice(operand)
        | H::DynCoerce { value: operand, .. } => output.push(*operand),
        H::Binary { left, right, .. }
        | H::Index {
            base: left,
            index: right,
        } => output.extend([*left, *right]),
        H::Field { base, .. } | H::IsVariant { base, .. } | H::VariantField { base, .. } => {
            output.push(*base)
        }
        H::Call {
            callee, arguments, ..
        } => {
            output.push(*callee);
            output.extend(arguments);
        }
        H::DynCall {
            receiver,
            arguments,
            ..
        } => {
            output.push(*receiver);
            output.extend(arguments);
        }
        H::Array(values) => output.extend(values),
        H::Repeat { value, .. } | H::RepeatConst { value, .. } => output.push(*value),
        H::Record { fields, .. } => output.extend(fields.iter().map(|(_, value)| value)),
        H::Match { subject, arms, .. } => {
            output.push(*subject);
            for arm in arms {
                output.extend(arm.guard);
                output.push(arm.value);
            }
        }
        H::BlockValue { value, .. } => output.extend(value),
        _ => {}
    }
}
