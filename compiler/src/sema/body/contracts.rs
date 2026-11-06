use super::*;

pub(in crate::sema) fn check_signature(
    context: &mut Context<'_>,
    module: ModuleId,
    definition: DefId,
    source: &ast::Function,
    span: Span,
) {
    let mut checker = Body::new(context, module, definition, span);
    seed_parameters(&mut checker, &source.parameters);
    for clause in &source.clauses {
        let checked = checker.clause(clause);
        checker.function.clauses.push(checked);
    }
    checker
        .context
        .program
        .contracts
        .signatures
        .insert(definition, checker.function);
}

pub(in crate::sema) fn check_predicate(
    context: &mut Context<'_>,
    module: ModuleId,
    definition: DefId,
    parameters: &[ast::Parameter],
    requirements: &[ast::ExprId],
    span: Span,
) -> hir::Function {
    if !requirements.is_empty()
        && context.program.contracts.predicates[&definition]
            .memory
            .is_some()
    {
        context.error(
            "E-LANG-CONTRACT",
            "a compiler-defined memory predicate cannot add source requirements",
            span,
        );
    }
    let mut checker = Body::new(context, module, definition, span);
    seed_parameters(&mut checker, parameters);
    checker.in_contract = true;
    let mut value = checker.add_expr(H::Constant(hir::Constant::Bool(true)), TyId::BOOL, span);
    for &requirement in requirements {
        let right = checker.expression(requirement, Some(TyId::BOOL));
        value = checker.add_expr(
            H::Binary {
                op: B::And,
                left: value,
                right,
            },
            TyId::BOOL,
            span,
        );
    }
    let returned = checker.add_stmt(S::Return(Some(value)), span);
    checker.function.body.statements.push(returned);
    checker.function
}

fn seed_parameters(checker: &mut Body<'_, '_>, parameters: &[ast::Parameter]) {
    let Ty::Function {
        parameters: types, ..
    } = checker.type_kind(checker.context.definition(checker.definition).ty)
    else {
        return;
    };
    let types = types.clone();
    for (parameter, ty) in parameters.iter().zip(types) {
        let local = checker.bind(parameter.name, ty, true, Init::Initialized);
        checker.function.parameters.push(local);
    }
}

impl Body<'_, '_> {
    pub(super) fn contract_block(&mut self, body: &ast::Block) -> (S, bool) {
        self.contract_depth += 1;
        let (body, falls) = self.block(body);
        self.contract_depth -= 1;
        (S::Block(body), falls)
    }

    pub(super) fn assumption(
        &mut self,
        predicate: ast::ExprId,
        reason: ast::ExprId,
        span: Span,
    ) -> S {
        if self.contract_depth == 0 {
            self.context.error(
                "E-CONTRACT-BOUNDARY",
                "assume requires an explicit contract block",
                span,
            );
            return S::Error;
        }
        let reason = self
            .context
            .sources
            .file(span.file)
            .slice(self.context.ast.expr(reason).span);
        let (_, hir::Constant::String(reason)) = literal::check(
            reason,
            LiteralKind::String,
            None,
            false,
            span,
            &mut self.context.program.types,
            self.context.diagnostics,
        ) else {
            self.context
                .error("E-CONTRACT-ASSUME", "assume requires a string reason", span);
            return S::Error;
        };
        if reason.trim().is_empty() || reason.len() > 4096 {
            self.context.error(
                "E-CONTRACT-ASSUME",
                "assume requires a non-empty external justification of at most 4096 UTF-8 bytes",
                span,
            );
        }
        self.in_contract = true;
        let predicate = self.expression(predicate, Some(TyId::BOOL));
        self.in_contract = false;
        S::Assume(crate::contracts::SourceAssumption {
            predicate,
            reason: reason.into(),
        })
    }
}

impl Body<'_, '_> {
    pub(super) fn check_reference_alignment(&mut self, mut place: ExprId, span: Span) {
        for _ in 0..128 {
            let base = match self.expr(place).kind {
                H::Field { base, .. } | H::Index { base, .. } | H::VariantField { base, .. } => {
                    base
                }
                H::Group(inner) | H::Unary { operand: inner, .. } => {
                    place = inner;
                    continue;
                }
                _ => return,
            };
            let mut ty = self.ty(base);
            while let Ty::Reference { inner, .. } = self.type_kind(ty) {
                ty = *inner;
            }
            if let Ty::Named { definition, .. } = self.type_kind(ty) {
                let packed = self.context.definition(*definition).attributes.iter().any(|attribute| {
                    let name = self.context.symbols.get(attribute.name);
                    name == "packed" || name == "repr" && attribute.arguments.iter().any(|token|
                        matches!(token.kind, crate::syntax::token::TokenKind::Ident(name) if self.context.symbols.get(name) == "packed"))
                });
                if packed {
                    self.context.error("E-BORROW-ALIGN", "cannot establish reference alignment inside packed storage; use an unaligned raw-memory operation", span);
                    return;
                }
            }
            place = base;
        }
        self.context.error(
            "E-BORROW-ALIGN",
            "reference alignment analysis exceeded its projection depth budget",
            span,
        );
    }
}
