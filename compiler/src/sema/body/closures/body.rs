use super::*;
use crate::{local::properties::Properties, types::Region};

impl Body<'_, '_> {
    pub(super) fn closure_body(
        &mut self,
        declaration: &Declaration,
        captures: &[Capture],
        syntax: &Syntax<'_>,
        outer: HashSet<Symbol>,
    ) -> (hir::Function, ClosureKind) {
        let parent = self.definition;
        let inherited_types: Vec<_> = self
            .generic_types
            .iter()
            .map(|(&name, &ty)| (name, ty))
            .collect();
        let mut checker = Body::new(
            self.context,
            self.module,
            declaration.function,
            syntax.body.span,
        );
        checker.inherit_closure_types(parent, &inherited_types, syntax.body.span);
        checker.uncaptured = outer;
        checker.prepare_closure_bindings(parent, captures, syntax);
        let (body, falls) = checker.block(syntax.body);
        checker.function.body = body;
        if matches!(checker.return_mode, ReturnMode::InferClosure) {
            checker.infer_closure_result(syntax.body.span);
        }
        if falls && !matches!(checker.function.result, TyId::VOID | TyId::ERROR) {
            checker.context.error(
                "E-RETURN-MISSING",
                "not every closure path returns a value",
                syntax.body.span,
            );
        }
        let kind = if checker.consumes_capture(captures.len()) {
            ClosureKind::FnOnce
        } else {
            checker.closure_borrow_kind(captures.len())
        };
        checker.install_environment(declaration, captures, kind);
        (checker.function, kind)
    }

    fn inherit_closure_types(&mut self, parent: DefId, bindings: &[(Symbol, TyId)], span: Span) {
        let arguments = self
            .context
            .program
            .types
            .generic_arguments(self.definition);
        for &(name, ty) in bindings {
            let ty = self.closure_substitute(ty, parent, &arguments, span);
            self.generic_types.insert(name, ty);
        }
    }

    fn prepare_closure_bindings(
        &mut self,
        parent: DefId,
        captures: &[Capture],
        syntax: &Syntax<'_>,
    ) {
        self.function.result = syntax
            .result
            .map_or(TyId::ERROR, |ty| self.resolve_type(ty));
        if syntax.result.is_none() {
            self.return_mode = ReturnMode::InferClosure;
        }
        let arguments = self
            .context
            .program
            .types
            .generic_arguments(self.definition);
        for capture in captures {
            let ty =
                self.closure_substitute(capture.body_ty, parent, &arguments, capture.name.span);
            self.bind(
                capture.name,
                ty,
                capture.mode != ast::CaptureMode::Shared,
                Init::Initialized,
            );
            self.uncaptured.remove(&capture.name.symbol);
        }
        for parameter in syntax.parameters {
            let ty = self.resolve_type(parameter.ty);
            let local = self.bind(parameter.name, ty, true, Init::Initialized);
            self.function.parameters.push(local);
        }
    }

    fn infer_closure_result(&mut self, span: Span) {
        let returned: Vec<_> = self
            .function
            .statements
            .iter()
            .filter_map(|statement| match statement.kind {
                S::Return(value) => Some(value),
                _ => None,
            })
            .collect();
        let result = returned
            .first()
            .copied()
            .flatten()
            .map_or(TyId::VOID, |value| self.ty(value));
        for value in returned {
            let actual = value.map_or(TyId::VOID, |value| self.ty(value));
            if !self.context.program.types.compatible(actual, result) {
                self.mismatch(
                    actual,
                    result,
                    value.map_or(span, |value| self.expr(value).span),
                );
            }
        }
        self.function.result = result;
    }

    fn consumes_capture(&mut self, captures: usize) -> bool {
        let moved: Vec<_> = self
            .function
            .expressions
            .iter()
            .filter_map(|expression| {
                if let H::Unary {
                    op: U::Move,
                    operand,
                } = expression.kind
                    && self.capture_root(operand, captures).is_some()
                {
                    Some(self.ty(operand))
                } else {
                    None
                }
            })
            .collect();
        // Most closures only read/borrow captures. They do not need a repeated
        // whole-program property pass merely to establish that no move occurs.
        if moved.is_empty() {
            return false;
        }
        let properties = Properties::compute(&mut self.context.program);
        moved.into_iter().any(|ty| !properties.get(ty).copy)
    }

    fn closure_borrow_kind(&self, captures: usize) -> ClosureKind {
        let mut kind = ClosureKind::Fn;
        for expression in &self.function.expressions {
            match &expression.kind {
                H::Unary {
                    op: U::BorrowMut,
                    operand,
                } if self.capture_root(*operand, captures).is_some() => {
                    kind = ClosureKind::FnMut;
                }
                H::Call {
                    arguments,
                    parameter_types,
                    ..
                }
                | H::DynCall {
                    arguments,
                    parameter_types,
                    ..
                } => {
                    for (&argument, &parameter) in arguments.iter().zip(parameter_types) {
                        if matches!(
                            self.type_kind(parameter),
                            Ty::Reference { mutable: true, .. }
                        ) && self.capture_root(argument, captures).is_some()
                        {
                            kind = ClosureKind::FnMut;
                        }
                    }
                }
                _ => {}
            }
        }
        for statement in &self.function.statements {
            if let S::Assign { target, .. } = statement.kind
                && self.capture_root(target, captures).is_some()
            {
                kind = ClosureKind::FnMut;
            }
        }
        kind
    }

    fn capture_root(&self, mut expression: ExprId, captures: usize) -> Option<usize> {
        for _ in 0..256 {
            expression = match self.expr(expression).kind {
                H::Local(local) => {
                    return ((local.0 as usize) < captures).then_some(local.0 as usize);
                }
                H::Group(inner)
                | H::CoerceArrayToSlice(inner)
                | H::DynCoerce { value: inner, .. }
                | H::Unary { operand: inner, .. } => inner,
                H::Field { base, .. } | H::Index { base, .. } => base,
                _ => return None,
            };
        }
        None
    }

    fn install_environment(
        &mut self,
        declaration: &Declaration,
        captures: &[Capture],
        kind: ClosureKind,
    ) {
        let environment = self.environment_type(declaration.environment, self.definition);
        let receiver = if kind == ClosureKind::FnOnce {
            environment
        } else {
            let region = self.context.program.types.fresh_region();
            self.context.program.types.intern(Ty::Reference {
                region,
                mutable: kind == ClosureKind::FnMut,
                inner: environment,
            })
        };
        let local = LocalId(self.function.locals.len() as u32);
        self.function.locals.push(hir::Local {
            name: self.context.definition(self.definition).name,
            ty: receiver,
            mutable: kind != ClosureKind::Fn,
            span: self.function.body.span,
        });
        self.function.parameters.insert(0, local);
        self.link_closure_result(captures, receiver);
        self.rewrite_environment(declaration, captures, local, receiver);
        let parameters = self
            .function
            .parameters
            .iter()
            .map(|local| self.function.locals[local].ty)
            .collect();
        let signature = self.context.program.types.intern(Ty::Function {
            parameters,
            result: self.function.result,
        });
        self.context.program.definitions[self.definition].ty = signature;
    }

    fn rewrite_environment(
        &mut self,
        declaration: &Declaration,
        captures: &[Capture],
        local: LocalId,
        receiver: TyId,
    ) {
        let count = self.function.expressions.len();
        let arguments = self
            .context
            .program
            .types
            .generic_arguments(self.definition);
        let field_types: Vec<_> = self
            .context
            .program
            .records
            .iter()
            .find(|record| record.definition == declaration.environment)
            .expect("declared closure environment")
            .fields
            .iter()
            .map(|field| field.ty)
            .collect();
        let fields: Vec<_> = field_types
            .into_iter()
            .map(|ty| {
                self.closure_substitute(
                    ty,
                    declaration.environment,
                    &arguments,
                    self.function.body.span,
                )
            })
            .collect();
        for index in 0..count {
            let H::Local(captured) = self.function.expressions[index].kind else {
                continue;
            };
            let Some(capture) = captures.get(captured.0 as usize) else {
                continue;
            };
            let span = self.function.expressions[index].span;
            let base = self.add_expr(H::Local(local), receiver, span);
            let field = H::Field {
                base,
                index: captured.0,
            };
            self.function.expressions[index].kind = if capture.mode == ast::CaptureMode::Move {
                field
            } else {
                let operand = self.add_expr(field, fields[captured.0 as usize], span);
                H::Unary {
                    op: U::Dereference,
                    operand,
                }
            };
        }
    }

    fn link_closure_result(&mut self, captures: &[Capture], receiver: TyId) {
        let Ty::Reference {
            region: result_region,
            mutable,
            inner,
        } = *self.type_kind(self.function.result)
        else {
            return;
        };
        let mut regions = HashSet::new();
        for statement in &self.function.statements {
            if let S::Return(Some(value)) = statement.kind
                && let Some(region) = self.returned_region(value, captures, receiver)
            {
                regions.insert(region);
            }
        }
        if let Ty::Reference { region, .. } = *self.type_kind(receiver)
            && regions.contains(&region)
        {
            self.context.error("E-CLOSURE-ESCAPE", "a closure result cannot borrow its owned environment; capture the source by reference instead", self.function.body.span);
            return;
        }
        if matches!(result_region, Region::Infer(_)) && regions.len() == 1 {
            let region = *regions.iter().next().expect("one result region");
            self.function.result = self.context.program.types.intern(Ty::Reference {
                region,
                mutable,
                inner,
            });
        }
    }

    fn returned_region(
        &self,
        mut value: ExprId,
        captures: &[Capture],
        receiver: TyId,
    ) -> Option<Region> {
        for _ in 0..256 {
            match self.expr(value).kind {
                H::Group(inner)
                | H::Unary {
                    op: U::Move,
                    operand: inner,
                } => value = inner,
                H::Unary {
                    op: U::Borrow | U::BorrowMut,
                    operand,
                } => return self.borrowed_region(operand, captures, receiver),
                _ => return reference_region(self.type_kind(self.ty(value))),
            }
        }
        None
    }

    fn borrowed_region(
        &self,
        mut place: ExprId,
        captures: &[Capture],
        receiver: TyId,
    ) -> Option<Region> {
        for _ in 0..256 {
            place = match self.expr(place).kind {
                H::Local(local) => {
                    let capture = captures.get(local.0 as usize)?;
                    let ty = if capture.mode != ast::CaptureMode::Shared {
                        receiver
                    } else {
                        capture.storage_ty
                    };
                    return reference_region(self.type_kind(ty));
                }
                H::Unary {
                    op: U::Dereference,
                    operand,
                } => return self.captured_referent_region(operand, captures, receiver),
                H::Field { base, .. } | H::Index { base, .. } => {
                    if reference_region(self.type_kind(self.ty(base))).is_some() {
                        return self.captured_referent_region(base, captures, receiver);
                    }
                    base
                }
                H::Group(inner) => inner,
                _ => return None,
            };
        }
        None
    }

    fn captured_referent_region(
        &self,
        operand: ExprId,
        captures: &[Capture],
        receiver: TyId,
    ) -> Option<Region> {
        let ty = self.type_kind(self.ty(operand));
        if matches!(ty, Ty::Reference { mutable: true, .. }) {
            let capture = captures.get(self.capture_root(operand, captures.len())?)?;
            let owner = if capture.mode == ast::CaptureMode::Shared {
                capture.storage_ty
            } else {
                receiver
            };
            return reference_region(self.type_kind(owner));
        }
        reference_region(ty)
    }
}

fn reference_region(ty: &Ty) -> Option<Region> {
    if let Ty::Reference { region, .. } = ty {
        Some(*region)
    } else {
        None
    }
}
