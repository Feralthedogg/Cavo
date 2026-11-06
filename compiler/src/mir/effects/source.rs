//! Conservative source precheck needed before deferred bodies can be lowered.
//! Actual MIR effects are analyzed independently after cleanup construction.

use super::{Boundedness, FunctionEffects, InvariantError, Unknown, error, propagate};
use crate::{
    diagnostic::{Diagnostic, report},
    hir::{self, ExprKind as H, StmtKind as S},
    local::properties::Properties,
    source::Span,
};
use std::collections::BTreeSet;

#[derive(Debug)]
pub struct CleanupError {
    pub span: Span,
    pub message: String,
}

/// Snapshot for one validated, unchanged HIR program. Recompute after edits;
/// this is a source lowering precondition, not a reusable effect certificate.
pub struct CleanupCandidates {
    allowed: Vec<bool>,
    properties: Properties,
}

impl CleanupCandidates {
    pub fn allows(&self, definition: hir::DefId) -> bool {
        self.allowed
            .get(definition.0 as usize)
            .copied()
            .unwrap_or(false)
    }
}

pub fn cleanup_candidates(program: &mut hir::Program) -> Result<CleanupCandidates, InvariantError> {
    program
        .validate()
        .map_err(|problem| error(&format!("invalid cleanup input HIR: {problem}")))?;
    let properties = Properties::compute(program);
    let mut indices = vec![None; program.definitions.len()];
    for (index, function) in program.functions.iter().enumerate() {
        indices[function.definition.0 as usize] = Some(index);
    }
    let mut summaries = Vec::with_capacity(program.functions.len());
    let mut dependencies = Vec::with_capacity(program.functions.len());
    for function in &program.functions {
        let scan = Scan::run(
            program,
            function,
            &function.body,
            &properties,
            Mode::Function,
        );
        let (summary, calls) = summarize_source(function, scan, &indices, &properties, program);
        summaries.push(summary);
        dependencies.push(calls);
    }
    propagate(&dependencies, &mut summaries)?;
    let mut allowed = vec![false; program.definitions.len()];
    for summary in summaries {
        allowed[summary.definition.0 as usize] = summary.cleanup_safe();
    }
    for (&definition, contract) in &program.modular.functions {
        if crate::modular::usable(program, definition) {
            allowed[definition.0 as usize] = contract.cleanup_safe();
        }
    }
    Ok(CleanupCandidates {
        allowed,
        properties,
    })
}

fn summarize_source(
    function: &hir::Function,
    scan: Scan,
    indices: &[Option<usize>],
    properties: &Properties,
    program: &hir::Program,
) -> (FunctionEffects, Vec<usize>) {
    let mut summary = FunctionEffects::empty(function.definition);
    if scan.problem.is_some() || !function.clauses.is_empty() {
        summary.bounded = Boundedness::Unknown;
        summary.unknown.insert(Unknown::IndirectCall);
    }
    if scan.cyclic {
        summary.bounded = Boundedness::MayDiverge;
    }
    if function
        .locals
        .iter()
        .any(|local| properties.get(local.ty).may_drop)
    {
        summary.bounded = summary.bounded.max(Boundedness::Unknown);
        summary.unknown.insert(Unknown::DropGlue);
    }
    let mut calls = Vec::with_capacity(scan.calls.len());
    for definition in scan.calls {
        if crate::modular::usable(program, definition)
            && let Some(contract) = program.modular.functions.get(&definition)
        {
            summary.effects.extend(&contract.upper);
            if !contract.bounded {
                summary.bounded = summary.bounded.max(Boundedness::Unknown);
            }
            continue;
        }
        if let Some(index) = indices[definition.0 as usize] {
            calls.push(index);
        } else {
            summary.bounded = summary.bounded.max(Boundedness::Unknown);
            summary.unknown.insert(Unknown::ExternalCall);
        }
    }
    (summary, calls)
}

/// `function` and `body` must belong to the unchanged validated program used to
/// construct `candidates`. Actual lowered MIR receives independent analysis.
pub fn validate_cleanup_body(
    program: &hir::Program,
    function: &hir::Function,
    body: &hir::Block,
    candidates: &CleanupCandidates,
) -> Result<(), CleanupError> {
    let scan = Scan::run(
        program,
        function,
        body,
        &candidates.properties,
        Mode::Cleanup,
    );
    finish_cleanup(scan, body.span, candidates)
}

fn finish_cleanup(
    scan: Scan,
    span: Span,
    candidates: &CleanupCandidates,
) -> Result<(), CleanupError> {
    if let Some(problem) = scan.problem {
        return Err(problem);
    }
    if scan.cyclic {
        return Err(problem(
            span,
            "defer requires bounded cleanup; loops are not yet proven bounded",
        ));
    }
    if scan.calls.iter().any(|&callee| !candidates.allows(callee)) {
        return Err(problem(
            span,
            "defer calls must have established bounded nosuspend, nocancel, nopanic and noalloc effects",
        ));
    }
    Ok(())
}

pub(crate) fn validate_defers(program: &mut hir::Program, diagnostics: &mut Vec<Diagnostic>) {
    let has_defer = program.functions.iter().any(|function| {
        function
            .statements
            .iter()
            .any(|statement| matches!(statement.kind, S::Defer { .. }))
    });
    if !has_defer {
        return;
    }
    let candidates = match cleanup_candidates(program) {
        Ok(candidates) => candidates,
        Err(error) => {
            if let Some(function) = program.functions.first() {
                report(
                    diagnostics,
                    Diagnostic::error("E-DEFER-EFFECT", error.to_string(), function.body.span),
                );
            }
            return;
        }
    };
    for function in &program.functions {
        for statement in &function.statements {
            let S::Defer { body, .. } = &statement.kind else {
                continue;
            };
            if let Err(error) = validate_cleanup_body(program, function, body, &candidates) {
                report(
                    diagnostics,
                    Diagnostic::error("E-DEFER-EFFECT", error.message, error.span),
                );
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Function,
    Cleanup,
}
enum Work {
    Statement(hir::StmtId),
    Expression(hir::ExprId),
}

struct Scan {
    calls: BTreeSet<hir::DefId>,
    cyclic: bool,
    problem: Option<CleanupError>,
}

struct Walker<'a> {
    program: &'a hir::Program,
    function: &'a hir::Function,
    mode: Mode,
    pending: Vec<Work>,
    seen_statements: Vec<bool>,
    seen_expressions: Vec<bool>,
    facts: &'a Properties,
    scan: Scan,
}

impl Scan {
    fn run(
        program: &hir::Program,
        function: &hir::Function,
        body: &hir::Block,
        facts: &Properties,
        mode: Mode,
    ) -> Self {
        Walker::new(program, function, body, mode, facts).run()
    }
}

impl<'a> Walker<'a> {
    fn new(
        program: &'a hir::Program,
        function: &'a hir::Function,
        body: &hir::Block,
        mode: Mode,
        facts: &'a Properties,
    ) -> Self {
        Self {
            program,
            function,
            mode,
            facts,
            pending: body
                .statements
                .iter()
                .copied()
                .map(Work::Statement)
                .collect(),
            seen_statements: vec![false; function.statements.len()],
            seen_expressions: vec![false; function.expressions.len()],
            scan: Scan {
                calls: BTreeSet::new(),
                cyclic: false,
                problem: None,
            },
        }
    }

    fn run(mut self) -> Scan {
        let mut remaining = 200_000usize;
        while let Some(work) = self.pending.pop() {
            let Some(next) = remaining.checked_sub(1) else {
                self.scan.problem = Some(problem(
                    self.function.body.span,
                    "cleanup effect analysis exceeds its work limit",
                ));
                break;
            };
            remaining = next;
            let outcome = match work {
                Work::Statement(id) => self.statement(id),
                Work::Expression(id) => self.expression(id),
            };
            if let Err(error) = outcome {
                self.scan.problem = Some(error);
                break;
            }
        }
        self.scan
    }

    fn block(&mut self, body: &hir::Block) {
        self.pending
            .extend(body.statements.iter().copied().map(Work::Statement));
    }
    fn expression_work(&mut self, id: hir::ExprId) {
        self.pending.push(Work::Expression(id));
    }

    fn statement(&mut self, id: hir::StmtId) -> Result<(), CleanupError> {
        let statement = &self.function.statements[id];
        if std::mem::replace(&mut self.seen_statements[id.0 as usize], true) {
            return Ok(());
        }
        match &statement.kind {
            S::Declare { local, initializer } => {
                self.check_drop_type(self.function.locals[local].ty, statement.span)?;
                if let Some(value) = initializer {
                    self.expression_work(*value);
                }
            }
            S::Expression(value) => self.expression_work(*value),
            S::Assign { target, value, .. } => {
                self.expression_work(*target);
                self.expression_work(*value);
            }
            S::Return(value) if self.mode == Mode::Function => {
                if let Some(value) = value {
                    self.expression_work(*value);
                }
            }
            S::Block(body) => self.block(body),
            S::If {
                condition,
                then_block,
                otherwise,
            } => {
                self.expression_work(*condition);
                self.block(then_block);
                if let Some(otherwise) = otherwise {
                    self.pending.push(Work::Statement(*otherwise));
                }
            }
            S::Defer { captures, body } => {
                for (_, initializer) in captures {
                    self.expression_work(*initializer);
                }
                self.block(body);
            }
            S::While { .. } | S::For { .. } | S::ForIn { .. } => self.scan.cyclic = true,
            S::Empty => {}
            S::Break | S::Continue if self.mode == Mode::Function => {}
            _ => {
                return Err(problem(
                    statement.span,
                    "defer cannot return or transfer control outside its cleanup",
                ));
            }
        }
        Ok(())
    }

    fn expression(&mut self, id: hir::ExprId) -> Result<(), CleanupError> {
        if std::mem::replace(&mut self.seen_expressions[id.0 as usize], true) {
            return Ok(());
        }
        let expression = &self.function.expressions[id];
        self.check_drop_type(expression.ty, expression.span)?;
        match &expression.kind {
            H::Spawn { .. } => {
                return Err(problem(
                    expression.span,
                    "task admission cannot execute in bounded cleanup",
                ));
            }
            H::Call {
                callee, arguments, ..
            } => {
                self.call(*callee, expression.span)?;
                self.pending
                    .extend(arguments.iter().copied().map(Work::Expression));
            }
            H::Unary { operand, .. } | H::Group(operand) | H::CoerceArrayToSlice(operand) => {
                self.expression_work(*operand)
            }
            H::Binary { left, right, .. }
            | H::Index {
                base: left,
                index: right,
            } => {
                self.expression_work(*left);
                self.expression_work(*right);
            }
            H::Field { base, .. } | H::VariantField { base, .. } | H::IsVariant { base, .. } => {
                self.expression_work(*base)
            }
            H::Array(values) => self
                .pending
                .extend(values.iter().copied().map(Work::Expression)),
            H::Repeat { value, .. } | H::RepeatConst { value, .. } | H::DynCoerce { value, .. } => {
                self.expression_work(*value)
            }
            H::Record { fields, .. } => self
                .pending
                .extend(fields.iter().map(|(_, value)| Work::Expression(*value))),
            H::Match { .. } | H::BlockValue { .. } => self.control_expression(&expression.kind),
            H::DynCall { .. } => {
                return Err(problem(
                    expression.span,
                    "source cleanup requires an established dynamic dispatch witness",
                ));
            }
            H::Constant(_) | H::ConstTerm(_) | H::Local(_) | H::Definition(_) => {}
            H::Old(_) | H::Error => {
                return Err(problem(
                    expression.span,
                    "defer contains an unverified expression effect",
                ));
            }
        }
        Ok(())
    }

    fn control_expression(&mut self, expression: &H) {
        match expression {
            H::Match { subject, arms, .. } => {
                self.expression_work(*subject);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expression_work(guard);
                    }
                    self.expression_work(arm.value);
                }
            }
            H::BlockValue { body, value } => {
                self.block(body);
                if let Some(value) = value {
                    self.expression_work(*value);
                }
            }
            _ => unreachable!("structured expression"),
        }
    }

    fn call(&mut self, mut callee: hir::ExprId, span: Span) -> Result<(), CleanupError> {
        while let H::Group(inner) = self.function.expressions[callee].kind {
            callee = inner;
        }
        let H::Definition(definition) = self.function.expressions[callee].kind else {
            return Err(problem(
                span,
                "defer cannot call a function with unknown indirect effects",
            ));
        };
        if matches!(
            self.program.definitions[definition].kind,
            hir::DefinitionKind::Variant { .. }
        ) {
            return Ok(());
        }
        self.scan.calls.insert(definition);
        Ok(())
    }

    fn check_drop_type(&self, ty: crate::types::TyId, span: Span) -> Result<(), CleanupError> {
        let may_drop = self.facts.get(ty).may_drop;
        if may_drop {
            return Err(problem(
                span,
                "cleanup requires established bounded Drop effects for every temporary and local",
            ));
        }
        Ok(())
    }
}

fn problem(span: Span, message: &str) -> CleanupError {
    CleanupError {
        span,
        message: message.into(),
    }
}
