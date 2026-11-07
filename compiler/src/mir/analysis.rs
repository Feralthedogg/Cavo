//! Coordinates independent MIR checks. Unknown coverage remains visible and
//! never becomes an authorization for native code generation.

use super::{Program, borrow, drop, effects};
use crate::{
    diagnostic::{Diagnostic, report},
    external::SummaryReport,
    hir,
    symbol::Interner,
};
use std::fmt::Write;

#[derive(Debug)]
pub struct Analysis {
    pub modular: crate::modular::Report,
    pub tasks: crate::tasks::Report,
    pub contracts: crate::contracts::Report,
    pub borrows: borrow::Report,
    pub effects: effects::Report,
    pub drops: drop::Program,
}

pub(crate) struct AnalysisError {
    pub code: &'static str,
    pub message: String,
}

pub(crate) fn analyze(
    mir: &Program,
    hir: &mut hir::Program,
    symbols: &Interner,
    external: &[SummaryReport],
    sources: &crate::source::SourceMap,
) -> Result<Analysis, AnalysisError> {
    let drops = drop::elaborate(mir, hir).map_err(|error| AnalysisError {
        code: "E-MIR-DROP",
        message: error.to_string(),
    })?;
    let effects =
        effects::analyze_with_cleanup(mir, hir, symbols, external, &drops).map_err(|error| {
            AnalysisError {
                code: "E-MIR-EFFECT",
                message: error.to_string(),
            }
        })?;
    let borrows =
        borrow::analyze_with_summaries(mir, hir, external).map_err(|error| AnalysisError {
            code: "E-MIR-BORROW",
            message: error.to_string(),
        })?;
    let tasks =
        crate::tasks::analyze(mir, hir, symbols, &effects.functions).map_err(|message| {
            AnalysisError {
                code: "E-TASK-LIMIT",
                message,
            }
        })?;
    let modular = crate::modular::analyze(mir, hir, &borrows, &effects);
    let contracts =
        crate::contracts::analyze(mir, hir, symbols, sources, external).map_err(|message| {
            AnalysisError {
                code: "E-CONTRACT-LIMIT",
                message,
            }
        })?;
    Ok(Analysis {
        modular,
        tasks,
        contracts,
        borrows,
        effects,
        drops,
    })
}

impl Analysis {
    pub(crate) fn diagnostics(&self, output: &mut Vec<Diagnostic>) {
        output.extend(self.modular.diagnostics.iter().cloned());
        output.extend(self.tasks.diagnostics.iter().cloned());
        self.contracts.diagnostics(output);
        for function in &self.borrows.functions {
            for finding in &function.findings {
                report(
                    output,
                    Diagnostic::error("E-MIR-BORROW", finding.kind.message(), finding.span),
                );
            }
        }
        for violation in &self.effects.violations {
            report(
                output,
                Diagnostic::error("E-EFFECT-BOUND", &violation.message, violation.span),
            );
        }
    }

    /// Inspection only: the reports must be recomputed after MIR changes.
    pub fn dump(&self) -> String {
        let mut output = self.borrows.dump();
        output.push_str(&self.contracts.dump());
        output.push_str(&self.tasks.dump());
        output.push_str("\nMIR effects / before runtime and checkpoint lowering\n");
        for function in &self.effects.functions {
            let _ = writeln!(
                output,
                "  function #{}: {:?}; bounded={:?}; fatal_abort={}",
                function.definition.0, function.effects, function.bounded, function.may_abort
            );
            let _ = writeln!(
                output,
                "    unknown={:?}; assumed={:?}",
                function.unknown, function.assumptions
            );
        }
        for pending in &self.effects.not_analyzed {
            let _ = writeln!(output, "  pending: {pending}");
        }
        output.push('\n');
        output.push_str(&self.drops.dump());
        output.push_str("\nTask backend: LLAM 3.0.0 / ABI 2.4 lacks cancellation-immune group drain; scoped task release is blocked.\n");
        output
    }
}
