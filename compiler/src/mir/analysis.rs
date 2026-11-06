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
) -> Result<Analysis, AnalysisError> {
    let effects = effects::analyze(mir, hir, symbols, external).map_err(|error| AnalysisError {
        code: "E-MIR-EFFECT",
        message: error.to_string(),
    })?;
    let borrows =
        borrow::analyze_with_summaries(mir, hir, external).map_err(|error| AnalysisError {
            code: "E-MIR-BORROW",
            message: error.to_string(),
        })?;
    let drops = drop::elaborate(mir, hir).map_err(|error| AnalysisError {
        code: "E-MIR-DROP",
        message: error.to_string(),
    })?;
    Ok(Analysis {
        borrows,
        effects,
        drops,
    })
}

impl Analysis {
    pub(crate) fn diagnostics(&self, output: &mut Vec<Diagnostic>) {
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
