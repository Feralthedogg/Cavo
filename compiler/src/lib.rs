//! Frontend artifacts are owned by a compilation and contain no LLVM/runtime state.

pub mod ctfe;
pub mod diagnostic;
pub mod driver;
pub mod external;
mod graph;
pub mod hir;
pub mod layout;
pub mod local;
pub mod mir;
pub mod mono;
pub mod sema;
pub mod source;
pub mod symbol;
pub mod syntax;
pub mod types;

use diagnostic::Diagnostic;
use source::{FileId, SourceMap};
use symbol::Interner;
use syntax::ast::Ast;

#[derive(Debug, Default)]
pub struct Compilation {
    pub sources: SourceMap,
    pub symbols: Interner,
    pub ast: Ast,
    pub diagnostics: Vec<Diagnostic>,
    pub local_analysis: Option<local::Report>,
    pub mir_analysis: Option<mir::Analysis>,
    pub external_summaries: external::Summaries,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AnalysisPath {
    SourceCfg,
    ExecutionMir,
}
struct CheckedInput {
    program: hir::Program,
    summaries: Vec<external::SummaryReport>,
    path: AnalysisPath,
}

impl Compilation {
    pub fn parse(&mut self, file: FileId) {
        let tokens = syntax::lexer::lex(
            self.sources.file(file),
            &mut self.symbols,
            &mut self.diagnostics,
        );
        syntax::parser::parse(
            file,
            &tokens,
            &self.symbols,
            &mut self.ast,
            &mut self.diagnostics,
        );
    }

    pub fn check(&mut self) -> Option<hir::Program> {
        let mut input = self.prepare_input()?;
        if input.path == AnalysisPath::ExecutionMir {
            self.build_mir(&mut input.program, &input.summaries)?;
        }
        Some(input.program)
    }

    fn prepare_input(&mut self) -> Option<CheckedInput> {
        let mut program = self.check_types()?;
        let bindings = self.external_summaries.bind(
            &program,
            &self.symbols,
            &self.sources,
            &mut self.diagnostics,
        );
        if !self.diagnostics.is_empty() {
            return None;
        }
        let path = if sema::requires_execution_mir(&mut program) {
            sema::validate_moves(&mut program, &mut self.diagnostics);
            AnalysisPath::ExecutionMir
        } else {
            AnalysisPath::SourceCfg
        };
        let summaries = if path == AnalysisPath::ExecutionMir {
            bindings.reports
        } else {
            self.check_local(&mut program, bindings)?;
            self.local_analysis
                .as_ref()
                .expect("local report")
                .summaries
                .clone()
        };
        self.diagnostics.is_empty().then_some(CheckedInput {
            program,
            summaries,
            path,
        })
    }

    fn check_local(
        &mut self,
        program: &mut hir::Program,
        bindings: external::Bindings,
    ) -> Option<()> {
        let report = local::analyze_with_summaries(
            program,
            &mut self.diagnostics,
            bindings,
            &self.external_summaries,
        );
        if let Err(error) = report.validate(program) {
            self.frontend_error(
                "E-LOCAL-INTERNAL",
                format!("invalid local analysis artifact: {error}"),
            );
        }
        self.local_analysis = Some(report);
        self.diagnostics.is_empty().then_some(())
    }

    /// Structured expressions are checked on their actual execution CFG. The
    /// template reports retain unresolved generic obligations and are not a
    /// certificate for native execution.
    pub fn check_mir(&mut self) -> Option<(hir::Program, mir::Program)> {
        let mut input = self.prepare_input()?;
        let mir = self.build_mir(&mut input.program, &input.summaries)?;
        Some((input.program, mir))
    }

    pub fn check_monomorphized(&mut self) -> Option<mono::Program> {
        let mut input = self.prepare_input()?;
        self.build_mir(&mut input.program, &input.summaries)?;
        let roots = mono::default_roots(&input.program);
        let context = mono::Context {
            symbols: &self.symbols,
            sources: &self.sources,
            external: &input.summaries,
        };
        match mono::instantiate(&input.program, &roots, context, mono::Options::default()) {
            Ok(program) => Some(program),
            Err(error) => {
                self.diagnostics
                    .push(Diagnostic::error(error.code, error.message, error.span));
                None
            }
        }
    }

    fn build_mir(
        &mut self,
        hir: &mut hir::Program,
        summaries: &[external::SummaryReport],
    ) -> Option<mir::Program> {
        let mir = match mir::lower(hir) {
            Ok(program) => program,
            Err(error) => {
                self.diagnostics
                    .push(Diagnostic::error("E-MIR-STAGE", error.message, error.span));
                return None;
            }
        };
        if let Err(error) = mir.validate(hir) {
            if let Some(code) = error.user_code() {
                let span = error.span.unwrap_or_else(|| {
                    self.sources
                        .files()
                        .first()
                        .map_or(source::Span::new(FileId(0), 0, 0), |file| {
                            source::Span::new(file.id, 0, 0)
                        })
                });
                self.diagnostics
                    .push(Diagnostic::error(code, error.to_string(), span));
            } else {
                self.frontend_error("E-MIR-INTERNAL", format!("invalid MIR artifact: {error}"));
            }
            return None;
        }
        match mir::analyze(&mir, hir, &self.symbols, summaries) {
            Ok(analysis) => {
                analysis.diagnostics(&mut self.diagnostics);
                self.mir_analysis = Some(analysis);
            }
            Err(error) => {
                self.frontend_error(error.code, error.message);
                return None;
            }
        }
        self.diagnostics.is_empty().then_some(mir)
    }

    fn frontend_error(&mut self, code: &'static str, message: String) {
        if let Some(source) = self.sources.files().first() {
            self.diagnostics.push(Diagnostic::error(
                code,
                message,
                source::Span::new(source.id, 0, 0),
            ));
        }
    }

    pub fn add_external_summary(
        &mut self,
        path: impl AsRef<std::path::Path>,
        text: String,
    ) -> Option<external::Digest> {
        self.external_summaries
            .add(path, text, &mut self.sources, &mut self.diagnostics)
    }
    pub fn trust_summary(&mut self, digest: external::Digest) {
        self.external_summaries.trust(digest);
    }

    /// Typed interface extraction is not borrow/effect verification.
    pub fn check_types(&mut self) -> Option<hir::Program> {
        self.local_analysis = None;
        self.mir_analysis = None;
        if !self.diagnostics.is_empty() {
            return None;
        }
        let mut output = sema::check(
            &self.ast,
            &self.sources,
            &self.symbols,
            &mut self.diagnostics,
        );
        if !self.diagnostics.is_empty() {
            return None;
        }
        if let Err(error) = output.validate() {
            if let Some(source) = self.sources.files().first() {
                self.diagnostics.push(Diagnostic::error(
                    "E-HIR-INTERNAL",
                    format!("internal frontend invariant failed: {error}"),
                    source::Span::new(source.id, 0, 0),
                ));
            }
            return None;
        }
        sema::validate_destructors(&mut output, &mut self.diagnostics);
        mir::effects::validate_defers(&mut output, &mut self.diagnostics);
        if !self.diagnostics.is_empty() {
            return None;
        }
        Some(output)
    }
}
