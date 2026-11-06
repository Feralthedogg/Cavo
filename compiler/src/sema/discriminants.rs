use super::*;
use crate::{
    ctfe,
    syntax::ast::BinaryOp,
    types::{ConstId, ConstKind, ConstTerm, GenericArg},
};

impl Context<'_> {
    pub(super) fn check_enum_discriminants(&mut self) {
        for index in 0..self.ast.items.len() {
            let ItemKind::Enum { variants, .. } = &self.ast.items[index].kind else {
                continue;
            };
            let Some(owner) = self.item_definitions[index] else {
                continue;
            };
            let module = self.definition(owner).module;
            let declarations: Vec<_> = variants
                .iter()
                .map(|variant| (variant.discriminant, variant.name.span))
                .collect();
            match self.discriminant_terms(owner, module, &declarations) {
                Ok(values) => {
                    if let Some(enumeration) = self
                        .program
                        .enums
                        .iter_mut()
                        .find(|item| item.definition == owner)
                    {
                        enumeration.discriminants = values;
                    }
                }
                Err(error) => self.report_constant(error),
            }
        }
    }

    fn discriminant_terms(
        &mut self,
        owner: DefId,
        module: ModuleId,
        declarations: &[(Option<ast::ExprId>, Span)],
    ) -> Result<Vec<ConstId>, ctfe::Error> {
        let mut values = Vec::with_capacity(declarations.len());
        let mut concrete = HashSet::new();
        for &(expression, span) in declarations {
            let value = if let Some(expression) = expression {
                self.const_length(module, owner, expression, &HashMap::new())?
            } else if let Some(&previous) = values.last() {
                self.next_discriminant(previous, span)?
            } else {
                self.program.types.const_value(0)
            };
            if let Some(number) = self.program.types.const_usize(value)
                && !concrete.insert(number)
            {
                return Err(ctfe::Error::new(
                    "E-ENUM-DISCRIMINANT",
                    "enum discriminants must be distinct",
                    span,
                ));
            }
            values.push(value);
        }
        Ok(values)
    }

    fn next_discriminant(&mut self, previous: ConstId, span: Span) -> Result<ConstId, ctfe::Error> {
        let one = self.program.types.const_value(1);
        let ty = self.program.types.const_term(one).ty;
        let next = self
            .program
            .types
            .intern_const(ConstTerm {
                ty,
                kind: ConstKind::Binary {
                    op: BinaryOp::Add,
                    left: previous,
                    right: one,
                },
            })
            .and_then(|id| self.program.types.normalize_const(id))
            .map_err(|error| ctfe::Error::new("E-CONST-EVAL", error.to_string(), span))?;
        Ok(next)
    }
}

/// HIR/MIR use variant identity. Only concrete layout turns it into a physical
/// unsigned tag, after evaluating the instance's const arguments.
pub(crate) fn enum_discriminants(
    program: &mut hir::Program,
    owner: DefId,
    arguments: &[GenericArg],
    limits: ctfe::Limits,
) -> Result<Vec<u64>, ctfe::Error> {
    let declaration = program
        .enums
        .iter()
        .find(|item| item.definition == owner)
        .ok_or_else(|| {
            ctfe::Error::new(
                "E-ENUM-DISCRIMINANT",
                "missing enum declaration",
                program.definitions[owner.0 as usize].span,
            )
        })?;
    let terms = declaration.discriminants.clone();
    let span = program.definitions[owner.0 as usize].span;
    let mut values = Vec::with_capacity(terms.len());
    let mut seen = HashSet::new();
    for term in terms {
        let term = program
            .types
            .const_substitute(term, owner, arguments)
            .map_err(|error| ctfe::Error::new("E-CONST-EVAL", error.to_string(), span))?;
        let term = ctfe::evaluate_term(program, term, limits)?;
        let value = program.types.const_usize(term).ok_or_else(|| {
            ctfe::Error::new(
                "E-CONST-CONTEXT",
                "enum discriminant must be a concrete usize",
                span,
            )
        })?;
        if !seen.insert(value) {
            return Err(ctfe::Error::new(
                "E-ENUM-DISCRIMINANT",
                "enum discriminants collide for this instance",
                span,
            ));
        }
        values.push(value);
    }
    Ok(values)
}
