use super::*;
use crate::types::ConstId;

impl Context<'_> {
    /// Attribute expressions are parsed once with the source AST, then resolved
    /// in the annotated declaration's generic scope like array lengths.
    pub(super) fn check_attribute_constants(&mut self) {
        for index in 0..self.ast.items.len() {
            let (Some(owner), Some(module)) =
                (self.item_definitions[index], self.item_modules[index])
            else {
                continue;
            };
            let attributes: Vec<_> = self.ast.items[index]
                .attributes
                .iter()
                .enumerate()
                .filter(|(_, attribute)| self.symbols.get(attribute.name.symbol) == "align")
                .map(|(slot, attribute)| (slot, attribute.expression, attribute.span))
                .collect();
            for (slot, expression, span) in attributes {
                match self.alignment_constant(module, owner, expression, span) {
                    Ok(value) => {
                        if let Some(attribute) =
                            self.program.definitions[owner].attributes.get_mut(slot)
                        {
                            attribute.constant = Some(value);
                        }
                    }
                    Err(error) => self.error(error.code, error.message, error.span),
                }
            }
        }
    }

    fn alignment_constant(
        &mut self,
        module: ModuleId,
        owner: DefId,
        expression: Option<ast::ExprId>,
        span: Span,
    ) -> Result<ConstId, crate::ctfe::Error> {
        if !matches!(self.definition(owner).kind, D::Record | D::Union | D::Enum) {
            return Err(crate::ctfe::Error::new(
                "E-ATTR-TARGET",
                "alignment annotates a record, union or enum type",
                span,
            ));
        }
        let expression = expression.ok_or_else(|| {
            crate::ctfe::Error::new(
                "E-CONST-CONTEXT",
                "alignment requires one constant expression",
                span,
            )
        })?;
        let value = self.const_length(module, owner, expression, &HashMap::new())?;
        if let Some(value) = self.program.types.const_usize(value)
            && (!value.is_power_of_two() || value > 1 << 29)
        {
            return Err(crate::ctfe::Error::new(
                "E-CONST-EVAL",
                "alignment must be a supported power of two",
                span,
            ));
        }
        Ok(value)
    }
}
