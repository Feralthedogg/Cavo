use super::*;

#[derive(Clone)]
enum Cover {
    Any,
    Bool(bool),
    Variant(DefId, Vec<Cover>),
    Scalar,
}

struct Constructor {
    variant: Option<DefId>,
    boolean: Option<bool>,
    fields: Vec<TyId>,
}

impl Body<'_, '_> {
    pub(super) fn check_match_coverage(&mut self, ty: TyId, arms: &[hir::MatchArm], span: Span) {
        let rows = arms
            .iter()
            .filter(|arm| arm.guard.is_none())
            .map(|arm| vec![cover(&arm.pattern)])
            .collect();
        match self.covered(&[ty], rows, 0, &mut 200_000) {
            Some(true) => {}
            Some(false) => self.context.error(
                "E-MATCH-EXHAUSTIVE",
                "match coverage is not established; add the missing cases or a wildcard arm",
                span,
            ),
            None => self.context.error(
                "E-MATCH-LIMIT",
                "pattern exhaustiveness exceeds its resource limit",
                span,
            ),
        }
    }

    fn covered(
        &mut self,
        columns: &[TyId],
        rows: Vec<Vec<Cover>>,
        depth: usize,
        remaining: &mut usize,
    ) -> Option<bool> {
        *remaining = remaining.checked_sub(rows.len() + 1)?;
        if depth >= 128 {
            return None;
        }
        let Some((&ty, rest)) = columns.split_first() else {
            return Some(!rows.is_empty());
        };
        if rows.is_empty() {
            return Some(
                self.constructors(ty)
                    .is_some_and(|values| values.is_empty()),
            );
        }
        let Some(constructors) = self.constructors(ty) else {
            let defaults = rows.into_iter().filter_map(default_row).collect();
            return self.covered(rest, defaults, depth + 1, remaining);
        };
        for constructor in constructors {
            if constructor
                .fields
                .len()
                .saturating_add(rest.len())
                .saturating_mul(rows.len())
                > *remaining
            {
                return None;
            }
            let mut columns = constructor.fields.clone();
            columns.extend_from_slice(rest);
            let specialized = rows
                .iter()
                .filter_map(|row| specialize(row, &constructor))
                .collect();
            if !self.covered(&columns, specialized, depth + 1, remaining)? {
                return Some(false);
            }
        }
        Some(true)
    }

    fn constructors(&mut self, ty: TyId) -> Option<Vec<Constructor>> {
        if ty == TyId::BOOL {
            return Some(
                [false, true]
                    .into_iter()
                    .map(|value| Constructor {
                        variant: None,
                        boolean: Some(value),
                        fields: Vec::new(),
                    })
                    .collect(),
            );
        }
        let Ty::Named { definition, .. } = self.type_kind(ty) else {
            return None;
        };
        let variants = self
            .context
            .program
            .enums
            .iter()
            .find(|enumeration| enumeration.definition == *definition)?
            .variants
            .clone();
        Some(
            variants
                .into_iter()
                .map(|variant| Constructor {
                    variant: Some(variant),
                    boolean: None,
                    fields: self.variant_fields(ty, variant),
                })
                .collect(),
        )
    }
}

fn cover(pattern: &Pattern) -> Cover {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Binding { .. } => Cover::Any,
        PatternKind::Literal(hir::Constant::Bool(value)) => Cover::Bool(*value),
        PatternKind::Variant { definition, fields } => {
            Cover::Variant(*definition, fields.iter().map(cover).collect())
        }
        PatternKind::Literal(_) => Cover::Scalar,
    }
}

fn default_row(mut row: Vec<Cover>) -> Option<Vec<Cover>> {
    if !matches!(row.first(), Some(Cover::Any)) {
        return None;
    }
    row.remove(0);
    Some(row)
}

fn specialize(row: &[Cover], constructor: &Constructor) -> Option<Vec<Cover>> {
    let (head, tail) = row.split_first()?;
    let mut result = match head {
        Cover::Any => vec![Cover::Any; constructor.fields.len()],
        Cover::Bool(value) if constructor.boolean == Some(*value) => Vec::new(),
        Cover::Variant(variant, fields) if constructor.variant == Some(*variant) => fields.clone(),
        _ => return None,
    };
    result.extend_from_slice(tail);
    Some(result)
}
