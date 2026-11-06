use super::*;
use crate::types::{ConstKind, TypeContext};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Head {
    Named(DefId),
    Reference(bool),
    Pointer(bool),
    Array,
    Slice,
    Function,
    Other(std::mem::Discriminant<Ty>),
    Variable,
}

impl Context<'_> {
    pub(super) fn reject_overlapping_implementations(&mut self) {
        let mut by_head: HashMap<(Option<DefId>, Head), Vec<usize>> = HashMap::new();
        let mut by_trait: HashMap<Option<DefId>, Vec<usize>> = HashMap::new();
        let mut remaining = 200_000usize;
        for right in 0..self.program.implementations.len() {
            let implementation = &self.program.implementations[right];
            let trait_id = implementation
                .trait_ref
                .as_ref()
                .map(|reference| reference.definition);
            let head = head(self.program.types.get(implementation.target));
            let candidates: Vec<_> = if head == Head::Variable {
                by_trait.get(&trait_id).cloned().unwrap_or_default()
            } else {
                by_head
                    .get(&(trait_id, head))
                    .into_iter()
                    .flatten()
                    .chain(
                        by_head
                            .get(&(trait_id, Head::Variable))
                            .into_iter()
                            .flatten(),
                    )
                    .copied()
                    .collect()
            };
            for left in candidates {
                if remaining == 0 {
                    self.error(
                        "E-IMPL-LIMIT",
                        "implementation coherence exceeds its work limit",
                        self.definition(self.program.implementations[right].definition)
                            .span,
                    );
                    return;
                }
                if may_overlap(&self.program, left, right, &mut remaining) {
                    self.error(
                        "E-IMPL-OVERLAP",
                        "implementations may overlap; specialization is not supported",
                        self.definition(self.program.implementations[right].definition)
                            .span,
                    );
                }
            }
            by_head.entry((trait_id, head)).or_default().push(right);
            by_trait.entry(trait_id).or_default().push(right);
        }
    }
}

fn head(ty: &Ty) -> Head {
    match ty {
        Ty::Parameter { .. } => Head::Variable,
        Ty::Named { definition, .. }
        | Ty::Dynamic {
            trait_definition: definition,
            ..
        } => Head::Named(*definition),
        Ty::Reference { mutable, .. } => Head::Reference(*mutable),
        Ty::Pointer { constant, .. } => Head::Pointer(*constant),
        Ty::Array { .. } | Ty::SymbolicArray { .. } => Head::Array,
        Ty::Slice(_) => Head::Slice,
        Ty::Function { .. } | Ty::ForAll { .. } => Head::Function,
        _ => Head::Other(std::mem::discriminant(ty)),
    }
}

fn may_overlap(program: &hir::Program, left: usize, right: usize, remaining: &mut usize) -> bool {
    let left = &program.implementations[left];
    let right = &program.implementations[right];
    if left.trait_ref.is_none()
        && !left.methods.iter().any(|a| {
            right.methods.iter().any(|b| {
                program.definitions[a.implementation.0 as usize].name
                    == program.definitions[b.implementation.0 as usize].name
            })
        })
    {
        return false;
    }
    let mut matcher = Overlap {
        types: &program.types,
        remaining,
    };
    if !matcher.ty(left.target, right.target, 0) {
        return false;
    }
    match (&left.trait_ref, &right.trait_ref) {
        (Some(left), Some(right)) => matcher.arguments(&left.arguments, &right.arguments, 0),
        (None, None) => true,
        _ => false,
    }
}

struct Overlap<'a, 'b> {
    types: &'a TypeContext,
    remaining: &'b mut usize,
}
impl Overlap<'_, '_> {
    fn ty(&mut self, left: TyId, right: TyId, depth: usize) -> bool {
        if *self.remaining == 0 || depth >= 128 {
            return true;
        }
        *self.remaining -= 1;
        if left == right {
            return true;
        }
        let (left, right) = (self.types.get(left), self.types.get(right));
        // Both sides have universally quantified parameters. Treating only one
        // side as a pattern can miss intersections such as Pair<T,i32>/Pair<u32,U>.
        if matches!(left, Ty::Parameter { .. }) || matches!(right, Ty::Parameter { .. }) {
            return true;
        }
        if head(left) != head(right) {
            return false;
        }
        match (left, right) {
            (Ty::Named { arguments: a, .. }, Ty::Named { arguments: b, .. })
            | (Ty::Dynamic { arguments: a, .. }, Ty::Dynamic { arguments: b, .. }) => {
                self.arguments(a, b, depth + 1)
            }
            (Ty::Reference { inner: a, .. }, Ty::Reference { inner: b, .. })
            | (Ty::Pointer { inner: a, .. }, Ty::Pointer { inner: b, .. })
            | (Ty::Slice(a), Ty::Slice(b)) => self.ty(*a, *b, depth + 1),
            (
                Ty::Array {
                    inner: a,
                    length: al,
                },
                Ty::Array {
                    inner: b,
                    length: bl,
                },
            ) => al == bl && self.ty(*a, *b, depth + 1),
            (Ty::SymbolicArray { inner: a, .. }, Ty::Array { inner: b, .. })
            | (Ty::Array { inner: a, .. }, Ty::SymbolicArray { inner: b, .. })
            | (Ty::SymbolicArray { inner: a, .. }, Ty::SymbolicArray { inner: b, .. }) => {
                self.ty(*a, *b, depth + 1)
            }
            (Ty::Function { .. } | Ty::ForAll { .. }, Ty::Function { .. } | Ty::ForAll { .. }) => {
                true
            }
            _ => left == right,
        }
    }

    fn arguments(&mut self, left: &[GenericArg], right: &[GenericArg], depth: usize) -> bool {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(&left, &right)| match (left, right) {
                    (GenericArg::Type(left), GenericArg::Type(right)) => {
                        self.ty(left, right, depth + 1)
                    }
                    (GenericArg::Const(left), GenericArg::Const(right)) => match (
                        &self.types.const_term(left).kind,
                        &self.types.const_term(right).kind,
                    ) {
                        (ConstKind::Value(left), ConstKind::Value(right)) => left == right,
                        _ => true,
                    },
                    (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
                    _ => false,
                })
    }
}
