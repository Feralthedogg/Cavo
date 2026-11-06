//! Domain-typed access to the existing contiguous arenas. `get_id` is for
//! unvalidated input; `at` preserves the invariant-checked indexing boundary.
//! The element fixes its ID type, so an ExprId cannot index a definition arena.
pub(crate) trait Element {
    type Id: Copy;
    fn index(id: Self::Id) -> usize;
}

pub(crate) trait Access<T: Element> {
    fn at(&self, id: T::Id) -> &T;
    fn at_mut(&mut self, id: T::Id) -> &mut T;
    fn get_id(&self, id: T::Id) -> Option<&T>;
    fn get_id_mut(&mut self, id: T::Id) -> Option<&mut T>;
}

impl<T: Element> Access<T> for [T] {
    fn at(&self, id: T::Id) -> &T {
        self.get_id(id).expect("validated arena identity")
    }
    fn at_mut(&mut self, id: T::Id) -> &mut T {
        self.get_id_mut(id).expect("validated arena identity")
    }
    fn get_id(&self, id: T::Id) -> Option<&T> {
        self.get(T::index(id))
    }
    fn get_id_mut(&mut self, id: T::Id) -> Option<&mut T> {
        self.get_mut(T::index(id))
    }
}

macro_rules! element {
    ($($value:ty => $id:ty),+ $(,)?) => {$(
        impl Element for $value {
            type Id = $id;
            fn index(id: Self::Id) -> usize { id.0 as usize }
        }
        impl std::ops::Index<$id> for Vec<$value> {
            type Output = $value;
            fn index(&self, id: $id) -> &Self::Output { self.as_slice().at(id) }
        }
        impl std::ops::IndexMut<$id> for Vec<$value> {
            fn index_mut(&mut self, id: $id) -> &mut Self::Output { self.as_mut_slice().at_mut(id) }
        }
        impl std::ops::Index<$id> for [$value] {
            type Output = $value;
            fn index(&self, id: $id) -> &Self::Output { self.at(id) }
        }
        impl std::ops::IndexMut<$id> for [$value] {
            fn index_mut(&mut self, id: $id) -> &mut Self::Output { self.at_mut(id) }
        }
        impl std::ops::Index<&$id> for Vec<$value> {
            type Output = $value;
            fn index(&self, id: &$id) -> &Self::Output { self.as_slice().at(*id) }
        }
        impl std::ops::Index<&$id> for [$value] {
            type Output = $value;
            fn index(&self, id: &$id) -> &Self::Output { self.at(*id) }
        }
    )+};
}

element! {
    crate::hir::Definition => crate::hir::DefId,
    crate::hir::Module => crate::hir::ModuleId,
    crate::hir::Expr => crate::hir::ExprId,
    crate::hir::Stmt => crate::hir::StmtId,
    crate::hir::Local => crate::hir::LocalId,
    crate::mir::Block => crate::mir::BlockId,
    crate::mir::Local => crate::mir::LocalId,
    crate::contracts::Evidence => crate::contracts::EvidenceId,
    crate::contracts::GuardPlan => crate::contracts::GuardPlanId,
    crate::syntax::ast::Expr => crate::syntax::ast::ExprId,
    crate::syntax::ast::Stmt => crate::syntax::ast::StmtId,
    crate::syntax::ast::Item => crate::syntax::ast::ItemId,
    crate::syntax::ast::Type => crate::syntax::ast::TypeId,
    crate::ctfe::Expr => crate::ctfe::ExprId,
    crate::mir::tasks::Block => crate::mir::tasks::ProtocolBlockId,
}
