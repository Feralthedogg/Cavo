use crate::mir::{BlockId, LocalId};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GuardPlanId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Dependency {
    Value(LocalId),
    Allocation(u32),
    Initialization(u32),
    Permission(u32),
    UnionTag(u32),
}

#[derive(Clone, Debug)]
pub struct GuardCheck {
    pub block: BlockId,
    pub success: BlockId,
    pub failure: BlockId,
    pub dependencies: BTreeMap<Dependency, u64>,
}

#[derive(Clone, Debug)]
pub struct GuardPlan {
    pub definition: crate::hir::DefId,
    pub checks: Vec<GuardCheck>,
    pub pure: bool,
    pub nosuspend: bool,
    pub noalloc: bool,
}

#[derive(Clone, Debug)]
pub struct GuardUseCertificate {
    pub plan: GuardPlanId,
    pub use_block: BlockId,
    pub dependencies: BTreeMap<Dependency, u64>,
}

impl GuardPlan {
    pub fn certify(
        &self,
        plan: GuardPlanId,
        use_block: BlockId,
        dominators: &BTreeSet<BlockId>,
        current: &BTreeMap<Dependency, u64>,
    ) -> Result<GuardUseCertificate, String> {
        if self.checks.is_empty() || !self.pure || !self.nosuspend || !self.noalloc {
            return Err(
                "guard evaluation is not established as pure, nosuspend and noalloc".into(),
            );
        }
        let mut dependencies = BTreeMap::new();
        for check in &self.checks {
            if check.success == check.failure
                || !dominators.contains(&check.block)
                || !dominators.contains(&check.success)
                || !dominators.contains(&use_block)
            {
                return Err("not all guard success paths dominate this use".into());
            }
            for (&dependency, &version) in &check.dependencies {
                if current.get(&dependency) != Some(&version)
                    || dependencies
                        .insert(dependency, version)
                        .is_some_and(|old| old != version)
                {
                    return Err("a guard dependency changed between its check and use".into());
                }
            }
        }
        Ok(GuardUseCertificate {
            plan,
            use_block,
            dependencies,
        })
    }
}
