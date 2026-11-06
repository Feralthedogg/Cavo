use super::*;
use crate::contracts::Intrinsic;

impl<R: Reporter> Evaluator<'_, '_, R> {
    pub(super) fn memory_intrinsic(
        &mut self,
        role: Intrinsic,
        arguments: &[Value],
        destination: &Place,
        normal: BlockId,
        mut state: State,
    ) -> Vec<(BlockId, State)> {
        let source = arguments.first().cloned().unwrap_or_default();
        let mut value = Value::default();
        match role {
            Intrinsic::AsPtr | Intrinsic::AsMutPtr | Intrinsic::Offset => value = source,
            Intrinsic::Read | Intrinsic::ReadUnaligned | Intrinsic::Take => {
                let target = self.pointer_target(&source, &state);
                self.check(
                    &target,
                    if role == Intrinsic::Take {
                        Access::Move
                    } else {
                        Access::Read
                    },
                    &state,
                );
                value = self.read_value(&target, self.place_type(destination), &state);
                if role == Intrinsic::Take {
                    clear_value(&target, &mut state);
                }
            }
            Intrinsic::Initialize | Intrinsic::Replace | Intrinsic::WriteUnaligned => {
                let target = self.pointer_target(&source, &state);
                self.check(&target, Access::Write, &state);
                self.store(
                    &target,
                    arguments.get(1).cloned().unwrap_or_default(),
                    &mut state,
                );
            }
            Intrinsic::Deallocate => {
                let target = self.pointer_target(&source, &state);
                self.check(&target, Access::End, &state);
                clear_value(&target, &mut state);
            }
            Intrinsic::Allocate | Intrinsic::Length => {}
            _ => unreachable!("task intrinsics have a separate transfer"),
        }
        let target = self.resolve(destination, &state);
        self.store(&target, value, &mut state);
        vec![(normal, state)]
    }

    fn pointer_target(&mut self, value: &Value, state: &State) -> Resolved {
        let mut target = Resolved::default();
        for loan in value.loans() {
            let origin = &state.loans[loan.0 as usize];
            target.locations.extend(origin.targets.iter().cloned());
            target.via.extend(ancestors(loan, state));
            target.permissions.insert(loan);
            target.unknown |= origin.unknown;
        }
        // Unknown raw origins are checked by the separate contract domain. Any
        // known reference origins still participate in region/store checking.
        target.unknown |= value.unknown;
        target
    }
}
