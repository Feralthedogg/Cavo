use super::*;

#[derive(Clone)]
struct Request {
    predicate: MemoryPredicate,
    value: Value,
    count: Option<u64>,
    ty: TyId,
    unaligned: bool,
    operation: String,
    span: Span,
    other: Option<(Value, Option<u64>)>,
}

struct Condition {
    name: &'static str,
    truth: Truth,
    basis: Basis,
    detail: &'static str,
}

impl Engine<'_> {
    pub(super) fn statement_obligations(
        &self,
        statement: &StatementKind,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        if let StatementKind::Contract(contract) = statement
            && let Action::Assume { reason } = &contract.action
        {
            report.evidence.insert(Evidence {
                kind: EvidenceKind::Assumption,
                span,
                event: self.basis(span).event,
                parents: Vec::new(),
                trust: BTreeSet::from([Trust::Source {
                    file: span.file.0,
                    start: span.start,
                    reason: reason.clone(),
                }]),
                detail: "explicit source premise; it is not an independently checked fact".into(),
            })?;
        }
        match statement {
            StatementKind::Contract(contract)
                if !matches!(contract.action, Action::Precondition) =>
            {
                let request = self.logical_request(contract, span, state)?;
                self.request(
                    request,
                    matches!(contract.action, Action::Assume { .. }),
                    state,
                    report,
                )?;
            }
            StatementKind::Assign { destination, value } => {
                self.place_request(destination, true, span, state, report)?;
                self.value_requests(value, span, state, report)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn logical_request(
        &self,
        contract: &crate::contracts::Statement,
        span: Span,
        state: &State,
    ) -> Result<Request, String> {
        let Some(first) = contract.atom.arguments.first() else {
            return Err("logical predicate has no operands".into());
        };
        let value = self.operand(first, state);
        let ty = match self.context.hir.types.get(self.operand_type(first)) {
            Ty::Pointer { inner, .. } | Ty::Reference { inner, .. } => *inner,
            _ => TyId::VOID,
        };
        Ok(Request {
            predicate: contract.atom.predicate,
            value,
            count: contract
                .atom
                .arguments
                .get(1)
                .and_then(|value| self.operand(value, state).integer),
            ty,
            unaligned: false,
            operation: format!("{:?}", contract.atom.predicate),
            span,
            other: if contract.atom.predicate == MemoryPredicate::BorrowedFrom {
                contract
                    .atom
                    .arguments
                    .get(1)
                    .map(|value| (self.operand(value, state), None))
            } else {
                contract.atom.arguments.get(2).map(|other| {
                    (
                        self.operand(other, state),
                        contract
                            .atom
                            .arguments
                            .get(3)
                            .and_then(|count| self.operand(count, state).integer),
                    )
                })
            },
        })
    }

    pub(super) fn exit_obligations(
        &self,
        exit: &Terminator,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        match exit {
            Terminator::Call {
                callee: Operand::Function { definition, .. },
                arguments,
                ..
            } => {
                self.intrinsic_request(*definition, arguments, span, state, report)?;
            }
            Terminator::Checked { value, .. } => self.value_requests(value, span, state, report)?,
            Terminator::Return
                if matches!(
                    self.context.hir.types.get(self.context.body.result),
                    Ty::Reference { .. }
                ) =>
            {
                let value = state.local(self.context.body.return_local).clone();
                if let Some(pointer) = &value.pointer
                    && pointer.expired
                {
                    self.request(
                        Request {
                            predicate: MemoryPredicate::Readable,
                            value,
                            count: Some(1),
                            ty: TyId::VOID,
                            unaligned: true,
                            operation: "returned reference lifetime".into(),
                            span,
                            other: None,
                        },
                        false,
                        state,
                        report,
                    )?;
                }
            }
            Terminator::Drop { place, .. } => self.storage_valid(place, span, state, report)?,
            _ => {}
        }
        if matches!(exit, Terminator::Return | Terminator::Resume(_)) {
            for (&id, allocation) in &state.allocations {
                if matches!(id, AllocationId::Input(_))
                    && allocation.raw_touched
                    && allocation.initialized != Truth::Yes
                {
                    self.single_unknown("reference restoration", "initialized borrowed storage on every exit",
                        "raw take must restore borrowed storage before normal, panic and cancellation exits", span, report)?;
                }
            }
        }
        Ok(())
    }

    fn intrinsic_request(
        &self,
        definition: hir::DefId,
        arguments: &[Operand],
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        let Some(&role) = self.context.hir.contracts.intrinsics.get(&definition) else {
            return Ok(());
        };
        let Some(first) = arguments.first() else {
            return Err("intrinsic has no input".into());
        };
        let Some(predicate) = intrinsic_requirement(role) else {
            return Ok(());
        };
        let ty = match self.context.hir.types.get(self.operand_type(first)) {
            Ty::Pointer { inner, .. } => *inner,
            _ => return Err("raw intrinsic requires a pointer operand".into()),
        };
        if matches!(role, Intrinsic::Read | Intrinsic::ReadUnaligned)
            && !self.context.properties.get(ty).copy
        {
            return self.single_unknown(
                "raw Copy read",
                "Copy value",
                "use a consuming take for a non-Copy value",
                span,
                report,
            );
        }
        let request = Request {
            predicate,
            value: self.operand(first, state),
            count: Some(1),
            ty,
            unaligned: matches!(role, Intrinsic::ReadUnaligned | Intrinsic::WriteUnaligned),
            operation: self.operation_name(definition, span).into(),
            span,
            other: None,
        };
        self.request(request.clone(), false, state, report)?;
        if let Some((predicate, operation)) = match role {
            Intrinsic::Replace => Some((MemoryPredicate::Readable, "initialized raw replacement")),
            Intrinsic::Take => Some((MemoryPredicate::Writable, "exclusive raw take")),
            _ => None,
        } {
            self.request(
                Request {
                    predicate,
                    operation: format!("{}: {operation}", request.operation),
                    ..request.clone()
                },
                false,
                state,
                report,
            )?;
        }
        if role == Intrinsic::Initialize {
            self.initialization_request(&request.value, ty, span, state, report)?;
        }
        Ok(())
    }

    fn operation_name(&self, definition: hir::DefId, span: Span) -> &str {
        self.context
            .call_names
            .get(&span)
            .copied()
            .unwrap_or_else(|| {
                self.context
                    .symbols
                    .get(self.context.hir.definitions[definition].name)
            })
    }

    fn initialization_request(
        &self,
        value: &Value,
        ty: TyId,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        let initialized = self.initialized_destination(value, ty, state);
        if initialized != Truth::No {
            let truth = if initialized == Truth::Yes {
                Truth::No
            } else {
                Truth::Unknown
            };
            let assessment = self.assessment(
                truth,
                self.basis(span),
                "initialize requires an uninitialized destination",
                report,
            )?;
            let name = crate::external::interface::qualified(
                self.context.hir,
                self.context.symbols,
                self.context.body.definition,
            );
            report.obligations.push(Obligation {
                key: source::obligation_key(
                    &name,
                    self.context.events[self.block] as usize,
                    "initialize destination",
                ),
                span,
                operation: "initialize destination".into(),
                components: vec![Component {
                    name: "uninitialized destination".into(),
                    assessment,
                }],
            });
        }
        Ok(())
    }

    fn initialized_destination(&self, value: &Value, ty: TyId, state: &State) -> Truth {
        let Some(pointer) = &value.pointer else {
            return Truth::Unknown;
        };
        let Some(allocation) = state.allocations.get(&pointer.allocation) else {
            return Truth::Unknown;
        };
        if let (Some(offset), Some(size)) = (pointer.offset, self.size(ty)) {
            let end = offset.saturating_add(size.bytes);
            if allocation
                .initialized_ranges
                .iter()
                .any(|&(start, bytes, _)| start < end && start.saturating_add(bytes) > offset)
            {
                return Truth::Yes;
            }
            if allocation
                .uninitialized_ranges
                .iter()
                .any(|&(start, bytes)| start <= offset && start.saturating_add(bytes) >= end)
            {
                return Truth::No;
            }
        }
        allocation.initialized
    }

    fn place_request(
        &self,
        place: &Place,
        write: bool,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        if !write {
            self.union_request(place, span, state, report)?;
        }
        if !write {
            self.storage_valid(place, span, state, report)?;
        }
        let Some(index) = place
            .projection
            .iter()
            .position(|p| *p == Projection::Deref)
        else {
            return Ok(());
        };
        let base = Place {
            local: place.local,
            projection: place.projection[..index].to_vec(),
        };
        if !matches!(
            self.context.hir.types.get(self.place_type(&base)),
            Ty::Pointer { .. }
        ) && !self
            .address(place, state)
            .is_some_and(|pointer| pointer.raw)
        {
            return Ok(());
        }
        self.request(
            Request {
                predicate: if write {
                    MemoryPredicate::Writable
                } else {
                    MemoryPredicate::Readable
                },
                value: Value {
                    pointer: self.address(place, state),
                    ..Value::default()
                },
                count: Some(1),
                ty: self.place_type(place),
                unaligned: false,
                operation: if write { "raw write" } else { "raw read" }.into(),
                span,
                other: None,
            },
            false,
            state,
            report,
        )
    }

    fn value_requests(
        &self,
        value: &Rvalue,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        let mut operands = Vec::new();
        match value {
            Rvalue::Use(value)
            | Rvalue::Unary { operand: value, .. }
            | Rvalue::Repeat { value, .. }
            | Rvalue::RepeatConst { value, .. }
            | Rvalue::ArrayToSlice(value)
            | Rvalue::DynCoerce { value, .. } => operands.push(value),
            Rvalue::Binary { left, right, .. } => operands.extend([left, right]),
            Rvalue::Array(values) | Rvalue::Variant { fields: values, .. } => {
                operands.extend(values)
            }
            Rvalue::Record { fields, .. } => operands.extend(fields.iter().map(|(_, value)| value)),
            Rvalue::Borrow { place, .. }
            | Rvalue::Length(place)
            | Rvalue::IsVariant { place, .. } => {
                self.place_request(place, false, span, state, report)?
            }
            Rvalue::AddressOf(_) => {}
        }
        for operand in operands {
            if let Operand::Copy(place) | Operand::Move(place) = operand {
                self.place_request(place, false, span, state, report)?;
            }
        }
        Ok(())
    }

    fn request(
        &self,
        request: Request,
        assumption: bool,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        let conditions = self.conditions(&request, state);
        let mut components = Vec::new();
        for condition in conditions {
            let mut truth = condition.truth;
            let mut basis = condition.basis;
            basis.trust.extend(request.value.trust.iter().cloned());
            if truth == Truth::Unknown
                && let Some(fact) = self.fact(&request, condition.name, state)
            {
                basis = fact;
                truth = Truth::Yes;
            }
            let assessment = if truth == Truth::Unknown && assumption {
                Assessment::Unknown(
                    "manual premise is recorded by the following assumption event".into(),
                )
            } else {
                self.assessment(truth, basis, condition.detail, report)?
            };
            if !assumption || truth == Truth::No {
                components.push(Component {
                    name: condition.name.into(),
                    assessment,
                });
            }
        }
        if components.is_empty() {
            return Ok(());
        }
        let name = crate::external::interface::qualified(
            self.context.hir,
            self.context.symbols,
            self.context.body.definition,
        );
        let key = source::obligation_key(
            &name,
            (self.context.events[self.block] + self.statement as u64) as usize,
            &request.operation,
        );
        report.obligations.push(Obligation {
            key,
            span: request.span,
            operation: request.operation,
            components,
        });
        Ok(())
    }

    fn fact(&self, request: &Request, component: &str, state: &State) -> Option<Basis> {
        if matches!(
            request.predicate,
            MemoryPredicate::NoRetain | MemoryPredicate::NoCallback
        ) {
            let function = request.value.function?;
            return state
                .assumptions
                .iter()
                .rev()
                .find(|fact| {
                    fact.predicate == request.predicate && fact.value.function == Some(function)
                })
                .map(|fact| fact.basis.clone());
        }
        state
            .assumptions
            .iter()
            .rev()
            .find(|fact| fact_matches(fact, request) && fact_supports(fact, request, component))
            .map(|fact| fact.basis.clone())
    }

    fn assessment(
        &self,
        truth: Truth,
        basis: Basis,
        detail: &str,
        report: &mut Report,
    ) -> Result<Assessment, String> {
        if truth == Truth::Unknown {
            return Ok(Assessment::Unknown(detail.into()));
        }
        let trust = basis.trust;
        let assumed = !trust.is_empty();
        let parent = report
            .evidence
            .origin(basis.event, basis.span, trust.clone(), detail)?;
        let id = report.evidence.insert(Evidence {
            kind: if truth == Truth::No {
                EvidenceKind::Violation
            } else if assumed {
                EvidenceKind::Assumption
            } else {
                EvidenceKind::Derivation
            },
            span: basis.span,
            event: basis.event,
            parents: vec![parent],
            trust,
            detail: detail.into(),
        })?;
        Ok(if truth == Truth::No {
            Assessment::Violated(WitnessId(id))
        } else if assumed {
            Assessment::Assumed(id)
        } else {
            Assessment::Proven(id)
        })
    }

    fn single_unknown(
        &self,
        operation: &str,
        component: &str,
        reason: &str,
        span: Span,
        report: &mut Report,
    ) -> Result<(), String> {
        let name = crate::external::interface::qualified(
            self.context.hir,
            self.context.symbols,
            self.context.body.definition,
        );
        report.obligations.push(Obligation {
            key: source::obligation_key(&name, report.obligations.len(), operation),
            span,
            operation: operation.into(),
            components: vec![Component {
                name: component.into(),
                assessment: Assessment::Unknown(reason.into()),
            }],
        });
        Ok(())
    }

    fn conditions(&self, request: &Request, state: &State) -> Vec<Condition> {
        if !matches!(
            request.predicate,
            MemoryPredicate::Scalar
                | MemoryPredicate::Readable
                | MemoryPredicate::Writable
                | MemoryPredicate::ReadableUnaligned
                | MemoryPredicate::WritableUnaligned
                | MemoryPredicate::Initialized
                | MemoryPredicate::OwnedAllocation
        ) {
            return self.relational_conditions(request, state);
        }
        if request.predicate == MemoryPredicate::Scalar {
            return vec![Condition {
                name: "scalar predicate",
                truth: match request.value.boolean {
                    Some(true) => Truth::Yes,
                    Some(false) => Truth::No,
                    None => Truth::Unknown,
                },
                basis: self.basis(request.span),
                detail: "the scalar predicate is evaluated with its current input values",
            }];
        }
        let basis = self.basis(request.span);
        let Some(pointer) = &request.value.pointer else {
            return vec![Condition {
                name: "pointer origin",
                truth: Truth::Unknown,
                basis,
                detail: "pointer origin is not established",
            }];
        };
        let allocation = state.allocations.get(&pointer.allocation);
        let life = if pointer.expired {
            Truth::No
        } else {
            allocation.map_or(Truth::Unknown, |a| a.live)
        };
        let origin = allocation.map_or_else(
            || pointer.basis.clone(),
            |a| a.invalidation.clone().unwrap_or_else(|| a.basis.clone()),
        );
        let mut conditions = vec![Condition {
            name: "allocation lifetime",
            truth: life,
            basis: origin,
            detail: "the allocation generation must remain live until this use",
        }];
        if request.predicate == MemoryPredicate::OwnedAllocation {
            conditions.extend(self.ownership_conditions(pointer, allocation, state));
            return conditions;
        }
        self.range_conditions(request, pointer, allocation, state, &mut conditions);
        conditions
    }

    fn ownership_conditions(
        &self,
        pointer: &Pointer,
        allocation: Option<&Allocation>,
        state: &State,
    ) -> Vec<Condition> {
        let mut conditions = Vec::new();
        conditions.push(Condition {
            name: "allocation base",
            truth: match (pointer.allocation, pointer.offset) {
                (AllocationId::Input(_), _) => Truth::Unknown,
                (_, Some(0)) => Truth::Yes,
                (_, Some(_)) => Truth::No,
                (_, None) => Truth::Unknown,
            },
            basis: pointer.basis.clone(),
            detail: "deallocation requires the original allocation base",
        });
        conditions.push(Condition {
            name: "unique deallocation permission",
            truth: if pointer.owned == Truth::No {
                Truth::No
            } else {
                allocation.map_or(Truth::Unknown, |a| a.owned)
            },
            basis: pointer.basis.clone(),
            detail: "the allocation must be owned and not already consumed",
        });
        conditions.push(Condition {
            name: "non-racing access",
            truth: self.alias_permission(pointer, true, state),
            basis: pointer.basis.clone(),
            detail: "deallocation cannot invalidate a live reference",
        });
        conditions
    }

    fn relational_conditions(&self, request: &Request, state: &State) -> Vec<Condition> {
        let truth = match request.predicate {
            MemoryPredicate::BorrowedFrom => match (
                request.value.pointer.as_ref(),
                request
                    .other
                    .as_ref()
                    .and_then(|(value, _)| value.pointer.as_ref()),
            ) {
                (Some(left), Some(right)) if left.expired || right.expired => Truth::No,
                (Some(left), Some(right)) if left.allocation == right.allocation => Truth::Yes,
                _ => Truth::Unknown,
            },
            MemoryPredicate::NoRetain | MemoryPredicate::NoCallback => request
                .value
                .function
                .filter(|function| crate::modular::usable(self.context.hir, *function))
                .and_then(|function| self.context.hir.modular.functions.get(&function))
                .filter(|contract| {
                    if request.predicate == MemoryPredicate::NoRetain {
                        contract.no_retain
                    } else {
                        contract.no_callback
                    }
                })
                .map_or(Truth::Unknown, |_| Truth::Yes),
            MemoryPredicate::Disjoint => disjoint(request),
            MemoryPredicate::ActiveUnion => request
                .value
                .pointer
                .as_ref()
                .and_then(|pointer| state.allocations.get(&pointer.allocation))
                .filter(|allocation| allocation.initialized_type == Some(request.ty))
                .and_then(|allocation| allocation.active_union)
                .or(request.value.active_union)
                .zip(request.count)
                .map_or(Truth::Unknown, |(actual, expected)| {
                    if u64::from(actual) == expected {
                        Truth::Yes
                    } else {
                        Truth::No
                    }
                }),
            _ => Truth::Unknown,
        };
        vec![Condition {
            name: "relational memory predicate",
            truth,
            basis: self.basis(request.span),
            detail: "the relation must hold for these exact operand origins and ranges",
        }]
    }

    fn union_request(
        &self,
        place: &Place,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        for (index, projection) in place.projection.iter().enumerate() {
            let Projection::Field(field) = projection else {
                continue;
            };
            let base = Place {
                local: place.local,
                projection: place.projection[..index].to_vec(),
            };
            if !self.context.properties.union(self.place_type(&base)) {
                continue;
            }
            let pointer = self.address(&base, state).unwrap_or(Pointer {
                raw: false,
                owned: Truth::No,
                ancestors: BTreeSet::new(),
                allocation: AllocationId::Local(base.local.0),
                offset: Some(0),
                readable: Truth::Yes,
                writable: Truth::No,
                unaligned: false,
                expired: false,
                basis: self.basis(span),
            });
            self.request(
                Request {
                    predicate: MemoryPredicate::ActiveUnion,
                    value: Value {
                        active_union: state.read(&base).active_union,
                        pointer: Some(pointer),
                        ..Value::default()
                    },
                    count: Some(u64::from(*field)),
                    ty: self.place_type(&base),
                    unaligned: false,
                    operation: "union field read".into(),
                    span,
                    other: None,
                },
                false,
                state,
                report,
            )?;
        }
        Ok(())
    }

    fn range_conditions(
        &self,
        request: &Request,
        pointer: &Pointer,
        allocation: Option<&Allocation>,
        state: &State,
        conditions: &mut Vec<Condition>,
    ) {
        let basis = pointer.basis.clone();
        let size = self.size(request.ty);
        let bytes = size.and_then(|size| {
            request
                .count
                .and_then(|count| count.checked_mul(size.bytes))
        });
        let range = pointer
            .offset
            .zip(bytes)
            .and_then(|(offset, bytes)| offset.checked_add(bytes).map(|end| (offset, end)));
        let bounds = range_within(range, allocation.and_then(|allocation| allocation.extent));
        let unaligned = request.unaligned
            || matches!(
                request.predicate,
                MemoryPredicate::ReadableUnaligned
                    | MemoryPredicate::WritableUnaligned
                    | MemoryPredicate::Initialized
            );
        let alignment = alignment(unaligned, pointer.offset, size, allocation);
        let writable = matches!(
            request.predicate,
            MemoryPredicate::Writable | MemoryPredicate::WritableUnaligned
        );
        conditions.push(Condition {
            name: "byte range",
            truth: bounds,
            basis: basis.clone(),
            detail: "the checked byte range must lie within one allocation",
        });
        conditions.push(Condition {
            name: "alignment",
            truth: alignment,
            basis: basis.clone(),
            detail: "alignment must match the requested type",
        });
        conditions.push(Condition {
            name: "access permission",
            truth: if writable {
                pointer.writable
            } else {
                pointer.readable
            },
            basis: basis.clone(),
            detail: "the originating reference or contract must authorize this access",
        });
        if !writable {
            conditions.push(initialization_condition(
                request.ty,
                bytes,
                range,
                allocation,
                basis.clone(),
            ));
        }
        conditions.push(Condition {
            name: "non-racing access",
            truth: self.alias_permission(pointer, writable, state),
            basis: basis.clone(),
            detail: "no live descendant or unrelated loan may conflict with this access",
        });
    }

    fn alias_permission(&self, pointer: &Pointer, write: bool, state: &State) -> Truth {
        let live = &self.context.liveness.before[self.block][self.statement];
        let mut result = Truth::Yes;
        for &local in live {
            if self.context.body.locals[local].kind == LocalKind::Address {
                continue;
            }
            match conflict(&state.values[local], pointer, write, state) {
                Truth::No => return Truth::No,
                Truth::Unknown => result = Truth::Unknown,
                Truth::Yes => {}
            }
        }
        result
    }

    fn storage_valid(
        &self,
        place: &Place,
        span: Span,
        state: &State,
        report: &mut Report,
    ) -> Result<(), String> {
        let id = self
            .address(place, state)
            .map_or(AllocationId::Local(place.local.0), |p| p.allocation);
        let Some(allocation) = state.allocations.get(&id) else {
            return Ok(());
        };
        if !allocation.raw_touched || allocation.initialized == Truth::Yes {
            return Ok(());
        }
        self.single_unknown("raw storage restoration", "initialized typed storage",
            "raw operations left this storage without an established initialized value; restore it before a safe use or cleanup", span, report)
    }
}

fn fact_matches(fact: &Fact, request: &Request) -> bool {
    let (Some(pointer), Some(other)) = (&request.value.pointer, &fact.value.pointer) else {
        return false;
    };
    if pointer.allocation != other.allocation
        || pointer.offset != other.offset
        || pointer.expired
        || fact.ty != request.ty
    {
        return false;
    }
    let covers = fact
        .count
        .zip(request.count)
        .is_some_and(|(available, needed)| {
            if request.predicate == MemoryPredicate::ActiveUnion {
                available == needed
            } else {
                available >= needed
            }
        })
        || matches!(
            request.predicate,
            MemoryPredicate::OwnedAllocation | MemoryPredicate::BorrowedFrom
        );
    if !covers {
        return false;
    }
    if request.predicate == MemoryPredicate::Disjoint
        && request.other.as_ref().is_some_and(|(value, count)| {
            fact.operands.get(2) != Some(value)
                || fact.operands.get(3).and_then(|value| value.integer) != *count
        })
    {
        return false;
    }
    !(request.predicate == MemoryPredicate::BorrowedFrom
        && request
            .other
            .as_ref()
            .is_some_and(|(owner, _)| fact.operands.get(1) != Some(owner)))
}

fn fact_supports(fact: &Fact, request: &Request, component: &str) -> bool {
    use MemoryPredicate::*;
    if matches!(
        component,
        "access permission" | "non-racing access" | "unique deallocation permission"
    ) && fact.permissions == Freshness::Invalidated
    {
        return false;
    }
    if (component == "initialization and validity" || request.predicate == ActiveUnion)
        && fact.contents == Freshness::Invalidated
    {
        return false;
    }
    let predicate = fact.predicate;
    match component {
        "allocation lifetime" | "byte range" => matches!(
            predicate,
            Readable | Writable | ReadableUnaligned | WritableUnaligned | OwnedAllocation
        ),
        "alignment" => matches!(predicate, Readable | Writable | OwnedAllocation),
        "access permission" => {
            if matches!(request.predicate, Writable | WritableUnaligned) {
                matches!(predicate, Writable | WritableUnaligned)
            } else {
                matches!(
                    predicate,
                    Readable | Writable | ReadableUnaligned | WritableUnaligned
                )
            }
        }
        "initialization and validity" => {
            matches!(predicate, Readable | ReadableUnaligned | Initialized)
        }
        _ => {
            predicate == request.predicate
                || request.unaligned
                    && matches!(
                        (request.predicate, predicate),
                        (Readable, ReadableUnaligned) | (Writable, WritableUnaligned)
                    )
        }
    }
}

fn conflict(value: &Value, pointer: &Pointer, write: bool, state: &State) -> Truth {
    let mut result = if value.opaque_references {
        Truth::Unknown
    } else {
        Truth::Yes
    };
    if let Some(reference) = &value.pointer
        && !reference.raw
        && !reference.expired
        && reference.basis.event != pointer.basis.event
        && !pointer.ancestors.contains(&reference.basis.event)
        && (write || reference.writable == Truth::Yes)
    {
        if reference.allocation == pointer.allocation {
            return Truth::No;
        }
        if !state
            .allocations
            .get(&reference.allocation)
            .is_some_and(|a| a.live == Truth::Yes)
            || !state
                .allocations
                .get(&pointer.allocation)
                .is_some_and(|a| a.live == Truth::Yes)
        {
            result = Truth::Unknown;
        }
    }
    for field in value.fields.values() {
        match conflict(field, pointer, write, state) {
            Truth::No => return Truth::No,
            Truth::Unknown => result = Truth::Unknown,
            Truth::Yes => {}
        }
    }
    result
}

fn disjoint(request: &Request) -> Truth {
    let (Some(left), Some(bytes), Some((right, Some(other_bytes)))) = (
        request.value.pointer.as_ref(),
        request.count,
        request.other.as_ref(),
    ) else {
        return Truth::Unknown;
    };
    if bytes == 0 || *other_bytes == 0 {
        return Truth::Yes;
    }
    let Some(right) = &right.pointer else {
        return Truth::Unknown;
    };
    if left.expired || right.expired {
        return Truth::Unknown;
    }
    if left.allocation != right.allocation {
        return if matches!(left.allocation, AllocationId::Input(_))
            || matches!(right.allocation, AllocationId::Input(_))
        {
            Truth::Unknown
        } else {
            Truth::Yes
        };
    }
    let Some((a, b)) = left.offset.zip(right.offset) else {
        return Truth::Unknown;
    };
    let Some((end_a, end_b)) = a.checked_add(bytes).zip(b.checked_add(*other_bytes)) else {
        return Truth::Unknown;
    };
    if end_a <= b || end_b <= a {
        Truth::Yes
    } else {
        Truth::No
    }
}

fn alignment(
    unaligned: bool,
    offset: Option<u64>,
    size: Option<Size>,
    allocation: Option<&Allocation>,
) -> Truth {
    if unaligned {
        return Truth::Yes;
    }
    match (offset, size, allocation) {
        (Some(offset), Some(size), Some(allocation)) if allocation.alignment >= size.alignment => {
            if offset % size.alignment == 0 {
                Truth::Yes
            } else {
                Truth::No
            }
        }
        _ => Truth::Unknown,
    }
}

fn initialization_condition(
    ty: TyId,
    bytes: Option<u64>,
    range: Option<(u64, u64)>,
    allocation: Option<&Allocation>,
    mut basis: Basis,
) -> Condition {
    if let Some(allocation) = allocation {
        basis.trust.extend(allocation.basis.trust.iter().cloned());
    }
    Condition {
        name: "initialization and validity",
        truth: initialization(ty, bytes, range, allocation),
        basis,
        detail: "every requested element must be initialized as a valid value of this type",
    }
}

fn initialization(
    ty: TyId,
    bytes: Option<u64>,
    range: Option<(u64, u64)>,
    allocation: Option<&Allocation>,
) -> Truth {
    let Some(allocation) = allocation else {
        return Truth::Unknown;
    };
    if bytes == Some(0) {
        return Truth::Yes;
    }
    if let Some((offset, end)) = range {
        if allocation
            .uninitialized_ranges
            .iter()
            .any(|&(start, bytes)| start < end && start.saturating_add(bytes) > offset)
        {
            return Truth::No;
        }
        if allocation
            .initialized_ranges
            .iter()
            .any(|&(start, bytes, kind)| {
                start <= offset && start.saturating_add(bytes) >= end && kind == ty.0
            })
        {
            return Truth::Yes;
        }
    }
    if allocation.initialized == Truth::No || allocation.initialized_type == Some(ty) {
        allocation.initialized
    } else {
        Truth::Unknown
    }
}

fn range_within(range: Option<(u64, u64)>, extent: Option<u64>) -> Truth {
    match (range, extent) {
        (Some((_, end)), Some(extent)) => {
            if end <= extent {
                Truth::Yes
            } else {
                Truth::No
            }
        }
        _ => Truth::Unknown,
    }
}

fn intrinsic_requirement(role: Intrinsic) -> Option<MemoryPredicate> {
    Some(match role {
        Intrinsic::Read | Intrinsic::ReadUnaligned | Intrinsic::Take => MemoryPredicate::Readable,
        Intrinsic::Initialize | Intrinsic::Replace | Intrinsic::WriteUnaligned => {
            MemoryPredicate::Writable
        }
        Intrinsic::Deallocate => MemoryPredicate::OwnedAllocation,
        _ => return None,
    })
}
