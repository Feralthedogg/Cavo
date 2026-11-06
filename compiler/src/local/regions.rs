use super::properties::Properties;
use crate::{
    diagnostic::{Diagnostic, report},
    hir,
    types::{Region, Ty, TyId},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionStep {
    Field(u32),
    Deref,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegionTerm {
    Declared(Region),
    Anonymous(u32),
}

/// A reference-bearing component of a function input. Field paths are semantic
/// record projections, not byte offsets or persistent external identifiers.
#[derive(Clone, Debug)]
pub struct RegionInput {
    pub parameter: u32,
    pub fields: Vec<u32>,
    pub path: Vec<RegionStep>,
    pub term: RegionTerm,
    pub region: Option<Region>,
    pub pointee: Option<TyId>,
    pub mutable: Option<bool>,
}

#[derive(Clone, Debug)]
pub struct RegionContract {
    pub definition: hir::DefId,
    pub inputs: Vec<RegionInput>,
    pub return_inputs: Vec<usize>,
    pub reference_result: bool,
    pub result_pointee: Option<TyId>,
    pub static_result: bool,
    pub has_body: bool,
    pub valid: bool,
    /// All supported bodies in this compilation were checked, including callees.
    /// This is not an external trust summary or full memory-safety certificate.
    pub body_checked: bool,
    pub outlives: Vec<(RegionTerm, RegionTerm)>,
    pub assumptions: Vec<crate::external::AssumptionId>,
}

impl RegionContract {
    pub fn outlives(&self, longer: RegionTerm, shorter: RegionTerm) -> bool {
        if longer == shorter || longer == RegionTerm::Declared(Region::Static) {
            return true;
        }
        let mut pending = vec![longer];
        let mut seen = std::collections::HashSet::new();
        while let Some(region) = pending.pop() {
            if !seen.insert(region) {
                continue;
            }
            for &(a, b) in &self.outlives {
                if a == region {
                    if b == shorter {
                        return true;
                    }
                    pending.push(b);
                }
            }
        }
        false
    }
}

pub(super) struct Signature<'a> {
    pub definition: hir::DefId,
    pub parameters: &'a [TyId],
    pub result: TyId,
    pub span: crate::source::Span,
    pub has_body: bool,
}
#[derive(Clone, Copy)]
struct RegionTypes<'a> {
    program: &'a hir::Program,
    properties: &'a Properties,
}
#[derive(Clone, Copy)]
pub(super) enum SignatureProblem {
    InputLimit(crate::source::Span),
    Elision(crate::source::Span),
}
impl SignatureProblem {
    pub fn diagnostic(self) -> Diagnostic {
        match self{
        Self::InputLimit(span)=>Diagnostic::error("E-REGION-LIMIT","function region inputs exceed their resource limit",span),
        Self::Elision(span)=>Diagnostic::error("E-REGION-ELISION","cannot infer the input lifetime of this return reference",span)
            .note("elision requires one reference input; without reference inputs, every return must have a static origin")
            .help("name the input and return lifetimes, or declare an explicit 'static result"),
    }
    }
}

pub(super) fn signature(
    signature: Signature<'_>,
    program: &hir::Program,
    properties: &Properties,
) -> (RegionContract, Option<SignatureProblem>) {
    let mut problem = None;
    let Signature {
        definition,
        parameters,
        result,
        span,
        has_body,
    } = signature;
    fn collect(
        ty: TyId,
        parameter: u32,
        path: &mut Vec<RegionStep>,
        contract: &mut RegionContract,
        parent: Option<RegionTerm>,
        active: &mut Vec<TyId>,
        types: RegionTypes<'_>,
    ) -> Option<()> {
        let RegionTypes {
            program,
            properties,
        } = types;
        if !properties.get(ty).references {
            return Some(());
        }
        if path.len() > 128 || contract.inputs.len() >= 128 {
            return None;
        }
        if let Ty::Reference {
            region,
            inner,
            mutable,
        } = *program.types.get(ty)
        {
            let term = if matches!(region, Region::Infer(_)) {
                RegionTerm::Anonymous(contract.inputs.len() as u32)
            } else {
                RegionTerm::Declared(region)
            };
            if let Some(parent) = parent {
                contract.outlives.push((term, parent));
            }
            contract.inputs.push(RegionInput {
                parameter,
                fields: path
                    .iter()
                    .filter_map(|step| {
                        if let RegionStep::Field(i) = step {
                            Some(*i)
                        } else {
                            None
                        }
                    })
                    .collect(),
                path: path.clone(),
                term,
                region: Some(region),
                pointee: Some(inner),
                mutable: Some(mutable),
            });
            if !active.contains(&inner) {
                active.push(inner);
                path.push(RegionStep::Deref);
                collect(inner, parameter, path, contract, Some(term), active, types)?;
                path.pop();
                active.pop();
            }
        } else if let Some(fields) = properties.fields(ty) {
            for (index, &field) in fields.iter().enumerate() {
                path.push(RegionStep::Field(index as u32));
                collect(field, parameter, path, contract, parent, active, types)?;
                path.pop();
            }
        } else if properties.get(ty).references {
            contract.inputs.push(RegionInput {
                parameter,
                fields: path
                    .iter()
                    .filter_map(|step| {
                        if let RegionStep::Field(i) = step {
                            Some(*i)
                        } else {
                            None
                        }
                    })
                    .collect(),
                path: path.clone(),
                term: RegionTerm::Anonymous(contract.inputs.len() as u32),
                region: None,
                pointee: None,
                mutable: None,
            });
        }
        Some(())
    }
    let mut contract = RegionContract {
        definition,
        inputs: Vec::new(),
        return_inputs: Vec::new(),
        reference_result: false,
        result_pointee: None,
        static_result: false,
        has_body,
        valid: true,
        body_checked: false,
        outlives: Vec::new(),
        assumptions: Vec::new(),
    };
    for (parameter, &ty) in parameters.iter().enumerate() {
        if collect(
            ty,
            parameter as u32,
            &mut Vec::new(),
            &mut contract,
            None,
            &mut Vec::new(),
            RegionTypes {
                program,
                properties,
            },
        )
        .is_none()
        {
            contract.valid = false;
            problem = Some(SignatureProblem::InputLimit(span));
            break;
        }
    }
    if let Ty::Reference { region, inner, .. } = *program.types.get(result) {
        contract.reference_result = true;
        contract.result_pointee = Some(inner);
        match region {
            Region::Infer(_) => {
                let matching: Vec<_> = contract
                    .inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, input)| (input.region == Some(region)).then_some(i))
                    .collect();
                let references: Vec<_> = contract
                    .inputs
                    .iter()
                    .enumerate()
                    .filter(|(_, i)| i.region.is_some())
                    .map(|(i, _)| i)
                    .collect();
                if !matching.is_empty() {
                    contract.return_inputs = matching;
                } else if references.len() == 1 {
                    contract.return_inputs = references;
                } else if contract.inputs.is_empty() {
                    contract.static_result = true;
                } else {
                    contract.valid = false;
                    problem.get_or_insert(SignatureProblem::Elision(span));
                }
            }
            Region::Named { .. } | Region::Static | Region::Bound { .. } => {
                contract.return_inputs = contract
                    .inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, input)| {
                        contract
                            .outlives(input.term, RegionTerm::Declared(region))
                            .then_some(i)
                    })
                    .collect();
                contract.static_result =
                    region == Region::Static || contract.return_inputs.is_empty();
            }
        }
    } else {
        // Opaque/generic aggregate results retain every possible input
        // origin. Never infer a field mapping from type/position alone.
        contract.return_inputs = (0..contract.inputs.len()).collect();
    }
    (contract, problem)
}

pub(super) fn contracts(
    program: &hir::Program,
    properties: &Properties,
    bodies: &[bool],
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Option<RegionContract>> {
    program
        .definitions
        .iter()
        .enumerate()
        .map(|(index, definition)| {
            if definition.kind != hir::DefinitionKind::Function {
                return None;
            }
            let Ty::Function { parameters, result } = program.types.get(definition.ty) else {
                return None;
            };
            let (contract, problem) = signature(
                Signature {
                    definition: hir::DefId(index as u32),
                    parameters,
                    result: *result,
                    span: definition.span,
                    has_body: bodies[index],
                },
                program,
                properties,
            );
            if let Some(problem) = problem {
                report(diagnostics, problem.diagnostic());
            }
            Some(contract)
        })
        .collect()
}
