use super::*;
use crate::types::{Region, TyId};

#[derive(Clone, Debug)]
pub(crate) enum Storage {
    Parameter { parameter: u32, path: Vec<Step> },
    Pointee { input: u32, path: Vec<Step> },
}

#[derive(Clone, Debug)]
pub(crate) struct Input {
    pub parameter: u32,
    pub path: Vec<Step>,
    pub storage: Storage,
    pub ty: TyId,
    pub region: Region,
    pub mutable: bool,
}

struct Position {
    parameter: u32,
    path: Vec<Step>,
    storage: Storage,
    parent: Option<Region>,
}

#[derive(Clone, Debug)]
pub(crate) struct Requirement {
    pub path: Vec<Step>,
    pub region: Region,
    pub invariant: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct Frame {
    pub inputs: Vec<Input>,
    pub result: Vec<Requirement>,
    pub stores: Vec<Vec<Requirement>>,
    pub relations: Vec<(Region, Region)>,
    pub complete: bool,
}
impl Frame {
    pub fn declaration(
        definition: hir::DefId,
        hir: &hir::Program,
        properties: &Properties,
    ) -> Self {
        let mut frame = Self {
            inputs: Vec::new(),
            result: Vec::new(),
            stores: Vec::new(),
            relations: Vec::new(),
            complete: true,
        };
        let Ty::Function { parameters, result } = hir.types.get(hir.definitions[definition].ty)
        else {
            frame.complete = false;
            return frame;
        };
        for (index, &ty) in parameters.iter().enumerate() {
            let position = Position {
                parameter: index as u32,
                path: Vec::new(),
                storage: Storage::Parameter {
                    parameter: index as u32,
                    path: Vec::new(),
                },
                parent: None,
            };
            frame.collect(ty, position, hir, properties);
        }
        frame.result = frame.requirements(*result, hir, properties);
        let inputs: Vec<_> = frame.inputs.iter().map(|input| input.ty).collect();
        frame.stores = inputs
            .into_iter()
            .map(|ty| frame.requirements(ty, hir, properties))
            .collect();
        frame
    }
    fn collect(
        &mut self,
        ty: TyId,
        position: Position,
        hir: &hir::Program,
        properties: &Properties,
    ) {
        if position.path.len() >= 64 || self.inputs.len() >= 128 {
            self.complete = false;
            return;
        }
        if !properties.get(ty).references {
            return;
        }
        if matches!(hir.types.get(ty), Ty::Reference { .. }) {
            self.reference(ty, position, hir, properties);
            return;
        }
        if matches!(
            hir.types.get(ty),
            Ty::Dynamic { .. } | Ty::Parameter { .. } | Ty::Str
        ) && matches!(position.storage, Storage::Pointee { .. })
        {
            return;
        }
        let Some(fields) = children(ty, hir, properties) else {
            self.complete = false;
            return;
        };
        for (suffix, field) in fields {
            let mut path = position.path.clone();
            path.extend(&suffix);
            let mut storage = position.storage.clone();
            for step in suffix {
                storage = storage.project(step);
            }
            let child = Position {
                parameter: position.parameter,
                path,
                storage,
                parent: position.parent,
            };
            self.collect(field, child, hir, properties);
        }
    }
    fn reference(
        &mut self,
        ty: TyId,
        position: Position,
        hir: &hir::Program,
        properties: &Properties,
    ) {
        let Ty::Reference {
            inner,
            region,
            mutable,
        } = hir.types.get(ty)
        else {
            unreachable!("reference input");
        };
        let input = self.inputs.len() as u32;
        if let Some(parent) = position.parent {
            self.relations.push((*region, parent));
        }
        self.inputs.push(Input {
            parameter: position.parameter,
            path: position.path.clone(),
            storage: position.storage,
            ty,
            region: *region,
            mutable: *mutable,
        });
        let mut path = position.path;
        path.push(Step::Deref);
        let child = Position {
            parameter: position.parameter,
            path,
            storage: Storage::Pointee {
                input,
                path: Vec::new(),
            },
            parent: Some(*region),
        };
        self.collect(*inner, child, hir, properties);
    }

    fn requirements(
        &mut self,
        ty: TyId,
        hir: &hir::Program,
        properties: &Properties,
    ) -> Vec<Requirement> {
        let mut result = Vec::new();
        let mut pending = vec![(ty, Vec::new(), false)];
        while let Some((ty, path, invariant)) = pending.pop() {
            if path.len() >= 64 || result.len() >= 128 {
                self.complete = false;
                break;
            }
            match hir.types.get(ty) {
                Ty::Reference {
                    region,
                    inner,
                    mutable,
                } => {
                    result.push(Requirement {
                        path: path.clone(),
                        region: *region,
                        invariant,
                    });
                    if !matches!(
                        hir.types.get(*inner),
                        Ty::Str | Ty::Parameter { .. } | Ty::Dynamic { .. }
                    ) {
                        let mut path = path;
                        path.push(Step::Deref);
                        pending.push((*inner, path, invariant || *mutable));
                    }
                }
                _ if properties.get(ty).references => {
                    if let Some(fields) = children(ty, hir, properties) {
                        for (suffix, field) in fields {
                            let mut path = path.clone();
                            path.extend(suffix);
                            pending.push((field, path, invariant));
                        }
                    } else {
                        self.complete = false;
                    }
                }
                _ => {}
            }
        }
        result
    }
    pub fn outlives(&self, input: u32, region: Region) -> bool {
        let Some(input) = self.inputs.get(input as usize) else {
            return false;
        };
        if matches!(region, Region::Infer(_)) && self.inputs.len() == 1 {
            return true;
        }
        self.region_outlives(input.region, region)
    }
    pub fn region_outlives(&self, longer: Region, shorter: Region) -> bool {
        if longer == Region::Static || longer == shorter {
            return true;
        }
        let mut seen = HashSet::new();
        let mut pending = vec![longer];
        while let Some(from) = pending.pop() {
            if !seen.insert(from) {
                continue;
            }
            for &(longer, next) in &self.relations {
                if longer == from {
                    if next == shorter {
                        return true;
                    }
                    pending.push(next);
                }
            }
        }
        false
    }
    pub fn reference_cell(&self, target: &Footprint) -> Option<usize> {
        self.inputs.iter().position(|value| matches!(&value.storage, Storage::Pointee { input, path } if *input == target.input && *path == target.path))
    }
    pub fn syntax_input(&self, parameter: u32, path: &[Step]) -> Option<usize> {
        self.inputs
            .iter()
            .position(|input| input.parameter == parameter && input.path == path)
    }
}
impl Storage {
    fn project(&self, step: Step) -> Self {
        match self {
            Self::Parameter { parameter, path } => {
                let mut path = path.clone();
                path.push(step);
                Self::Parameter {
                    parameter: *parameter,
                    path,
                }
            }
            Self::Pointee { input, path } => {
                let mut path = path.clone();
                path.push(step);
                Self::Pointee {
                    input: *input,
                    path,
                }
            }
        }
    }
}

pub(in crate::mir::borrow) fn children(
    ty: TyId,
    hir: &hir::Program,
    properties: &Properties,
) -> Option<Vec<(Vec<Step>, TyId)>> {
    if let Some(fields) = properties.fields(ty) {
        return Some(
            fields
                .iter()
                .enumerate()
                .map(|(i, &ty)| (vec![Step::Field(i as u32)], ty))
                .collect(),
        );
    }
    match hir.types.get(ty) {
        Ty::Array { inner, .. } | Ty::SymbolicArray { inner, .. } | Ty::Slice(inner) => {
            Some(vec![(vec![Step::Element], *inner)])
        }
        Ty::Named { definition, .. } => {
            let enumeration = hir
                .enums
                .iter()
                .find(|value| value.definition == *definition)?;
            let mut fields = Vec::new();
            for &variant in &enumeration.variants {
                for (index, &ty) in properties.variant_fields(ty, variant)?.iter().enumerate() {
                    fields.push((vec![Step::Variant(variant), Step::Field(index as u32)], ty));
                }
            }
            Some(fields)
        }
        _ => None,
    }
}
