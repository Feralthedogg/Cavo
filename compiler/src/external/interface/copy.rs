use super::*;
use crate::hir::traits::{Impl, copy_implementations as implementations};

#[derive(Debug)]
pub struct CopyPermission {
    pub name: String,
    /// These are declarations, not an assertion that every instantiation is Copy.
    pub explicit_impls: Vec<Digest>,
    pub negative_traits: Vec<&'static str>,
}

pub fn permissions(
    program: &hir::Program,
    symbols: &Interner,
    sources: &SourceMap,
) -> Option<Vec<CopyPermission>> {
    let internal = program.internal_definitions();
    let mut permissions = Vec::new();
    for (index, definition) in program.definitions.iter().enumerate() {
        let id = hir::DefId(index as u32);
        if !internal.contains(&id)
            && matches!(
                definition.kind,
                hir::DefinitionKind::Record
                    | hir::DefinitionKind::Union
                    | hir::DefinitionKind::Enum
            )
        {
            let mut explicit_impls = implementations(program, id)
                .map(|implementation| {
                    descriptor(program, symbols, sources, implementation)
                        .map(|encoder| sha256(&encoder.bytes))
                })
                .collect::<Option<Vec<_>>>()?;
            explicit_impls.sort();
            permissions.push(CopyPermission {
                name: qualified(program, symbols, id),
                explicit_impls,
                negative_traits: negative_markers(program, id),
            });
        }
    }
    permissions.sort_by(|left, right| left.name.cmp(&right.name));
    Some(permissions)
}

impl Encoder<'_> {
    pub(super) fn copy_permissions(&mut self, definition: hir::DefId) -> Option<()> {
        let mut descriptors = Vec::new();
        for implementation in implementations(self.program, definition) {
            let descriptor = descriptor(self.program, self.symbols, self.sources, implementation)?;
            self.nominals.extend(descriptor.nominals);
            descriptors.push(descriptor.bytes);
        }
        descriptors.sort();
        self.remaining = self.remaining.checked_sub(descriptors.len())?;
        self.token("explicit-copy-v1");
        self.number(descriptors.len() as u64);
        for descriptor in descriptors {
            self.token(&sha256(&descriptor).to_string());
        }
        Some(())
    }
}

fn descriptor<'a>(
    program: &'a hir::Program,
    symbols: &'a Interner,
    sources: &'a SourceMap,
    implementation: &Impl,
) -> Option<Encoder<'a>> {
    let mut encoder = Encoder::new(program, symbols, sources);
    encoder.token("copy-impl-v1");
    let definition = &program.definitions[implementation.definition];
    encoder.number(definition.generic_parameter_kinds.len() as u64);
    for kind in &definition.generic_parameter_kinds {
        encoder.token(&format!("{kind:?}"));
    }
    encoder.ty(implementation.target, 0)?;
    let mut bounds = Vec::new();
    for bound in &definition.bounds {
        let mut body = Encoder::new(program, symbols, sources);
        body.number(u64::from(bound.parameter));
        body.token(&qualified(program, symbols, bound.trait_ref.definition));
        body.number(bound.trait_ref.arguments.len() as u64);
        for &argument in &bound.trait_ref.arguments {
            body.generic(argument, 0)?;
        }
        encoder.nominals.extend(body.nominals);
        bounds.push(body.bytes);
    }
    bounds.sort();
    encoder.number(bounds.len() as u64);
    for bound in bounds {
        encoder.token(&sha256(&bound).to_string());
    }
    Some(encoder)
}
