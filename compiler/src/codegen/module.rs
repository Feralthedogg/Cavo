use super::*;

const IR_LIMIT: usize = 64 * 1024 * 1024;

pub(super) struct Module<'a> {
    pub program: &'a mono::Program,
    pub symbols: &'a Interner,
    pub output: String,
    pub declarations: BTreeMap<String, String>,
    pub strings: BTreeMap<Vec<u8>, String>,
    pub annotations: BTreeSet<(String, String)>,
    pub span: Span,
}

impl<'a> Module<'a> {
    pub fn new(
        program: &'a mono::Program,
        symbols: &'a Interner,
        triple: &str,
        span: Span,
    ) -> Result<Self, Error> {
        if triple.len() > 256
            || !triple
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
        {
            return Err(problem(span, "invalid LLVM target triple"));
        }
        if program.layouts.target.pointer_bits != 64 {
            return Err(problem(
                span,
                "native emission currently requires a 64-bit target layout",
            ));
        }
        Ok(Self {
            program,
            symbols,
            span,
            output: format!("; Cavo checked MIR\ntarget triple = {}\n\n", quote(triple)),
            declarations: BTreeMap::new(),
            strings: BTreeMap::new(),
            annotations: BTreeSet::new(),
        })
    }

    pub fn functions(&mut self) -> Result<(), Error> {
        for core in &self.program.mir.functions {
            if self
                .program
                .hir
                .modular
                .functions
                .get(&core.definition)
                .is_some_and(|contract| contract.affinity)
            {
                self.annotations.insert((
                    format!("__cavo_f_{}", core.definition.0),
                    "llam-native-affine".into(),
                ));
            }
            let cleanup = self
                .program
                .analysis
                .drops
                .functions
                .iter()
                .find(|body| body.definition == core.definition)
                .ok_or_else(|| problem(core.blocks[0].span, "concrete cleanup body is missing"))?;
            body::Emitter::function(self, core, cleanup)?;
            self.budget()?;
        }
        self.vtables()
    }

    fn vtables(&mut self) -> Result<(), Error> {
        for (index, table) in self.program.hir.vtables.iter().enumerate() {
            let entries = table
                .slots
                .iter()
                .map(|slot| format!("ptr {}", self.function(slot.implementation)))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                self.output,
                "@__cavo_vtable_{index} = private constant [{} x ptr] [{entries}], align 8",
                table.slots.len()
            );
        }
        self.budget()
    }

    pub fn function(&self, id: hir::DefId) -> String {
        let definition = &self.program.hir.definitions[id];
        if definition.foreign_abi.is_some() {
            format!("@{}", quote(self.symbols.get(definition.name)))
        } else {
            format!("@__cavo_f_{}", id.0)
        }
    }

    pub fn layout(&self, ty: TyId) -> Result<&layout::Layout, Error> {
        self.program.layouts.get(ty).ok_or_else(|| {
            problem(
                self.span,
                format!("native storage layout is missing for type {}", ty.0),
            )
        })
    }

    pub fn scalar_type(&self, ty: TyId) -> Result<String, Error> {
        Ok(match self.program.hir.types.get(ty) {
            Ty::Bool => "i8".into(),
            Ty::Char => "i32".into(),
            Ty::Integer { bits, .. } => format!("i{}", if *bits == 0 { 64 } else { *bits }),
            Ty::Float { bits: 32 } => "float".into(),
            Ty::Float { bits: 64 } => "double".into(),
            Ty::Pointer { .. } | Ty::Function { .. } | Ty::ForAll { .. } => "ptr".into(),
            Ty::Reference { .. }
                if matches!(self.layout(ty)?.kind, layout::Kind::Pointer { words: 1 }) =>
            {
                "ptr".into()
            }
            _ => {
                return Err(problem(
                    self.span,
                    "this operation requires a scalar native value",
                ));
            }
        })
    }

    pub fn declare(&mut self, name: &str, signature: String) -> Result<(), Error> {
        if self
            .declarations
            .get(name)
            .is_some_and(|existing| existing != &signature)
        {
            return Err(problem(
                self.span,
                format!("conflicting native ABI declarations for {name}"),
            ));
        }
        self.declarations.insert(name.into(), signature);
        Ok(())
    }

    pub fn runtime_import(&mut self, name: &str, signature: &str) -> Result<(), Error> {
        self.declare(name, signature.into())?;
        self.annotations
            .insert((name.into(), "llam-foreign-fast".into()));
        Ok(())
    }

    pub fn entry(&mut self, id: hir::DefId) -> Result<(), Error> {
        let function = self.function(id);
        let _ = writeln!(
            self.output,
            "define void @cavo_program_entry(ptr %cell) #0 {{\nentry:\n  %out = getelementptr i8, ptr %cell, i64 4\n  %status = call i32 {function}(ptr null, ptr %out)\n  store i32 %status, ptr %cell, align 4\n  ret void\n}}\n"
        );
        self.budget()
    }

    pub fn finish(mut self) -> Result<String, Error> {
        for declaration in self.declarations.values() {
            let _ = writeln!(self.output, "{declaration}");
        }
        let mut annotations = Vec::new();
        for (name, annotation) in &self.annotations {
            let bytes = format!("{annotation}\0").into_bytes();
            let index = self.strings.len();
            let text = self
                .strings
                .entry(bytes)
                .or_insert_with(|| format!("@__cavo_string_{index}"));
            annotations.push(format!("{{ ptr, ptr, ptr, i32, ptr }} {{ ptr @{name}, ptr {text}, ptr null, i32 0, ptr null }}"));
        }
        if !annotations.is_empty() {
            let _ = writeln!(
                self.output,
                "@llvm.global.annotations = appending global [{} x {{ ptr, ptr, ptr, i32, ptr }}] [{}], section \"llvm.metadata\"",
                annotations.len(),
                annotations.join(", ")
            );
        }
        for (bytes, name) in &self.strings {
            let mut encoded = String::new();
            for byte in bytes {
                let _ = write!(encoded, "\\{byte:02X}");
            }
            let _ = writeln!(
                self.output,
                "{name} = private unnamed_addr constant [{} x i8] c\"{encoded}\", align 1",
                bytes.len()
            );
        }
        self.output.push_str("attributes #0 = { noinline \"frame-pointer\"=\"all\" \"disable-tail-calls\"=\"true\" \"no-jump-tables\"=\"true\" }\n");
        self.output.push_str("attributes #1 = { noinline optnone \"frame-pointer\"=\"all\" \"disable-tail-calls\"=\"true\" }\n");
        self.budget()?;
        Ok(self.output)
    }

    pub fn budget(&self) -> Result<(), Error> {
        if self.output.len() > IR_LIMIT {
            Err(problem(
                self.span,
                "LLVM emission exceeds its 64 MiB IR budget",
            ))
        } else {
            Ok(())
        }
    }
}
