use super::{
    body::{Emitter, iterator_cursor},
    *,
};
use mir::drop::{self as cleanup, GlueId, GlueKind};

impl Emitter<'_, '_> {
    pub fn cleanup_exit(&mut self, exit: &cleanup::Terminator) -> Result<(), Error> {
        match exit {
            cleanup::Terminator::Core { source, successors } => self.core_exit(*source, successors),
            cleanup::Terminator::Goto(next) => {
                self.ir.line(format!("br label %b{}", next.0));
                Ok(())
            }
            cleanup::Terminator::TestFlag {
                flag,
                initialized,
                clear,
            } => {
                let value = self
                    .ir
                    .temp(format!("load i1, ptr %flag{}, align 1", flag.0));
                self.ir.line(format!(
                    "br i1 {value}, label %b{}, label %b{}",
                    initialized.0, clear.0
                ));
                Ok(())
            }
            cleanup::Terminator::TestVariant {
                place,
                variant,
                matches,
                otherwise,
            } => {
                let value = self.tag(place, *variant)?;
                self.ir.line(format!(
                    "br i1 {value}, label %b{}, label %b{}",
                    matches.0, otherwise.0
                ));
                Ok(())
            }
            cleanup::Terminator::InvokeGlue {
                place,
                glue,
                next,
                unwind,
            } => {
                let address = self.address(place)?;
                let status = self.ir.temp(format!(
                    "call i32 @__cavo_drop_{}(ptr %context, ptr null, ptr {})",
                    glue.0, address.pointer
                ));
                let success = self.ir.temp(format!("icmp eq i32 {status}, 0"));
                self.ir.line(format!(
                    "br i1 {success}, label %b{}, label %b{}",
                    next.0, unwind.0
                ));
                Ok(())
            }
        }
    }
}

struct GlueEmitter<'m, 'p> {
    module: &'m mut Module<'p>,
    ir: ir::Writer,
    failure: String,
}

impl Module<'_> {
    pub fn glue(&mut self) -> Result<(), Error> {
        let program = self.program;
        for (index, glue) in program.analysis.drops.glue.iter().enumerate() {
            let mut emitter = GlueEmitter {
                module: self,
                ir: ir::Writer::new(),
                failure: String::new(),
            };
            emitter.failure = emitter.ir.alloca(4, 4);
            let failure = emitter.failure.clone();
            emitter
                .ir
                .line(format!("store i32 0, ptr {failure}, align 1"));
            emitter.emit(glue.ty, &glue.kind, "%self")?;
            let status = emitter.ir.temp(format!("load i32, ptr {failure}, align 1"));
            emitter.ir.line(format!("ret i32 {status}"));
            let _ = writeln!(
                emitter.module.output,
                "define i32 @__cavo_drop_{index}(ptr %context, ptr %out, ptr %self) #0 {{\nentry:"
            );
            emitter.module.output.push_str(&emitter.ir.allocations);
            emitter.module.output.push_str(&emitter.ir.text);
            emitter.module.output.push_str("}\n\n");
            emitter.module.budget()?;
        }
        Ok(())
    }
}

impl GlueEmitter<'_, '_> {
    fn emit(&mut self, ty: TyId, kind: &GlueKind, pointer: &str) -> Result<(), Error> {
        match kind {
            GlueKind::Trivial => Ok(()),
            GlueKind::Record(fields) => {
                for field in fields {
                    let offset = self.field_offset(ty, None, field.field)?;
                    let pointer = self.ir.offset(pointer, offset);
                    self.call(field.glue, &pointer)?;
                }
                Ok(())
            }
            GlueKind::User {
                destructor,
                fields,
                concrete: true,
            } => {
                self.destructor(destructor, pointer)?;
                self.call(*fields, pointer)
            }
            GlueKind::Destructor {
                destructor,
                concrete: true,
            } => self.destructor(destructor, pointer),
            GlueKind::Array { element, count } => self.array(ty, *element, *count, pointer, false),
            GlueKind::ArrayTail {
                element,
                count: cleanup::ArrayLength::Concrete(count),
            } => self.array(ty, *element, *count, pointer, true),
            GlueKind::Enum(variants) => self.enumeration(ty, variants, pointer),
            GlueKind::TaskHandle => Err(problem(
                self.module.span,
                "Task observation drop needs the scoped task runtime barrier",
            )),
            _ => Err(problem(
                self.module.span,
                "native drop glue is still generic or manually owned",
            )),
        }
    }

    fn field_offset(
        &self,
        ty: TyId,
        variant: Option<hir::DefId>,
        index: u32,
    ) -> Result<u64, Error> {
        let (fields, payload) = match &self.module.layout(ty)?.kind {
            layout::Kind::Record { fields, .. } | layout::Kind::Union { fields } => (fields, 0),
            layout::Kind::Enum {
                variants,
                payload_offset,
                ..
            } => (
                &variants
                    .iter()
                    .find(|item| Some(item.definition) == variant)
                    .ok_or_else(|| problem(self.module.span, "drop variant layout is missing"))?
                    .fields,
                *payload_offset,
            ),
            _ => {
                return Err(problem(
                    self.module.span,
                    "drop field has no aggregate layout",
                ));
            }
        };
        fields
            .iter()
            .find(|field| field.index == index)
            .map(|field| field.offset + payload)
            .ok_or_else(|| problem(self.module.span, "drop field offset is missing"))
    }

    fn destructor(
        &mut self,
        target: &hir::traits::MethodSelection,
        pointer: &str,
    ) -> Result<(), Error> {
        let argument = self.ir.alloca(8, 8);
        self.ir
            .line(format!("store ptr {pointer}, ptr {argument}, align 1"));
        let callee = self.module.function(target.definition);
        let status = self.ir.temp(format!(
            "call i32 {callee}(ptr %context, ptr null, ptr {argument})"
        ));
        self.retain_failure(&status)
    }

    fn call(&mut self, id: GlueId, pointer: &str) -> Result<(), Error> {
        let status = self.ir.temp(format!(
            "call i32 @__cavo_drop_{}(ptr %context, ptr null, ptr {pointer})",
            id.0
        ));
        self.retain_failure(&status)
    }

    fn retain_failure(&mut self, status: &str) -> Result<(), Error> {
        // One failure starts unwinding, but fields/tail still need cleanup.
        // A second failure aborts; returning early would leak initialized owners.
        let bad = self.ir.fresh("drop_failed");
        let first = self.ir.fresh("drop_first");
        let abort = self.ir.fresh("drop_abort");
        let next = self.ir.fresh("drop_next");
        let success = self.ir.temp(format!("icmp eq i32 {status}, 0"));
        self.ir
            .line(format!("br i1 {success}, label %{next}, label %{bad}"));
        self.ir.start(&bad);
        let failure = self.failure.clone();
        let old = self.ir.temp(format!("load i32, ptr {failure}, align 1"));
        let empty = self.ir.temp(format!("icmp eq i32 {old}, 0"));
        self.ir
            .line(format!("br i1 {empty}, label %{first}, label %{abort}"));
        self.ir.start(&abort);
        self.module.runtime_import(
            "cavo_rt_abort",
            "declare void @cavo_rt_abort() cold noreturn nounwind",
        )?;
        self.ir.line("call void @cavo_rt_abort()".into());
        self.ir.line("unreachable".into());
        self.ir.start(&first);
        self.ir
            .line(format!("store i32 {status}, ptr {failure}, align 1"));
        self.ir.line(format!("br label %{next}"));
        self.ir.start(&next);
        Ok(())
    }

    fn array(
        &mut self,
        ty: TyId,
        element: GlueId,
        count: u64,
        pointer: &str,
        tail: bool,
    ) -> Result<(), Error> {
        let layout = self.module.layout(ty)?;
        let layout::Kind::Array { stride, .. } = layout.kind else {
            return Err(problem(self.module.span, "array drop has no array layout"));
        };
        let size = layout.size;
        let cursor = if tail {
            Some(self.ir.offset(pointer, iterator_cursor(size)))
        } else {
            None
        };
        let start = cursor
            .as_ref()
            .map(|cursor| self.ir.temp(format!("load i64, ptr {cursor}, align 1")))
            .unwrap_or_else(|| "0".into());
        let predecessor = self.ir.label.clone();
        let check = self.ir.fresh("drop_check");
        let body = self.ir.fresh("drop_element");
        let latch = self.ir.fresh("drop_latch");
        let done = self.ir.fresh("drop_done");
        let index = self.ir.fresh("drop_index");
        let next = self.ir.fresh("drop_index_next");
        self.ir.line(format!("br label %{check}"));
        self.ir.start(&check);
        self.ir.line(format!(
            "%{index} = phi i64 [{start}, %{predecessor}], [%{next}, %{latch}]"
        ));
        let present = self.ir.temp(format!("icmp ult i64 %{index}, {count}"));
        self.ir
            .line(format!("br i1 {present}, label %{body}, label %{done}"));
        self.ir.start(&body);
        let bytes = self.ir.temp(format!("mul i64 %{index}, {stride}"));
        let item = self
            .ir
            .temp(format!("getelementptr i8, ptr {pointer}, i64 {bytes}"));
        if let Some(cursor) = cursor {
            let advanced = self.ir.temp(format!("add i64 %{index}, 1"));
            self.ir
                .line(format!("store i64 {advanced}, ptr {cursor}, align 1"));
        }
        self.call(element, &item)?;
        self.ir.line(format!("br label %{latch}"));
        self.ir.start(&latch);
        self.ir.line(format!("%{next} = add i64 %{index}, 1"));
        self.ir.line(format!("br label %{check}"));
        self.ir.start(&done);
        Ok(())
    }

    fn enumeration(
        &mut self,
        ty: TyId,
        variants: &[cleanup::VariantGlue],
        pointer: &str,
    ) -> Result<(), Error> {
        let layout::Kind::Enum {
            tag_bytes,
            variants: layouts,
            ..
        } = &self.module.layout(ty)?.kind
        else {
            return Err(problem(self.module.span, "enum drop has no enum layout"));
        };
        let bits = u32::from(*tag_bytes) * 8;
        let tags = layouts
            .iter()
            .map(|item| (item.definition, item.discriminant))
            .collect::<BTreeMap<_, _>>();
        let tag = self
            .ir
            .temp(format!("load i{bits}, ptr {pointer}, align 1"));
        let done = self.ir.fresh("enum_drop_done");
        let labels = variants
            .iter()
            .map(|_| self.ir.fresh("enum_drop_variant"))
            .collect::<Vec<_>>();
        let cases = variants
            .iter()
            .zip(&labels)
            .map(|(variant, label)| format!("i{bits} {}, label %{label}", tags[&variant.variant]))
            .collect::<Vec<_>>()
            .join(" ");
        self.ir
            .line(format!("switch i{bits} {tag}, label %{done} [{cases}]"));
        for (variant, label) in variants.iter().zip(labels) {
            self.ir.start(&label);
            for (index, &glue) in variant.fields.iter().enumerate() {
                let offset = self.field_offset(ty, Some(variant.variant), index as u32)?;
                let field = self.ir.offset(pointer, offset);
                self.call(glue, &field)?;
            }
            self.ir.line(format!("br label %{done}"));
        }
        self.ir.start(&done);
        Ok(())
    }
}
