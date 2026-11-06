use super::*;
use crate::symbol::Interner;
use std::fmt::{self, Write};

impl Program {
    /// Deterministic inspection format for a validated artifact, not a stable ABI.
    pub fn dump(&self, hir: &hir::Program, symbols: &Interner) -> String {
        let mut out = String::from(concat!(
            "cavoite MIR / stage=cleanup-foundation\n",
            "verification: structure, storage and cleanup; not an ownership certificate\n",
            "core IR: conditional cleanup; explicit flags/glue and analysis reports follow\n",
            "pending: complete heap/raw/contract proofs, native ABI and runtime preemption\n",
            "source spans: file ID and half-open UTF-8 byte range\n",
        ));
        let printer = Printer { hir, symbols };
        for body in &self.functions {
            let _ = printer.body(&mut out, body);
        }
        out
    }
}

struct Printer<'a> {
    hir: &'a hir::Program,
    symbols: &'a Interner,
}

impl Printer<'_> {
    fn ty(&self, ty: TyId) -> String {
        self.hir
            .types
            .display(ty, self.symbols, &self.hir.definitions)
    }

    fn definition(&self, out: &mut String, id: hir::DefId) -> fmt::Result {
        let definition = &self.hir.definitions[id.0 as usize];
        for name in &self.hir.modules[definition.module.0 as usize].path {
            write!(out, "{}::", self.symbols.get(*name))?;
        }
        out.write_str(self.symbols.get(definition.name))
    }

    fn body(&self, out: &mut String, body: &Body) -> fmt::Result {
        out.push_str("\nfn ");
        self.definition(out, body.definition)?;
        writeln!(out, " -> {} {{", self.ty(body.result))?;
        writeln!(
            out,
            "  entry bb{}; return _{};",
            body.entry.0, body.return_local.0
        )?;
        for (index, scope) in body.scopes.iter().enumerate() {
            write!(out, "  scope s{index}")?;
            if let Some(parent) = scope.parent {
                write!(out, " in s{}", parent.0)?;
            }
            span(out, scope.span)?;
            out.push('\n');
        }
        for (index, local) in body.locals.iter().enumerate() {
            let kind = match local.kind {
                LocalKind::Return => "return",
                LocalKind::Parameter => "parameter",
                LocalKind::Source => "local",
                LocalKind::Temporary => "temporary",
                LocalKind::Address => "place-handle",
                LocalKind::ArrayIterator => "owned-array-iterator",
            };
            write!(
                out,
                "  _{index}: {} [{kind}, s{}]",
                self.ty(local.ty),
                local.scope.0
            )?;
            if let Some(name) = local.name {
                write!(out, " // {}", self.symbols.get(name))?;
            }
            span(out, local.span)?;
            out.push('\n');
        }
        for (index, block) in body.blocks.iter().enumerate() {
            write!(out, "\n  bb{index}")?;
            if let Some(kind) = block.cleanup {
                write!(out, " [cleanup {}]", exit_kind(kind))?;
            }
            span(out, block.span)?;
            out.push_str(":\n");
            for statement in &block.statements {
                out.push_str("    ");
                self.statement(out, statement)?;
                out.push(';');
                span(out, statement.span)?;
                out.push('\n');
            }
            out.push_str("    ");
            self.terminator(out, &block.terminator)?;
            out.push_str(";\n");
        }
        out.push_str("}\n");
        Ok(())
    }

    fn statement(&self, out: &mut String, statement: &Statement) -> fmt::Result {
        match &statement.kind {
            StatementKind::EnterScope(scope) => write!(out, "enter_scope s{}", scope.0)?,
            StatementKind::ExitScope(scope) => write!(out, "exit_scope s{}", scope.0)?,
            StatementKind::StorageLive(local) => write!(out, "storage_live _{}", local.0)?,
            StatementKind::StorageDead(local) => write!(out, "storage_dead _{}", local.0)?,
            StatementKind::Argument(local) => write!(out, "argument _{}", local.0)?,
            StatementKind::IteratorStart { iterator, value } => {
                write!(out, "iterator_start _{} = ", iterator.0)?;
                self.operand(out, value)?;
            }
            StatementKind::Assign { destination, value } => {
                place(out, destination)?;
                out.push_str(" = ");
                self.rvalue(out, value)?;
            }
        }
        Ok(())
    }

    fn operand(&self, out: &mut String, operand: &Operand) -> fmt::Result {
        match operand {
            Operand::ConstTerm { value, ty } => write!(
                out,
                "const_term {}: {}",
                self.hir.types.display_const(*value),
                self.ty(*ty)
            ),
            Operand::Constant { value, ty } => {
                out.push_str("const ");
                match value {
                    hir::Constant::Integer {
                        magnitude,
                        negative,
                    } => {
                        if *negative {
                            out.push('-');
                        }
                        write!(out, "{magnitude}")?;
                    }
                    hir::Constant::Float(value) => write!(out, "{value:?}")?,
                    hir::Constant::Bool(value) => write!(out, "{value}")?,
                    hir::Constant::Char(value) => write!(out, "{value:?}")?,
                    hir::Constant::String(value) => write!(out, "{value:?}")?,
                    hir::Constant::Null => out.push_str("null"),
                }
                write!(out, ": {}", self.ty(*ty))
            }
            Operand::Copy(value) => {
                out.push_str("copy ");
                place(out, value)
            }
            Operand::Move(value) => {
                out.push_str("move ");
                place(out, value)
            }
            Operand::Function { definition, ty } => {
                out.push_str("fn ");
                self.definition(out, *definition)?;
                write!(out, ": {}", self.ty(*ty))
            }
            Operand::Unit => out.write_str("unit"),
        }
    }

    fn operands(&self, out: &mut String, values: &[Operand]) -> fmt::Result {
        for (index, value) in values.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            self.operand(out, value)?;
        }
        Ok(())
    }

    fn rvalue(&self, out: &mut String, value: &Rvalue) -> fmt::Result {
        match value {
            Rvalue::IsVariant {
                place: value,
                variant,
            } => {
                out.push_str("is_variant ");
                place(out, value)?;
                out.push_str(" == ");
                self.definition(out, *variant)
            }
            Rvalue::DynCoerce { value, vtable } => {
                write!(out, "dyn_pack vtable{vtable}(")?;
                self.operand(out, value)?;
                out.write_char(')')
            }
            Rvalue::Use(value) => self.operand(out, value),
            Rvalue::Unary { op, operand } => {
                write!(out, "{op:?}(")?;
                self.operand(out, operand)?;
                out.write_char(')')
            }
            Rvalue::Binary { op, left, right } => {
                write!(out, "{op:?}(")?;
                self.operand(out, left)?;
                out.push_str(", ");
                self.operand(out, right)?;
                out.write_char(')')
            }
            Rvalue::Borrow {
                mutable,
                place: value,
            } => {
                out.push_str(if *mutable { "borrow_mut " } else { "borrow " });
                place(out, value)
            }
            Rvalue::AddressOf(value) => {
                out.push_str("capture_address ");
                place(out, value)
            }
            Rvalue::Array(_)
            | Rvalue::Repeat { .. }
            | Rvalue::RepeatConst { .. }
            | Rvalue::Record { .. }
            | Rvalue::Variant { .. } => self.aggregate(out, value),
            Rvalue::ArrayToSlice(value) => {
                out.push_str("array_to_slice ");
                self.operand(out, value)
            }
            Rvalue::Length(value) => {
                out.push_str("length ");
                place(out, value)
            }
        }
    }

    fn aggregate(&self, out: &mut String, value: &Rvalue) -> fmt::Result {
        match value {
            Rvalue::RepeatConst { value, count } => {
                out.push_str("repeat [");
                self.operand(out, value)?;
                write!(out, "; {}]", self.hir.types.display_const(*count))
            }
            Rvalue::Array(values) => {
                out.push_str("array [");
                self.operands(out, values)?;
                out.write_char(']')
            }
            Rvalue::Repeat { value, count } => {
                out.push_str("repeat [");
                self.operand(out, value)?;
                write!(out, "; {count}]")
            }
            Rvalue::Record { definition, fields } => {
                self.definition(out, *definition)?;
                out.push_str(" { ");
                for (index, (field, operand)) in fields.iter().enumerate() {
                    if index != 0 {
                        out.push_str(", ");
                    }
                    write!(out, "field{field}: ")?;
                    self.operand(out, operand)?;
                }
                out.write_str(" }")
            }
            Rvalue::Variant { definition, fields } => {
                self.definition(out, *definition)?;
                out.push('(');
                self.operands(out, fields)?;
                out.write_char(')')
            }
            _ => unreachable!("aggregate formatter"),
        }
    }

    fn call(&self, out: &mut String, terminator: &Terminator) -> fmt::Result {
        let Terminator::Call {
            callee,
            type_arguments,
            arguments,
            parameter_types,
            destination,
            normal,
            panic,
            cancel,
        } = terminator
        else {
            unreachable!("direct call formatter");
        };

        place(out, destination)?;
        out.push_str(" = call ");
        self.operand(out, callee)?;
        if !type_arguments.is_empty() {
            out.push_str("::<");
            for (index, ty) in type_arguments.iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                out.push_str(&self.hir.types.display_argument(
                    *ty,
                    self.symbols,
                    &self.hir.definitions,
                ));
            }
            out.push('>');
        }
        out.push('(');
        self.operands(out, arguments)?;
        out.push_str(") [parameters: ");
        for (index, ty) in parameter_types.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            out.push_str(&self.ty(*ty));
        }
        write!(
            out,
            "] -> normal bb{}, panic bb{}, cancel bb{}",
            normal.0, panic.0, cancel.0
        )
    }

    fn dynamic_call(&self, out: &mut String, terminator: &Terminator) -> fmt::Result {
        let Terminator::DynCall {
            receiver,
            trait_method,
            arguments,
            destination,
            normal,
            panic,
            cancel,
            ..
        } = terminator
        else {
            unreachable!("dynamic call formatter");
        };

        place(out, destination)?;
        out.push_str(" = dyn_call ");
        self.definition(out, *trait_method)?;
        out.push('(');
        self.operand(out, receiver)?;
        for argument in arguments {
            out.push_str(", ");
            self.operand(out, argument)?;
        }
        write!(
            out,
            ") -> normal bb{}, panic bb{}, cancel bb{}",
            normal.0, panic.0, cancel.0
        )
    }

    fn checked(&self, out: &mut String, terminator: &Terminator) -> fmt::Result {
        let Terminator::Checked {
            value,
            destination,
            normal,
            trap,
        } = terminator
        else {
            unreachable!("checked arithmetic formatter");
        };
        place(out, destination)?;
        out.push_str(" = checked ");
        self.rvalue(out, value)?;
        write!(out, " -> normal bb{}, trap bb{}", normal.0, trap.0)
    }

    fn terminator(&self, out: &mut String, terminator: &Terminator) -> fmt::Result {
        match terminator {
            Terminator::Goto(target) => write!(out, "goto bb{}", target.0),
            Terminator::Switch { condition, yes, no } => {
                out.push_str("switch ");
                self.operand(out, condition)?;
                write!(out, " -> true bb{}, false bb{}", yes.0, no.0)
            }
            Terminator::Call { .. } => self.call(out, terminator),
            Terminator::DynCall { .. } => self.dynamic_call(out, terminator),
            Terminator::IteratorNext {
                iterator,
                destination,
                some,
                none,
            } => {
                place(out, destination)?;
                write!(
                    out,
                    " = iterator_next _{} -> some bb{}, none bb{}",
                    iterator.0, some.0, none.0
                )
            }
            Terminator::Checked { .. } => self.checked(out, terminator),
            Terminator::Bounds {
                base,
                index,
                normal,
                trap,
            } => {
                out.push_str("bounds ");
                place(out, base)?;
                write!(
                    out,
                    "[_{}] -> normal bb{}, trap bb{}",
                    index.0, normal.0, trap.0
                )
            }
            Terminator::Drop {
                place: value,
                next,
                unwind,
            } => {
                out.push_str("drop_if_initialized ");
                place(out, value)?;
                write!(out, " -> next bb{}, unwind bb{}", next.0, unwind.0)
            }
            Terminator::Return => out.write_str("return"),
            Terminator::Resume(kind) => write!(out, "resume {}", exit_kind(*kind)),
            Terminator::Abort => out.write_str("abort"),
            Terminator::Unreachable => out.write_str("unreachable"),
        }
    }
}

fn place(out: &mut String, place: &Place) -> fmt::Result {
    write!(out, "_{}", place.local.0)?;
    for projection in &place.projection {
        match projection {
            Projection::Deref => out.push_str(".deref"),
            Projection::Downcast(variant) => write!(out, ".variant#{}", variant.0)?,
            Projection::Field(index) => write!(out, ".field{index}")?,
            Projection::Index(local) => write!(out, "[_{}]", local.0)?,
        }
    }
    Ok(())
}

fn span(out: &mut String, span: Span) -> fmt::Result {
    write!(out, " @file{}:{}..{}", span.file.0, span.start, span.end)
}

fn exit_kind(kind: ExitKind) -> &'static str {
    match kind {
        ExitKind::Normal => "normal",
        ExitKind::Panic => "panic",
        ExitKind::Cancel => "cancel",
    }
}
