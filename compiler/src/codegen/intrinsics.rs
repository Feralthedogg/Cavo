use super::{body::Emitter, *};
use crate::contracts::Intrinsic as I;

impl Emitter<'_, '_> {
    pub fn intrinsic(
        &mut self,
        role: I,
        arguments: &[mir::Operand],
        destination: &mir::Place,
        labels: &[String],
    ) -> Result<(), Error> {
        match role {
            I::TaskJoin | I::TaskCancel | I::TaskIgnore => return Err(self.scope_error()),
            I::Length => self.intrinsic_length(&arguments[0], destination)?,
            I::AsPtr | I::AsMutPtr => {
                let (_, pointer) = self.scalar(&arguments[0])?;
                let destination = self.address(destination)?;
                self.store_scalar(&destination.pointer, destination.ty, &pointer)?;
            }
            I::Read | I::ReadUnaligned | I::Take => {
                let (_, pointer) = self.scalar(&arguments[0])?;
                let destination = self.address(destination)?;
                self.copy(
                    &destination.pointer,
                    &pointer,
                    self.module.layout(destination.ty)?.size,
                )?;
            }
            I::Initialize | I::Replace | I::WriteUnaligned => {
                let (ty, pointer) = self.scalar(&arguments[0])?;
                let Ty::Pointer { inner, .. } = self.module.program.hir.types.get(ty) else {
                    return Err(self.error("raw write is missing its element type"));
                };
                self.copy_operand(&pointer, &arguments[1], *inner)?;
            }
            I::Allocate => return self.allocate(&arguments[0], destination, labels),
            I::Deallocate => {
                let (_, pointer) = self.scalar(&arguments[0])?;
                self.module
                    .runtime_import("cavo_rt_free", "declare void @cavo_rt_free(ptr)")?;
                self.ir
                    .line(format!("call void @cavo_rt_free(ptr {pointer})"));
            }
            I::Offset => return self.pointer_offset(arguments, destination, labels),
        }
        self.ir.line(format!("br label %{}", labels[0]));
        Ok(())
    }

    fn intrinsic_length(
        &mut self,
        argument: &mir::Operand,
        destination: &mir::Place,
    ) -> Result<(), Error> {
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = argument else {
            return Err(self.error("length intrinsic has no reference storage"));
        };
        let place = place.clone().project(mir::Projection::Deref);
        let length = self.length(&place)?;
        let destination = self.address(destination)?;
        self.store_scalar(&destination.pointer, destination.ty, &length)
    }

    fn allocate(
        &mut self,
        count: &mir::Operand,
        destination: &mir::Place,
        labels: &[String],
    ) -> Result<(), Error> {
        let (_, count) = self.scalar(count)?;
        let destination = self.address(destination)?;
        let Ty::Pointer { inner, .. } = self.module.program.hir.types.get(destination.ty) else {
            return Err(self.error("allocation result is not a raw pointer"));
        };
        let layout = self.module.layout(*inner)?;
        let (size, alignment) = (layout.size, layout.alignment);
        self.module.runtime_import(
            "cavo_rt_allocate",
            "declare ptr @cavo_rt_allocate(i64, i64, i64)",
        )?;
        let pointer = self.ir.temp(format!(
            "call ptr @cavo_rt_allocate(i64 {count}, i64 {size}, i64 {alignment})"
        ));
        let failed = self.ir.temp(format!("icmp eq ptr {pointer}, null"));
        let success = self.ir.fresh("allocation_ok");
        self.ir.line(format!(
            "br i1 {failed}, label %{}, label %{success}",
            labels[1]
        ));
        self.ir.start(&success);
        self.store_scalar(&destination.pointer, destination.ty, &pointer)?;
        self.ir.line(format!("br label %{}", labels[0]));
        Ok(())
    }

    fn pointer_offset(
        &mut self,
        arguments: &[mir::Operand],
        destination: &mir::Place,
        labels: &[String],
    ) -> Result<(), Error> {
        let (ty, pointer) = self.scalar(&arguments[0])?;
        let (_, count) = self.scalar(&arguments[1])?;
        let Ty::Pointer { inner, .. } = self.module.program.hir.types.get(ty) else {
            return Err(self.error("pointer offset lacks its element type"));
        };
        let size = self.module.layout(*inner)?.size;
        let (bad, _) = self.overflow(
            crate::syntax::ast::BinaryOp::Multiply,
            "i64",
            false,
            &count,
            &size.to_string(),
        )?;
        let success = self.ir.fresh("pointer_offset_ok");
        self.ir.line(format!(
            "br i1 {bad}, label %{}, label %{success}",
            labels[1]
        ));
        self.ir.start(&success);
        let bytes = self.ir.temp(format!("mul i64 {count}, {size}"));
        let pointer = self
            .ir
            .temp(format!("getelementptr i8, ptr {pointer}, i64 {bytes}"));
        let destination = self.address(destination)?;
        self.store_scalar(&destination.pointer, destination.ty, &pointer)?;
        self.ir.line(format!("br label %{}", labels[0]));
        Ok(())
    }
}
