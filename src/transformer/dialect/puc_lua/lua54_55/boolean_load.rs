//! 降低 Lua 5.4/5.5 的布尔常量及 LFALSESKIP；依赖跳转目标校验，不负责其他常量；例如为 LFALSESKIP 同时发射 false 与跳过下一指令的边。

use super::*;

impl ProtoLowerer<'_> {
    pub(super) fn lower_boolean_constant(
        &mut self,
        raw_index: usize,
        raw_pc: u32,
        opcode: FamilyOpcode,
        operands: &FamilyOperands,
    ) -> Result<(), TransformError> {
        match opcode {
            FamilyOpcode::LoadFalse => {
                let a = expect_a(raw_pc, opcode, operands)?;
                let dst = reg_from_u8(a);
                self.pending_methods.invalidate_reg(dst);
                self.emit(
                    Some(raw_index),
                    vec![raw_index],
                    PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr { dst, value: false })),
                );
            }
            FamilyOpcode::LFalseSkip => {
                let a = expect_a(raw_pc, opcode, operands)?;
                let dst = reg_from_u8(a);
                self.pending_methods.invalidate_reg(dst);
                self.emit(
                    Some(raw_index),
                    vec![raw_index],
                    PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr { dst, value: false })),
                );
                self.pending_methods.clear();
                self.emit(
                    None,
                    vec![raw_index],
                    PendingLowInstr::Jump {
                        target: TargetPlaceholder::Raw(
                            self.ensure_targetable_pc(raw_pc, raw_pc + 2)?,
                        ),
                    },
                );
            }
            FamilyOpcode::LoadTrue => {
                let a = expect_a(raw_pc, opcode, operands)?;
                let dst = reg_from_u8(a);
                self.pending_methods.invalidate_reg(dst);
                self.emit(
                    Some(raw_index),
                    vec![raw_index],
                    PendingLowInstr::Ready(LowInstr::LoadBool(LoadBoolInstr { dst, value: true })),
                );
            }
            _ => unreachable!("only boolean constant opcodes should reach this helper"),
        }
        Ok(())
    }
}
