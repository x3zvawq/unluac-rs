//! 处理不发射 low-IR 的 Luau 标记与 FASTCALL 前缀；依赖 fallback CALL 协议，不负责普通 CALL lowering；例如冻结 FASTCALL3 的三个直接参数。

use super::*;

impl ProtoLowerer<'_> {
    pub(super) fn lower_noop_or_fastcall(
        &mut self,
        raw_index: usize,
        raw_pc: u32,
        opcode: LuauOpcode,
        operands: &LuauOperands,
        extra: LuauInstrExtra,
    ) -> Result<(), TransformError> {
        let fastcall = match opcode {
            LuauOpcode::PrepVarArgs => {
                expect_a(raw_pc, opcode, operands)?;
                None
            }
            LuauOpcode::Coverage => {
                expect_e(raw_pc, opcode, operands)?;
                None
            }
            LuauOpcode::FastCall => {
                let (_, skip) = expect_ac(raw_pc, opcode, operands)?;
                Some((skip, PendingFastCall::All))
            }
            LuauOpcode::FastCall1 => {
                let (_, source, skip) = expect_abc(raw_pc, opcode, operands)?;
                Some((
                    skip,
                    PendingFastCall::Fixed {
                        sources: [Some(reg_from_u8(source)), None, None],
                        len: 1,
                    },
                ))
            }
            LuauOpcode::FastCall2 | LuauOpcode::FastCall2K => {
                let (_, source, skip) = expect_abc(raw_pc, opcode, operands)?;
                let second = if opcode == LuauOpcode::FastCall2 {
                    Some(reg_from_u8(aux_reg(raw_pc, opcode, extra)?))
                } else {
                    required_aux(raw_pc, opcode, extra)?;
                    None
                };
                Some((
                    skip,
                    PendingFastCall::Fixed {
                        sources: [Some(reg_from_u8(source)), second, None],
                        len: 2,
                    },
                ))
            }
            LuauOpcode::FastCall3 => {
                let (_, source, skip) = expect_abc(raw_pc, opcode, operands)?;
                let aux = required_aux(raw_pc, opcode, extra)?;
                if aux >> 16 != 0 {
                    return Err(TransformError::UnexpectedOperands {
                        raw_pc,
                        opcode: opcode.label(),
                        expected: "AUX upper 16 bits must be zero",
                    });
                }
                Some((
                    skip,
                    PendingFastCall::Fixed {
                        sources: [
                            Some(reg_from_u8(source)),
                            Some(reg_from_u8(aux as u8)),
                            Some(reg_from_u8((aux >> 8) as u8)),
                        ],
                        len: 3,
                    },
                ))
            }
            LuauOpcode::Nop => None,
            _ => unreachable!("only no-op Luau opcodes should reach this arm"),
        };
        if let Some((skip, fastcall)) = fastcall {
            self.record_fastcall_target(raw_pc, opcode, skip, fastcall)?;
        }
        // opcode 本身不发 low-IR；FASTCALL 协议已冻结到 fallback CALL，raw pc 仍映射到其后的首条 low-IR 供跳转引用。
        self.lowering.mark_raw_target(raw_index);
        Ok(())
    }
}
