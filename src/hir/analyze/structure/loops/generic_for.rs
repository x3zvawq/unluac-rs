//! 这个文件承载 generic-for header 的局部解析与 iterator 表达式恢复。
//!
//! generic-for lowering 需要同时读取 `GenericForCall` 和紧随其后的 `GenericForLoop`，
//! 并把 iterator/state/control 三元组恢复为 HIR 表达式。本文件只处理这段 VM 头部
//! 形状的提取，不决定 loop body、break pad 或 state slot 身份。
//!
//! 输入形状：`GenericForCall` + `GenericForLoop` 相邻出现在 header 尾部。
//! 输出形状：for lowering 可消费的 call/loop 指令和 iterator 表达式列表。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn generic_for_header_instrs(
        &self,
        header: BlockRef,
    ) -> Option<(
        InstrRef,
        crate::transformer::GenericForCallInstr,
        crate::transformer::GenericForLoopInstr,
    )> {
        let range = self.lowering.cfg.blocks[header.index()].instrs;
        if range.len < 2 {
            return None;
        }

        let call_instr_ref = InstrRef(range.end() - 2);
        let loop_instr_ref = InstrRef(range.end() - 1);
        let LowInstr::GenericForCall(call) =
            self.lowering.proto.instrs.get(call_instr_ref.index())?
        else {
            return None;
        };
        let LowInstr::GenericForLoop(loop_instr) =
            self.lowering.proto.instrs.get(loop_instr_ref.index())?
        else {
            return None;
        };

        Some((call_instr_ref, *call, *loop_instr))
    }

    pub(super) fn lower_generic_for_iterator(
        &self,
        header: BlockRef,
        call_instr_ref: InstrRef,
        call: crate::transformer::GenericForCallInstr,
    ) -> Vec<HirExpr> {
        (0..call.state.len)
            .map(|offset| {
                expr_for_reg_use(
                    self.lowering,
                    header,
                    call_instr_ref,
                    Reg(call.state.start.index() + offset),
                )
            })
            .collect()
    }
}
