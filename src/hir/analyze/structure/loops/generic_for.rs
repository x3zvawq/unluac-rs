//! 这个文件承载 generic-for header 的局部解析与 iterator 表达式恢复。
//!
//! generic-for lowering 需要同时读取 `GenericForCall` 和紧随其后的 `GenericForLoop`；
//! Lua 5.4/5.5 还要从 preheader 的 `GenericForPrep` 读取交换前的源码四元组。本文件
//! 只处理这段 VM 头部形状，不决定 loop body、break pad 或 state slot 身份。
//!
//! 输入形状：`GenericForCall` + `GenericForLoop` 相邻出现在 header 尾部。
//! 输出形状：for lowering 可消费的 call/loop 指令和 iterator 表达式列表。

use super::*;

pub(super) struct GenericForSource {
    block: BlockRef,
    pub(super) prep_instr_ref: Option<InstrRef>,
    regs: crate::transformer::RegRange,
}

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn generic_for_header_instrs(
        &self,
        header: BlockRef,
    ) -> Option<(
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
        if call.results != crate::transformer::ResultPack::Fixed(loop_instr.bindings) {
            return None;
        }

        Some((*call, *loop_instr))
    }

    pub(super) fn generic_for_source(
        &self,
        preheader: BlockRef,
        call: crate::transformer::GenericForCallInstr,
    ) -> Option<GenericForSource> {
        let range = self.lowering.cfg.blocks[preheader.index()].instrs;
        let prep_instr_ref = (range.len >= 2).then(|| InstrRef(range.end() - 2));
        let Some((prep_instr_ref, prep)) = prep_instr_ref.and_then(|instr_ref| {
            match self.lowering.proto.instrs.get(instr_ref.index())? {
                LowInstr::GenericForPrep(prep) => Some((instr_ref, *prep)),
                _ => None,
            }
        }) else {
            if call.state != Reg(call.iterator.index() + 1)
                || call.control != Reg(call.iterator.index() + 2)
            {
                return None;
            }
            return Some(GenericForSource {
                block: preheader,
                prep_instr_ref: None,
                regs: crate::transformer::RegRange::new(call.iterator, 3),
            });
        };
        let terminator = range.last()?;
        if !matches!(
            self.lowering.proto.instrs[terminator.index()],
            LowInstr::Jump(_)
        ) {
            return None;
        }
        if prep.iterator != call.iterator
            || prep.state != call.state
            || prep.state != Reg(prep.iterator.index() + 1)
            || prep.control_source != Reg(prep.iterator.index() + 2)
            || prep.closing_source != Reg(prep.iterator.index() + 3)
            || prep.control_target != call.control
        {
            return None;
        }
        Some(GenericForSource {
            block: preheader,
            prep_instr_ref: Some(prep_instr_ref),
            regs: crate::transformer::RegRange::new(prep.iterator, 4),
        })
    }

    pub(super) fn lower_generic_for_iterator(&self, source: &GenericForSource) -> Vec<HirExpr> {
        (0..source.regs.len)
            .map(|offset| {
                let reg = Reg(source.regs.start.index() + offset);
                // 无 prep 的方言必须读取 preheader 出口；header 上的 control 已是
                // loop-carried phi。5.4/5.5 则读取 prep 的交换前 use，保留第 4 项 closing。
                source.prep_instr_ref.map_or_else(
                    || expr_for_reg_at_block_exit(self.lowering, source.block, reg),
                    |instr_ref| expr_for_reg_use(self.lowering, source.block, instr_ref, reg),
                )
            })
            .collect()
    }
}
