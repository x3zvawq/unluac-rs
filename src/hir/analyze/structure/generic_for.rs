//! Generic-for iterator 表达式恢复。
//!
//! StructurePlan 已经冻结了 `prep/call/loop` identity 与 iterator 源寄存器区间；
//! 这里只把这些稳定输入翻译成 HIR 表达式，不再重新识别 VM 协议。

use crate::hir::common::HirExpr;
use crate::structure::BlockRef;
use crate::transformer::Reg;

use super::super::exprs::{expr_for_reg_at_block_exit, expr_for_reg_use};
use super::super::lower::ProtoLowering;

pub(super) fn lower_generic_for_iterator(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
) -> Vec<HirExpr> {
    (0..protocol.iterator.len)
        .map(|offset| {
            let reg = Reg(protocol.iterator.start.index() + offset);
            // 无 prep 的方言必须读取 preheader 出口；header 上的 control 已是
            // loop-carried phi。5.4/5.5 则读取 prep 的交换前 use，保留第 4 项 closing。
            protocol.prep_instr.map_or_else(
                || expr_for_reg_at_block_exit(lowering, preheader, reg),
                |instr_ref| expr_for_reg_use(lowering, preheader, instr_ref, reg),
            )
        })
        .collect()
}
