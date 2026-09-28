//! 保留比较输入树化前的原准备写入身份。
//!
//! 消费 Dataflow 的 use/Def、home 和 epoch，发布单次准备证书；完整源码前缀由帧 owner 验证。

use crate::hir::common::TempId;
use crate::structure::{Cfg, DataflowFacts, SsaValue};
use crate::transformer::{CallKind, CondOperand, InstrRef, LowInstr, LoweredProto, ResultPack};

use super::{
    SlotEpochFacts,
    operand_preparations::{self, OperandPreparation},
};

#[derive(Debug, Clone)]
pub(super) struct ComparisonPreparation {
    pub(super) lhs: bool,
    pub(super) operand: OperandPreparation,
    pub(super) call: InstrRef,
    pub(super) call_result: TempId,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    site: InstrRef,
    operands: [CondOperand; 2],
) -> Option<ComparisonPreparation> {
    for (index, operand) in operands.iter().enumerate() {
        let (CondOperand::Reg(reg), CondOperand::Reg(other)) = (*operand, operands[1 - index])
        else {
            continue;
        };
        let Some(operand) =
            operand_preparations::collect(proto, cfg, dataflow, epochs, fixed_temps, site, reg)
        else {
            continue;
        };
        let SsaValue::Def(other_def) = dataflow.use_value(site, other) else {
            continue;
        };
        let call_result = TempId(other_def.index());
        if fixed_temps[other_def.index()] != call_result {
            continue;
        }
        let call_site = dataflow.def_instr(other_def);
        let block = cfg.instr_to_block[site.index()];
        if dataflow.def_block(other_def) != block {
            continue;
        }
        let LowInstr::Call(call) = &proto.instrs[call_site.index()] else {
            continue;
        };
        if call.kind != CallKind::Normal
            || call.callee != other
            || !matches!(call.results, ResultPack::Fixed(pack) if pack.len == 1 && pack.start == other)
            || other.index() != reg.index() + 1
        {
            continue;
        }
        // 外层 callee 的准备先于内层参数 CALL。证书必须从它之前开始，不能仅按
        // 最后执行的 CALL 指令号声称准备顺序；已有 callee/跨块准备不由此查询猜测。
        let SsaValue::Def(callee) = dataflow.use_value(call_site, call.callee) else {
            continue;
        };
        if dataflow.def_block(callee) != block
            || operand.read.index() >= dataflow.def_instr(callee).index()
        {
            continue;
        }
        return Some(ComparisonPreparation {
            lhs: index == 0,
            operand,
            call: call_site,
            call_result,
        });
    }
    None
}
