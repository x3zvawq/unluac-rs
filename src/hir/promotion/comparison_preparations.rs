//! 保存比较操作数树化前的一次原准备身份。
//!
//! Dataflow 的比较 use→Def 证明哪次 GETUPVAL/字面量写入先于对侧普通 CALL 的准备。
//! 例如 `captured == f()` 的 GETUPVAL r0 与 CALL r1，或 `1000 < tonumber(f())`
//! 的 LOADI r0 与外层 CALL r1；内联成 UpvalueRef/字面量后不能再用值或槽号猜回该次写。
//! 本模块只发布单用、同块、同 epoch 的准备证书；完整源码前缀和词法末端仍由
//! source_frames 验证，不把准备写等同于提前释放旧对象。每条比较只查两个原 use，
//! 不扫描后缀，也不按 UpvalueId 合并不同读取。

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
