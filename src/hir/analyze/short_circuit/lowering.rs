//! 将短路 header 降低为单次求值的 HIR 条件主体。
//!
//! 消费冻结的 branch terminator 与 operand 来源，整段结构由决策 lowering 组织。

use super::*;

pub(crate) fn lower_short_circuit_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    predicate: crate::transformer::InstrRef,
) -> Option<(HirExpr, crate::hir::HirDecisionTestSource)> {
    let LowInstr::Branch(branch) = &lowering.proto.instrs[predicate.index()] else {
        return None;
    };

    Some(lower_branch_subject(
        lowering,
        block,
        predicate,
        branch.cond,
    ))
}

pub(crate) fn lower_short_circuit_subject_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    predicate: crate::transformer::InstrRef,
) -> Option<(HirExpr, crate::hir::HirDecisionTestSource)> {
    let LowInstr::Branch(branch) = &lowering.proto.instrs[predicate.index()] else {
        return None;
    };

    Some(lower_branch_subject_single_eval(
        lowering,
        block,
        predicate,
        branch.cond,
    ))
}
