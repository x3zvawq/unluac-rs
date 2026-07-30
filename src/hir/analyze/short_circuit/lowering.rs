//! 这个子模块负责把短路候选里的 header branch 直接降成 HIR 测试表达式。
//!
//! 它依赖 CFG 末尾 branch terminator 和前面的 branch-subject lowering，只提供“单次求值的
//! 条件主体长什么样”，不会在这里决定整段结构该如何收束。
//! 例如：短路 header 的 `Branch(Truthy r0)` 会先在这里得到 `r0` 这个测试表达式。

use super::*;

pub(crate) fn lower_short_circuit_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    predicate: crate::transformer::InstrRef,
) -> Option<HirExpr> {
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
) -> Option<HirExpr> {
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
