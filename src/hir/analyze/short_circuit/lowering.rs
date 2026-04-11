//! 这个子模块负责把短路候选里的 header branch 直接降成 HIR 测试表达式。
//!
//! 它依赖 CFG 末尾 branch terminator 和前面的 branch-subject lowering，只提供“单次求值的
//! 条件主体长什么样”，不会在这里决定整段结构该如何收束。
//! 例如：短路 header 的 `Branch(Truthy r0)` 会先在这里得到 `r0` 这个测试表达式。

use super::*;

pub(crate) fn lower_short_circuit_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<HirExpr> {
    let instr_ref = lowering.cfg.blocks[block.index()].instrs.last()?;
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr_ref.index()] else {
        return None;
    };

    Some(lower_branch_subject(
        lowering,
        block,
        instr_ref,
        branch.cond,
    ))
}

pub(crate) fn lower_short_circuit_subject_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<HirExpr> {
    let instr_ref = lowering.cfg.blocks[block.index()].instrs.last()?;
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr_ref.index()] else {
        return None;
    };

    Some(lower_branch_subject_inline(
        lowering,
        block,
        instr_ref,
        branch.cond,
    ))
}

pub(crate) fn lower_short_circuit_subject_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<HirExpr> {
    let instr_ref = lowering.cfg.blocks[block.index()].instrs.last()?;
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr_ref.index()] else {
        return None;
    };

    Some(lower_branch_subject_single_eval(
        lowering,
        block,
        instr_ref,
        branch.cond,
    ))
}

pub(crate) fn lower_value_leaf_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    block: BlockRef,
) -> Option<HirExpr> {
    if short.nodes.iter().any(|node| node.header == block) {
        return lower_short_circuit_subject_single_eval(lowering, block);
    }

    let def = value_leaf_latest_local_def(short, block)?;
    // 优先用 inline（不深度展开 call）来恢复 leaf 值表达式；
    // 只有 inline 无法给出结果时（例如 Move 指令），才退回 single_eval。
    //
    // 避免的问题：GETTABLE 叶子的 base 寄存器是已物化 temp（如 GetBuff 调用结果 t87）时，
    // single_eval 会沿 expr_for_reg_use_single_eval → expr_for_fixed_def(call) 路径把整条
    // call 链重新展开，生成重复调用的表达式，而不是引用已有的 TempRef(t87)。
    expr_for_fixed_def(lowering, def).or_else(|| expr_for_fixed_def_single_eval(lowering, def))
}

/// 语句级短路恢复已经先把 leaf block 自己的副作用语句物化出来了。
///
/// 因此这里不能再把 leaf 结果重新 inline 成 `call(...)` 之类的表达式，而是应该优先
/// 引用“这个 block 最后一次给 result_reg 写出的稳定绑定”；若本 block 没有重写它，
/// 就回退到 block 入口时已经可见的那个值。
pub(crate) fn lower_materialized_value_leaf_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    block: BlockRef,
) -> Option<HirExpr> {
    let reg = short.result_reg?;
    if short.nodes.iter().any(|node| node.header == block) {
        return lower_short_circuit_subject(lowering, block);
    }

    if let Some(def) = value_leaf_latest_local_def(short, block) {
        return Some(HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]));
    }

    Some(expr_for_reg_at_block_entry(lowering, block, reg))
}

fn value_leaf_latest_local_def(short: &ShortCircuitCandidate, block: BlockRef) -> Option<DefId> {
    short
        .value_incomings
        .iter()
        .find(|incoming| incoming.pred == block)
        .and_then(|incoming| incoming.latest_local_def)
}
