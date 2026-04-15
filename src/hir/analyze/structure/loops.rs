//! 这个文件承载 HIR 结构恢复里的 loop 专项逻辑。
//!
//! `while / repeat / numeric-for / generic-for` 的恢复需要同时处理 header phi、
//! backedge 重写、多出口 break pad 和 Lua VM 特有的 for 头部形状。如果这些逻辑继续
//! 混在 `structure.rs` 入口文件里，很快就会把“分支恢复”和“循环恢复”搅成一团，
//! 也更难看出每一步为什么安全。

mod lower;
mod state;

use super::rewrites::{expr_has_temp_ref_in, lvalue_as_expr, rewrite_expr_temps, temp_expr_overrides};
use super::*;

fn merge_target_overrides(
    inherited: &BTreeMap<TempId, HirLValue>,
    local: &BTreeMap<TempId, HirLValue>,
) -> BTreeMap<TempId, HirLValue> {
    // 嵌套 loop 里当前轮次新增的 state override 只覆盖“同一个 temp 的新身份”，
    // 但父层已经稳定好的状态变量身份也必须继续向下传。否则子 loop 体里读取外层
    // carried 值时，又会退回成悬空 temp，后面的 closure/capture/cond 都会一起串坏。
    let mut merged = inherited.clone();
    merged.extend(local.iter().map(|(temp, target)| (*temp, target.clone())));
    merged
}

fn loop_state_init_stmts(plan: &LoopStatePlan) -> Vec<HirStmt> {
    plan.states
        .iter()
        .filter(|state| {
            // 嵌套循环场景下，内层 loop reuse 外层 state target 时 init == target，
            // 会产生无意义的 `x = x` 自赋值；跳过这些 no-op。
            lvalue_as_expr(&state.target) != Some(state.init.clone())
        })
        .map(|state| assign_stmt(vec![state.target.clone()], vec![state.init.clone()]))
        .collect()
}

fn unique_loop_preheader(candidate: &LoopCandidate) -> Option<BlockRef> {
    candidate.preheader
}

fn block_is_terminal_exit(lowering: &ProtoLowering<'_>, block: BlockRef) -> bool {
    let Some(instr_ref) = lowering.cfg.blocks[block.index()].instrs.last() else {
        return false;
    };
    matches!(
        lowering.proto.instrs[instr_ref.index()],
        LowInstr::Return(_) | LowInstr::TailCall(_)
    )
}

fn loop_branch_body_and_exit(
    lowering: &ProtoLowering<'_>,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<(BlockRef, BlockRef)> {
    let instr = lowering.cfg.terminator(&lowering.proto.instrs, header)?;
    let LowInstr::Branch(branch) = instr else {
        return None;
    };
    let then_target = lowering.cfg.instr_to_block[branch.then_target.index()];
    let else_target = lowering.cfg.instr_to_block[branch.else_target.index()];

    if loop_blocks.contains(&then_target) && !loop_blocks.contains(&else_target) {
        Some((then_target, else_target))
    } else if !loop_blocks.contains(&then_target) && loop_blocks.contains(&else_target) {
        Some((else_target, then_target))
    } else {
        None
    }
}

fn loop_value_has_inside_and_outside_incoming(value: &LoopValueMerge) -> bool {
    !value.inside_arm.is_empty() && !value.outside_arm.is_empty()
}

fn loop_value_incoming_all_within_blocks(
    value: &LoopValueMerge,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    value.inside_arm.all_preds_within(allowed_blocks)
        && value.outside_arm.all_preds_within(allowed_blocks)
}

fn single_fixed_def_expr(
    lowering: &ProtoLowering<'_>,
    defs: impl IntoIterator<Item = crate::cfg::DefId>,
) -> Option<HirExpr> {
    let mut defs = defs.into_iter();
    let def = defs.next()?;
    if defs.next().is_some() {
        return None;
    }
    Some(HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]))
}
