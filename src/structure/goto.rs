//! 这个文件实现必须保留跳转的结构约束。
//!
//! 目标不是做最终 `goto/label` 决策，而是把当前结构候选无法吞掉的边先明确标记。

use std::collections::BTreeSet;

use crate::cfg::{Cfg, EdgeKind};
use crate::transformer::{LowInstr, LoweredProto};

use super::branches::collect_branch_region_blocks;
use super::common::{BranchCandidate, GotoReason, GotoRequirement, LoopCandidate, LoopKindHint};
use super::helpers::IrreducibleRegion;

pub(super) fn analyze_goto_requirements(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &[BranchCandidate],
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<GotoRequirement> {
    let mut requirements = BTreeSet::new();

    for loop_candidate in loop_candidates {
        for block in &loop_candidate.blocks {
            for edge_ref in &cfg.preds[block.index()] {
                let edge = cfg.edges[edge_ref.index()];
                if cfg.reachable_blocks.contains(&edge.from)
                    && !loop_candidate.blocks.contains(&edge.from)
                    && *block != loop_candidate.header
                {
                    requirements.insert(GotoRequirement {
                        from: edge.from,
                        to: *block,
                        reason: GotoReason::MultiEntryRegion,
                    });
                }
            }
        }

        if let Some(continue_target) = loop_candidate.continue_target {
            let numeric_for_tail_carries_body = loop_candidate.kind_hint
                == LoopKindHint::NumericForLike
                && block_has_non_control_prefix(proto, cfg, continue_target);
            for block in &loop_candidate.blocks {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];
                    // 顺着线性 body tail 自然落到 continue target 的边，本质上还是
                    // 当前循环的正常执行路径，不应该被提前标成 continue-like requirement。
                    // 这里保留的只应该是“主动提前跳到 continue target”的控制边，
                    // 这样 HIR 才能区分自然 fallthrough 和真正的 continue 语义。
                    //
                    // numeric-for 的 continue target 是 `FORLOOP` 所在 block。本来如果这个
                    // block 前面还挂着普通 low-IR 指令，那它就已经是 loop tail 的一部分：
                    // 提前跳到 block 开头仍会执行这些语句，语义上不是 `continue`，只是
                    // branch 正常 merge 回 tail。像 `branch_state_carry` 这类 case 必须在
                    // facts 层把它排除掉，不能等 HIR 再兜底。
                    if edge.to == continue_target
                        && !numeric_for_tail_carries_body
                        && !loop_candidate.backedges.contains(edge_ref)
                        && edge.kind != EdgeKind::Fallthrough
                        && cfg.reachable_blocks.contains(&edge.from)
                    {
                        requirements.insert(GotoRequirement {
                            from: edge.from,
                            to: edge.to,
                            reason: GotoReason::UnstructuredContinueLike,
                        });
                    }
                }
            }
        }
    }

    for irreducible in irreducible_regions {
        for edge_ref in &irreducible.entry_edges {
            let edge = cfg.edges[edge_ref.index()];
            requirements.insert(GotoRequirement {
                from: edge.from,
                to: edge.to,
                reason: GotoReason::IrreducibleFlow,
            });
        }
    }

    for branch_candidate in branch_candidates {
        let Some(merge) = branch_candidate.merge else {
            continue;
        };
        let region_blocks = collect_branch_region_blocks(cfg, branch_candidate, merge, None);
        for block in &region_blocks {
            for edge_ref in &cfg.succs[block.index()] {
                let edge = cfg.edges[edge_ref.index()];
                if cfg.reachable_blocks.contains(&edge.to)
                    && !region_blocks.contains(&edge.to)
                    && edge.to != merge
                {
                    requirements.insert(GotoRequirement {
                        from: edge.from,
                        to: edge.to,
                        reason: GotoReason::CrossStructureJump,
                    });
                }
            }
        }
    }

    requirements.into_iter().collect()
}

fn block_has_non_control_prefix(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::cfg::BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let Some(last_instr_ref) = range.last() else {
        return false;
    };
    let Some(last_instr) = proto.instrs.get(last_instr_ref.index()) else {
        return false;
    };

    let body_end = if is_control_terminator(last_instr) {
        range.end().saturating_sub(1)
    } else {
        range.end()
    };
    range.start.index() < body_end
}

fn is_control_terminator(instr: &LowInstr) -> bool {
    matches!(
        instr,
        LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::Return(_)
            | LowInstr::TailCall(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_)
    )
}
