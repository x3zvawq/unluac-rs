//! 这个文件实现必须保留跳转的结构约束。
//!
//! 它依赖 loop/branch/irreducible region 已经给出的结构候选，负责把这些候选明确
//! 吞不掉的边提前标成 `GotoRequirement`，避免 HIR/AST 再去临时猜“这里是不是还要
//! 保留 label/goto”。
//! 它不会越权决定最终 `goto/label` 语法，只表达“哪些跳转现在还不能被结构化吸收”。
//!
//! 例子：
//! - `break` 或 `continue` 形状如果提前跳出了当前 loop body，会被记成
//!   `UnstructuredBreakLike / UnstructuredContinueLike`
//! - branch region 内部如果有一条边直接跳到 merge 之外，会被记成
//!   `CrossStructureJump`

use std::collections::BTreeSet;

use crate::cfg::{Cfg, EdgeKind};
use crate::transformer::{LowInstr, LoweredProto};

use super::common::IrreducibleRegion;
use super::common::{BranchRegionFact, GotoReason, GotoRequirement, LoopCandidate, LoopKindHint};
use super::helpers::{collect_region_entry_edges, collect_region_exit_edges};

pub(super) fn analyze_goto_requirements(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    branch_regions: &[BranchRegionFact],
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<GotoRequirement> {
    let mut requirements = BTreeSet::new();

    for loop_candidate in loop_candidates {
        for edge_ref in collect_region_entry_edges(cfg, &loop_candidate.blocks) {
            let edge = cfg.edges[edge_ref.index()];
            if edge.to != loop_candidate.header {
                requirements.insert(GotoRequirement {
                    from: edge.from,
                    to: edge.to,
                    reason: GotoReason::MultiEntryRegion,
                });
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

    for branch_region in branch_regions {
        for edge_ref in collect_region_exit_edges(cfg, &branch_region.flow_blocks) {
            let edge = cfg.edges[edge_ref.index()];
            if edge.to != branch_region.merge {
                requirements.insert(GotoRequirement {
                    from: edge.from,
                    to: edge.to,
                    reason: GotoReason::CrossStructureJump,
                });
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
