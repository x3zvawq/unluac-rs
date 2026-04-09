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
            // numeric-for 和 repeat-until 的 continue target block 可能在 terminator
            // 前面挂着属于 loop body tail 的普通语句（如 state carry 或 body 尾部
            // 计算）。这些前缀不是循环控制，跳到 block 开头只是让 branch merge 回
            // body tail 的自然路径，语义上不是 continue。
            //
            // generic-for 的 continue target 是 header（GenericForCall +
            // GenericForLoop）。这里的前缀 GenericForCall 是循环控制的一部分（调用
            // 迭代器），跳到 header 等价于"重新迭代"，所以仍应视为 continue。
            let tail_carries_body = matches!(
                loop_candidate.kind_hint,
                LoopKindHint::NumericForLike | LoopKindHint::RepeatLike
            ) && block_has_non_control_prefix(proto, cfg, continue_target);
            for block in &loop_candidate.blocks {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];

                    if edge.to == continue_target
                        && !tail_carries_body
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
