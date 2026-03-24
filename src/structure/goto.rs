//! 这个文件实现必须保留跳转的结构约束。
//!
//! 目标不是做最终 `goto/label` 决策，而是把当前结构候选无法吞掉的边先明确标记。

use std::collections::BTreeSet;

use crate::cfg::Cfg;

use super::branches::collect_branch_region_blocks;
use super::common::{BranchCandidate, GotoReason, GotoRequirement, LoopCandidate};
use super::helpers::IrreducibleRegion;

pub(super) fn analyze_goto_requirements(
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
            for block in &loop_candidate.blocks {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];
                    if edge.to == continue_target
                        && !loop_candidate.backedges.contains(edge_ref)
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
