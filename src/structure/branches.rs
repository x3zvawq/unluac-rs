//! 这个文件实现共享分支候选提取。
//!
//! 它依赖 CFG/GraphFacts 已经提供好的 branch 边和后支配信息，负责回答
//! “这个 block 更像哪种 branch 形态”，以及后续多个 pass 共用的 branch-region 事实。
//! 它不会越权做短路、scope 或最终 HIR 结构决策。
//!
//! 例子：
//! - `if cond then ... end` 会产出 `BranchKind::IfThen`
//! - `if cond then ... else ... end` 会产出 `BranchKind::IfElse`
//! - `if not cond then return end; ...` 这种守卫形状会被标成 `BranchKind::Guard`
//! - loop 内嵌套 early return 把严格后支配点推到 synthetic exit 时，单臂归属
//!   仍由 dominance frontier 的真实汇入关系证明，不直接猜 if/else

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts};
use crate::transformer::LoweredProto;

use super::common::{
    BranchCandidate, BranchKind, BranchRegionFact, IrreducibleRegion, LoopCandidate, LoopKindHint,
    SinglePassFenceFact,
};
use super::helpers::{block_has_non_control_prefix, control_prefix_is_movable};
use super::phi_facts::{BranchValueMergeContext, branch_value_merges_in_block};

mod classify;
mod fences;
mod one_arm;
mod regions;

use classify::*;
pub(super) use classify::{find_soft_merge, transparent_jump_target};
use fences::*;
use one_arm::*;
pub(super) use one_arm::{for_loop_body_entry, for_loop_exit_owner};
pub(super) use regions::analyze_branch_regions;
use regions::*;

pub(super) fn analyze_branches(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    loop_candidates: &[LoopCandidate],
    irreducible_regions: &[IrreducibleRegion],
) -> (
    Vec<BranchCandidate>,
    BTreeMap<BlockRef, SinglePassFenceFact>,
) {
    let branch_index = BranchIndex::new(cfg, graph_facts, loop_candidates);
    let mut irreducible_blocks = vec![false; cfg.blocks.len()];
    for block in irreducible_regions
        .iter()
        .flat_map(|region| region.blocks.iter())
    {
        irreducible_blocks[block.index()] = true;
    }
    let mut branch_candidates: Vec<_> = cfg
        .block_order
        .iter()
        .copied()
        .filter(|header| cfg.reachable_blocks.contains(header))
        .filter_map(|header| {
            let (then_edge_ref, else_edge_ref) = cfg.branch_edges(header)?;
            let then_entry = cfg.edges[then_edge_ref.index()].to;
            let else_entry = cfg.edges[else_edge_ref.index()].to;
            if then_entry == else_entry {
                return None;
            }
            classify_loop_break_guard(
                cfg,
                graph_facts,
                &branch_index,
                header,
                then_entry,
                else_entry,
            )
            .or_else(|| {
                classify_loop_continue_guard(
                    proto,
                    cfg,
                    &branch_index,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| {
                classify_infinite_loop_bounded_branch(
                    cfg,
                    graph_facts,
                    &branch_index,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| {
                classify_for_loop_exit_branch(
                    cfg,
                    graph_facts,
                    &branch_index,
                    header,
                    then_entry,
                    else_entry,
                )
            })
            .or_else(|| {
                (!irreducible_blocks[header.index()])
                    .then(|| {
                        classify_loop_exit_bounded_one_arm_branch(
                            cfg,
                            graph_facts,
                            &branch_index,
                            header,
                            then_entry,
                            else_entry,
                        )
                    })
                    .flatten()
            })
            .or_else(|| {
                // loop 内的 continue/break 会把严格后支配点推到 loop 外；必须先用
                // loop owner 与 frontier 汇入事实恢复词法 tail，再考虑普通后支配单臂。
                // 不可规约 SCC 则始终留给 island。
                (!irreducible_blocks[header.index()])
                    .then(|| {
                        classify_postdom_one_arm_branch(graph_facts, header, then_entry, else_entry)
                    })
                    .flatten()
            })
            .or_else(|| {
                // 不可规约 SCC 内的共同后支配点可能位于绕回另一入口之后，不能作为
                // 当前 branch 的词法合流；保留给 island 才能冻结真实跨入口跳转。
                (!irreducible_blocks[header.index()])
                    .then(|| {
                        classify_if_else_branch(cfg, graph_facts, header, then_entry, else_entry)
                    })
                    .flatten()
            })
            .or_else(|| {
                (!irreducible_blocks[header.index()])
                    .then(|| {
                        classify_loop_bounded_one_arm_branch(
                            &branch_index,
                            header,
                            then_entry,
                            else_entry,
                        )
                    })
                    .flatten()
            })
            .or_else(|| Some(classify_guard_branch(header, then_entry, else_entry)))
        })
        .collect();
    refine_loop_iteration_if_else_branches(
        proto,
        cfg,
        graph_facts,
        &branch_index,
        &mut branch_candidates,
    );
    refine_terminal_one_arm_branches(
        cfg,
        &branch_index,
        &irreducible_blocks,
        &mut branch_candidates,
    );
    refine_enclosing_loop_escape_merges(
        proto,
        cfg,
        graph_facts,
        &branch_index,
        &mut branch_candidates,
    );
    let single_pass_fences = refine_single_pass_fences(
        cfg,
        graph_facts,
        dataflow,
        loop_candidates,
        &mut branch_candidates,
    );
    branch_candidates.sort_by_key(|candidate| candidate.header);
    (branch_candidates, single_pass_fences)
}
