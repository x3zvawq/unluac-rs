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
//! - same-header 内层 loop 的结构化出口自然汇入外层条件时，不会误记成 continue
//! - 多层嵌套 loop 共用一份 `block -> candidate owner` 索引，入口边与 backedge owner
//!   不会为每个候选重新展开完整 membership 集合

use std::collections::BTreeSet;

use crate::structure::{Cfg, EdgeKind, EdgeRef};
use crate::transformer::LoweredProto;

use super::common::IrreducibleRegion;
use super::common::{BranchCandidate, GotoReason, GotoRequirement, LoopCandidate, LoopKindHint};
use super::helpers::block_has_non_control_prefix;
use super::loops::transparent_loop_exit_target;

pub(super) fn analyze_goto_requirements(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &[BranchCandidate],
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<GotoRequirement> {
    let mut requirements = BTreeSet::new();
    let membership = LoopMembershipIndex::new(cfg, loop_candidates);

    for (candidate_index, loop_candidate) in loop_candidates.iter().enumerate() {
        for &edge_ref in &membership.entry_edges_by_candidate[candidate_index] {
            let edge = cfg.edges[edge_ref.index()];
            if edge.to != loop_candidate.header {
                requirements.insert(GotoRequirement {
                    edge: edge_ref,
                    reason: GotoReason::MultiEntryRegion,
                });
            }
        }

        for edge_ref in &loop_candidate.backedges {
            if backedge_crosses_nested_loop(
                proto,
                cfg,
                loop_candidates,
                &membership.body_scope_owners_by_block,
                loop_candidate,
                *edge_ref,
            ) {
                requirements.insert(GotoRequirement {
                    edge: *edge_ref,
                    reason: GotoReason::CrossLoopContinueLike,
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
                LoopKindHint::NumericForLike
                    | LoopKindHint::RepeatLike
                    | LoopKindHint::WhileTrueLike
            ) && block_has_non_control_prefix(proto, cfg, continue_target);
            for block in &loop_candidate.blocks {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];

                    if edge.to == continue_target
                        && !tail_carries_body
                        && !loop_candidate.backedges.contains(edge_ref)
                        && !loop_candidate.continue_edges.contains(edge_ref)
                        && edge.kind != EdgeKind::Fallthrough
                        && cfg.reachable_blocks.contains(&edge.from)
                        // 如果 edge.from 是某个 branch candidate 的 header，
                        // 且 continue_target 是它的一个分支臂或 merge，
                        // 那么这条边会被结构化 branch lowering 自然吸收
                        // （表现为 `if cond then body end` 的自然落回），
                        // 不应标记为 unstructured continue。
                        && !is_branch_arm_to_target(
                            branch_candidates,
                            edge.from,
                            continue_target,
                        )
                        && !is_same_header_nested_loop_exit(
                            loop_candidates,
                            &membership.exit_owners_by_block,
                            loop_candidate,
                            edge.from,
                        )
                        && !is_degenerate_branch_to_target(cfg, edge.from, continue_target)
                    {
                        requirements.insert(GotoRequirement {
                            edge: *edge_ref,
                            reason: GotoReason::UnstructuredContinueLike,
                        });
                    }
                }
            }
        }
    }

    for irreducible in irreducible_regions {
        for edge_ref in &irreducible.entry_edges {
            requirements.insert(GotoRequirement {
                edge: *edge_ref,
                reason: GotoReason::IrreducibleFlow,
            });
        }
    }

    requirements.into_iter().collect()
}

/// loop 候选 membership 的单次稠密投影。
///
/// candidate identity 仍由切片下标精确区分；same-header 与退化候选不会被按 header
/// 合并。入口边直接从 CFG edge 扫描投影到 owner，避免每个候选再次扫描全部 block。
struct LoopMembershipIndex {
    body_scope_owners_by_block: Vec<Vec<usize>>,
    exit_owners_by_block: Vec<Vec<usize>>,
    entry_edges_by_candidate: Vec<Vec<EdgeRef>>,
}

impl LoopMembershipIndex {
    fn new(cfg: &Cfg, candidates: &[LoopCandidate]) -> Self {
        let mut core_owners_by_block = vec![Vec::new(); cfg.blocks.len()];
        let mut body_scope_owners_by_block = vec![Vec::new(); cfg.blocks.len()];
        let mut exit_owners_by_block = vec![Vec::new(); cfg.blocks.len()];
        for (candidate_index, candidate) in candidates.iter().enumerate() {
            for block in &candidate.blocks {
                core_owners_by_block[block.index()].push(candidate_index);
            }
            for block in &candidate.body_scope_blocks {
                body_scope_owners_by_block[block.index()].push(candidate_index);
            }
            for block in &candidate.exits {
                exit_owners_by_block[block.index()].push(candidate_index);
            }
        }

        let mut entry_edges_by_candidate = vec![Vec::new(); candidates.len()];
        for (edge_index, edge) in cfg.edges.iter().enumerate() {
            if !cfg.reachable_blocks.contains(&edge.from) {
                continue;
            }
            let source_owners = &core_owners_by_block[edge.from.index()];
            for &candidate_index in &core_owners_by_block[edge.to.index()] {
                if source_owners.binary_search(&candidate_index).is_err() {
                    entry_edges_by_candidate[candidate_index].push(EdgeRef(edge_index));
                }
            }
        }

        Self {
            body_scope_owners_by_block,
            exit_owners_by_block,
            entry_edges_by_candidate,
        }
    }
}

fn backedge_crosses_nested_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidates: &[LoopCandidate],
    body_scope_owners_by_block: &[Vec<usize>],
    outer: &LoopCandidate,
    edge_ref: EdgeRef,
) -> bool {
    let edge = cfg.edges[edge_ref.index()];
    edge.to == outer.header
        && body_scope_owners_by_block[edge.from.index()]
            .iter()
            .map(|index| &candidates[*index])
            .any(|inner| {
                inner.header != outer.header
                    && inner.blocks.len() < outer.blocks.len()
                    && inner.blocks.is_subset(&outer.body_scope_blocks)
                    && !nested_loop_exits_to_outer_header(proto, cfg, inner, outer.header)
            })
}

fn nested_loop_exits_to_outer_header(
    proto: &LoweredProto,
    cfg: &Cfg,
    inner: &LoopCandidate,
    outer_header: crate::structure::BlockRef,
) -> bool {
    inner.exits.contains(&outer_header)
        && inner.exits.iter().all(|exit| {
            *exit == outer_header
                || transparent_loop_exit_target(proto, cfg, *exit) == Some(outer_header)
        })
}

fn is_same_header_nested_loop_exit(
    candidates: &[LoopCandidate],
    exit_owners_by_block: &[Vec<usize>],
    outer: &LoopCandidate,
    from: crate::structure::BlockRef,
) -> bool {
    // 内层 exit block 属于外层区域却不属于内层 core；它汇入外层条件是正常的
    // 嵌套控制流，不能因为目标恰是外层 continue target 就要求 goto。
    exit_owners_by_block[from.index()]
        .iter()
        .copied()
        .map(|index| &candidates[index])
        .any(|inner| {
            inner.header == outer.header
                && inner.blocks.len() < outer.blocks.len()
                && inner.blocks.is_subset(&outer.blocks)
        })
}

fn is_degenerate_branch_to_target(
    cfg: &Cfg,
    from: crate::structure::BlockRef,
    target: crate::structure::BlockRef,
) -> bool {
    cfg.branch_edges(from)
        .is_some_and(|(then_edge, else_edge)| {
            cfg.edges[then_edge.index()].to == target && cfg.edges[else_edge.index()].to == target
        })
}

/// 判断 `from` 是否是某个 branch candidate 的 header，且该 branch 的某个分支臂
/// 直接指向 `target`。这种边会被结构化 branch lowering 自然吸收为
/// `if cond then ... end` 的隐式 fallthrough，不需要标记为 unstructured continue。
fn is_branch_arm_to_target(
    branch_candidates: &[BranchCandidate],
    from: crate::structure::BlockRef,
    target: crate::structure::BlockRef,
) -> bool {
    branch_candidates.iter().any(|candidate| {
        candidate.header == from
            && (candidate.then_entry == target
                || candidate.else_entry == Some(target)
                || candidate.merge == Some(target))
    })
}
