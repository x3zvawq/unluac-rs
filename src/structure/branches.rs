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

/// 恢复被编译器消去回边的 `repeat ... until true`。
///
/// 这类区域有一个被多条正常路径共享的线性 tail，同时若干早退路径直接进入 tail
/// 之后的严格合流点。把外层 branch 的 continuation 收到 tail 后，最终 plan 就能用
/// 一个 single-pass containment owner 承载所有跳过 tail 的 `break`。
fn refine_single_pass_fences(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &mut [BranchCandidate],
) -> BTreeMap<BlockRef, SinglePassFenceFact> {
    let mut outer_by_exit = vec![None; cfg.blocks.len()];
    let mut ambiguous_exit = vec![false; cfg.blocks.len()];
    let mut branches_by_exit = vec![Vec::new(); cfg.blocks.len()];
    for (index, candidate) in branch_candidates.iter().enumerate() {
        let Some(exit) = candidate.merge.filter(|exit| *exit != cfg.exit_block) else {
            continue;
        };
        branches_by_exit[exit.index()].push(index);
        let slot = &mut outer_by_exit[exit.index()];
        let Some(current) = *slot else {
            *slot = Some(index);
            continue;
        };
        let current_header = branch_candidates[current].header;
        if graph_facts.dominates(candidate.header, current_header) {
            *slot = Some(index);
        } else if !graph_facts.dominates(current_header, candidate.header) {
            ambiguous_exit[exit.index()] = true;
        }
    }

    let branch_headers = branch_candidates
        .iter()
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();
    let loop_headers = loop_candidates
        .iter()
        .map(|candidate| candidate.header)
        .collect::<BTreeSet<_>>();
    let mut fences = BTreeMap::new();
    for (exit_index, candidate_index) in outer_by_exit.into_iter().enumerate() {
        let Some(candidate_index) = candidate_index else {
            continue;
        };
        if ambiguous_exit[exit_index] {
            continue;
        }
        let exit = BlockRef(exit_index);
        let header = branch_candidates[candidate_index].header;
        let mut tails = cfg.preds[exit.index()].iter().filter_map(|edge_ref| {
            let edge = cfg.edges[edge_ref.index()];
            let tail = edge.from;
            if !cfg.reachable_blocks.contains(&tail)
                || !graph_facts.dominates(header, tail)
                || branch_headers.contains(&tail)
                || loop_headers.contains(&tail)
                || cfg.succs[tail.index()].as_slice() != [*edge_ref]
            {
                return None;
            }
            let incoming = cfg.preds[tail.index()]
                .iter()
                .filter(|incoming| {
                    let source = cfg.edges[incoming.index()].from;
                    cfg.reachable_blocks.contains(&source) && graph_facts.dominates(header, source)
                })
                .count();
            (incoming >= 2).then_some((tail, *edge_ref))
        });
        let Some((tail, tail_edge)) = tails.next() else {
            continue;
        };
        if tails.next().is_some() {
            continue;
        }
        // loop header 也可能是外层迭代的合法 single-pass continuation，但此时 fence
        // 必须完整位于该 natural loop 内。否则这里只是循环前的普通 branch 汇入
        // header，真实 backedge 会被误收为 early escape，并把 branch merge 提前。
        if loop_headers.contains(&exit)
            && !loop_candidates.iter().any(|owner| {
                owner.header == exit
                    && owner.blocks.contains(&header)
                    && owner.blocks.contains(&tail)
            })
        {
            continue;
        }

        let escape_edges = cfg.preds[exit.index()]
            .iter()
            .copied()
            .filter(|edge_ref| {
                let source = cfg.edges[edge_ref.index()].from;
                source != tail
                    && cfg.reachable_blocks.contains(&source)
                    && graph_facts.dominates(header, source)
            })
            .collect::<BTreeSet<_>>();
        // 普通 `if cond then <多路值计算>; tail end` 也会形成“多前驱 tail +
        // 另一臂直达 exit”，但所有直达 exit 的边都位于 tail 所属 arm 之外。
        // 真正需要一次性 fence 的 break 至少有一条嵌在同一 tail owner 内；否则
        // 现有 branch/value decision 已能直接表达，不能为了形状相似改写 branch merge。
        let tail_owner = graph_facts.dominator_tree.parent[tail.index()];
        let has_nested_escape = tail_owner.is_some_and(|owner| {
            owner == header
                || escape_edges
                    .iter()
                    .any(|edge_ref| graph_facts.dominates(owner, cfg.edges[edge_ref.index()].from))
        });
        if escape_edges.is_empty()
            || !has_nested_escape
            || closed_if_else_owns_value_result(
                graph_facts,
                dataflow,
                &branch_candidates[candidate_index],
                tail,
                tail_edge,
                exit,
                &escape_edges,
            )
            || loop_candidates.iter().any(|owner| {
                owner.exits.contains(&exit)
                    && owner.body_scope_blocks.contains(&header)
                    && owner.body_scope_blocks.contains(&tail)
                    && escape_edges.iter().all(|edge_ref| {
                        owner
                            .body_scope_blocks
                            .contains(&cfg.edges[edge_ref.index()].from)
                    })
            })
        {
            continue;
        }
        let owns = |block| {
            block != cfg.exit_block
                && cfg.reachable_blocks.contains(&block)
                && (block == tail
                    || graph_facts.dominates(header, block)
                        && !graph_facts.dominates(tail, block)
                        && !graph_facts.dominates(exit, block))
        };
        // header 的支配关系已经排除了普通外部入口；这里只需检查重新加入的 tail
        // 以及 fence 出口。这样验证成本与边界边数相关，不再扫描整个支配子树。
        let tail_is_internal = cfg.preds[tail.index()].iter().all(|edge| {
            let predecessor = cfg.edges[edge.index()].from;
            !cfg.reachable_blocks.contains(&predecessor) || owns(predecessor)
        });
        let escapes_are_internal = escape_edges
            .iter()
            .all(|edge| owns(cfg.edges[edge.index()].from));
        if !owns(header) || !tail_is_internal || !escapes_are_internal {
            continue;
        }

        for nested in &branches_by_exit[exit.index()] {
            if graph_facts.dominates(header, branch_candidates[*nested].header) {
                branch_candidates[*nested].merge = Some(tail);
            }
        }
        fences.insert(header, SinglePassFenceFact { exit, escape_edges });
    }
    fences
}

/// value-result 已经证明两臂在严格后支配点闭合时，shared-tail 只是其中一臂的
/// 实现形状；改成 single-pass 会把正常分支的结果边误解释成 `break`。
fn closed_if_else_owns_value_result(
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    candidate: &BranchCandidate,
    tail: BlockRef,
    tail_edge: EdgeRef,
    exit: BlockRef,
    escape_edges: &BTreeSet<EdgeRef>,
) -> bool {
    let Some(else_entry) = candidate.else_entry else {
        return false;
    };
    if candidate.kind != BranchKind::IfElse
        || candidate.merge != Some(exit)
        || graph_facts.nearest_common_postdom(candidate.then_entry, else_entry) != Some(exit)
    {
        return false;
    }

    // 普通 if/else 的线性 tail 只属于一臂，另一臂直接给 result phi 供值；真正的
    // single-pass shared tail 会被两臂共同到达，不能仅因 exit 上恰好存在 phi 就拦截。
    let (then_owns_tail, else_owns_tail) = (
        graph_facts.dominates(candidate.then_entry, tail),
        graph_facts.dominates(else_entry, tail),
    );
    let result_arm = match (then_owns_tail, else_owns_tail) {
        (true, false) => else_entry,
        (false, true) => candidate.then_entry,
        (true, true) | (false, false) => return false,
    };

    // Dataflow 的 block range 是稠密索引；每个 exit 只检查自身 canonical/live phi，
    // 并要求当前两臂的物理边给同一个非平凡 phi 提供不同值。
    dataflow.phi_candidates_in_block(exit).iter().any(|phi| {
        let Some(tail_value) = phi
            .incoming
            .iter()
            .find(|incoming| incoming.edge == Some(tail_edge))
            .map(|incoming| incoming.value)
        else {
            return false;
        };
        let mut covered_escapes = 0;
        let mut differs = false;
        for incoming in &phi.incoming {
            if incoming
                .edge
                .is_some_and(|edge_ref| escape_edges.contains(&edge_ref))
            {
                if !incoming
                    .pred
                    .is_some_and(|pred| graph_facts.dominates(result_arm, pred))
                {
                    return false;
                }
                covered_escapes += 1;
                differs |= incoming.value != tail_value;
            }
        }
        covered_escapes == escape_edges.len() && differs
    })
}

fn refine_enclosing_loop_escape_merges(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    branch_candidates: &mut [BranchCandidate],
) {
    // 先消费现有 branch/loop owner，再用 soft-merge 与 nested branch 自身的出口合同
    // 确认本轮合流；不为每个 outer branch 重新复制 block 集或扫描 CFG。
    let snapshot = branch_candidates.to_vec();
    let mut nested_by_merge = vec![Vec::new(); cfg.blocks.len()];
    for candidate in &snapshot {
        if matches!(candidate.kind, BranchKind::IfThen | BranchKind::Guard)
            && candidate.else_entry.is_none()
            && let Some(merge) = candidate.merge
        {
            nested_by_merge[merge.index()].push(candidate);
        }
    }
    let mut branch_by_header = vec![None; cfg.blocks.len()];
    for candidate in &snapshot {
        branch_by_header[candidate.header.index()] = Some(candidate);
    }
    let mut refinements = vec![None; cfg.blocks.len()];
    for outer in &snapshot {
        let (Some(strict_merge), Some(else_entry)) = (outer.merge, outer.else_entry) else {
            continue;
        };
        if outer.kind != BranchKind::IfElse || strict_merge == cfg.exit_block {
            continue;
        }
        let Some(soft_merge) =
            find_soft_merge(cfg, graph_facts, outer.header, outer.then_entry, else_entry)
        else {
            continue;
        };
        let Some(owner) = branch_index
            .body_loops(outer.header)
            .filter(|owner| {
                (owner.exits.contains(&strict_merge)
                    || loop_iteration_escape_entry(proto, cfg, owner, strict_merge)
                    || branch_by_header[strict_merge.index()].is_some_and(|candidate| {
                        branch_has_loop_escape_arm(proto, cfg, owner, candidate)
                    }))
                    && [outer.header, outer.then_entry, else_entry]
                        .into_iter()
                        .all(|block| owner.body_scope_blocks.contains(&block))
                    && (owner.body_scope_blocks.contains(&soft_merge)
                        || owner.blocks.contains(&soft_merge)
                        || owner.control_blocks.contains(&soft_merge)
                        || owner.continue_target == Some(soft_merge))
            })
            .min_by_key(|owner| owner.body_scope_blocks.len())
        else {
            continue;
        };
        let mut nested = owner
            .exits
            .iter()
            .chain(std::iter::once(&soft_merge))
            .flat_map(|merge| nested_by_merge[merge.index()].iter())
            .copied()
            .filter(|candidate| {
                candidate.header != soft_merge
                    && graph_facts.dominates(outer.then_entry, candidate.header)
                        != graph_facts.dominates(else_entry, candidate.header)
                    && (candidate.merge == Some(soft_merge)
                        || branch_has_loop_escape_arm(proto, cfg, owner, candidate))
            })
            .collect::<Vec<_>>();
        for entry in [outer.then_entry, else_entry] {
            let Some(candidate) = branch_by_header[entry.index()] else {
                continue;
            };
            if candidate.header != soft_merge
                && branch_has_loop_escape_arm(proto, cfg, owner, candidate)
                && nested
                    .iter()
                    .all(|nested| nested.header != candidate.header)
            {
                nested.push(candidate);
            }
        }
        if nested.is_empty()
            || nested.iter().any(|candidate| candidate.merge.is_none())
            || !nested.iter().any(|candidate| {
                candidate.merge == Some(strict_merge)
                    || candidate.merge == Some(soft_merge)
                    || branch_has_loop_escape_arm(proto, cfg, owner, candidate)
            })
        {
            continue;
        }
        refinements[outer.header.index()] = Some((outer.then_entry, else_entry, soft_merge));
        for candidate in nested {
            let Some(merge) = candidate.merge else {
                continue;
            };
            if merge == soft_merge {
                continue;
            }
            refinements[candidate.header.index()] = Some((candidate.then_entry, merge, soft_merge));
        }
    }
    for candidate in branch_candidates {
        let Some((then_entry, else_entry, merge)) = refinements[candidate.header.index()] else {
            continue;
        };
        candidate.then_entry = then_entry;
        candidate.else_entry = Some(else_entry);
        candidate.merge = Some(merge);
        candidate.kind = BranchKind::IfElse;
    }
}

/// 恢复“条件成立时直接结束本轮，否则继续执行共享 tail”的源码分支。
///
/// 这类边在 CFG 上不会流回 branch 的词法 continuation，因此普通 postdom 会把
/// continuation 推到 loop 外。continue target 或其唯一 backedge pad 已经由 loop
/// candidate 冻结，可以在这里作为精确的 escape arm 证据。
fn classify_loop_continue_guard(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let owner = branch_index
        .endpoint_loops(header)
        .filter(|candidate| {
            loop_candidate_owns_endpoint(cfg, candidate, header)
                && loop_candidate_owns_endpoint(cfg, candidate, then_entry)
                && loop_candidate_owns_endpoint(cfg, candidate, else_entry)
        })
        .filter_map(|candidate| {
            let then_escape = loop_iteration_escape_entry(proto, cfg, candidate, then_entry);
            let else_escape = loop_iteration_escape_entry(proto, cfg, candidate, else_entry);
            (then_escape != else_escape).then_some((candidate, then_escape))
        })
        .min_by_key(|(candidate, _)| candidate.body_scope_blocks.len())?;
    let (then_entry, merge, invert_hint) = if owner.1 {
        (then_entry, else_entry, false)
    } else {
        (else_entry, then_entry, true)
    };
    // 普通 while/generic-for 的 normal arm 若只在 escape 汇入，就是源码 gated tail。
    if matches!(
        owner.0.kind_hint,
        LoopKindHint::WhileLike | LoopKindHint::WhileTrueLike | LoopKindHint::GenericForLike
    ) && branch_index.has_single_local_join(merge, then_entry)
    {
        return None;
    }
    Some(BranchCandidate {
        header,
        then_entry,
        else_entry: None,
        merge: Some(merge),
        kind: BranchKind::Guard,
        invert_hint,
    })
}

/// 恢复“一臂退出当前 loop，另一臂继续到共享尾”的条件 break。
///
/// 编译器常把 break 先落到一个纯 jump pad，再跳到 loop continuation。若不在 branch
/// 层认领这个 pad，两个物理条件边都会退化为 fallthrough，HIR 随后会把 break 与
/// repeat latch 串在同一语句块中。这里只接受已冻结 loop exit 或其唯一透明 pad，且
/// 排除 loop 自己的 control header。
fn classify_loop_break_guard(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let (_, then_break) = branch_index
        .endpoint_loops(header)
        .filter(|candidate| {
            !candidate.control_blocks.contains(&header)
                && candidate.condition_header != Some(header)
                && loop_candidate_owns_endpoint(cfg, candidate, header)
        })
        .filter_map(|candidate| {
            let then_break = loop_break_entry(cfg, candidate, then_entry);
            let else_break = loop_break_entry(cfg, candidate, else_entry);
            (then_break != else_break).then_some((candidate, then_break))
        })
        .min_by_key(|(candidate, _)| candidate.body_scope_blocks.len())?;
    let (then_entry, merge, invert_hint) = if then_break {
        (then_entry, else_entry, false)
    } else {
        (else_entry, then_entry, true)
    };
    if graph_facts.post_dominates(then_entry, merge) {
        return None;
    }
    Some(BranchCandidate {
        header,
        then_entry,
        else_entry: None,
        merge: Some(merge),
        kind: BranchKind::Guard,
        invert_hint,
    })
}

fn loop_break_entry(cfg: &Cfg, candidate: &LoopCandidate, entry: BlockRef) -> bool {
    candidate.continue_target != Some(entry)
        && candidate.condition_header != Some(entry)
        && !candidate.control_blocks.contains(&entry)
        && (candidate.exits.contains(&entry)
            || matches!(cfg.succs[entry.index()].as_slice(), [edge]
                if candidate.exits.contains(&cfg.edges[edge.index()].to))
            || transparent_jump_target(cfg, entry)
                .is_some_and(|target| candidate.exits.contains(&target)))
}

fn loop_candidate_owns_endpoint(cfg: &Cfg, candidate: &LoopCandidate, block: BlockRef) -> bool {
    candidate.body_scope_blocks.contains(&block)
        || candidate.blocks.contains(&block)
        || candidate.control_blocks.contains(&block)
        || candidate.continue_target == Some(block)
        || candidate
            .backedges
            .iter()
            .any(|edge| cfg.edges[edge.index()].from == block)
}

fn branch_has_loop_escape_arm(
    proto: &LoweredProto,
    cfg: &Cfg,
    owner: &LoopCandidate,
    branch: &BranchCandidate,
) -> bool {
    cfg.branch_edges(branch.header)
        .is_some_and(|(truthy, falsy)| {
            [truthy, falsy].into_iter().any(|edge| {
                let target = cfg.edges[edge.index()].to;
                loop_break_entry(cfg, owner, target)
                    || (branch.merge != Some(target)
                        && loop_iteration_escape_entry(proto, cfg, owner, target))
            })
        })
}

fn loop_iteration_escape_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopCandidate,
    entry: BlockRef,
) -> bool {
    let direct_continue = candidate.continue_target == Some(entry)
        && !(matches!(
            candidate.kind_hint,
            LoopKindHint::Unknown
                | LoopKindHint::RepeatLike
                | LoopKindHint::NumericForLike
                | LoopKindHint::WhileTrueLike
        ) && block_has_non_control_prefix(proto, cfg, entry)
            && !control_prefix_is_movable(proto, cfg, entry));
    direct_continue
        || candidate.backedges.iter().any(|edge| {
            cfg.edges[edge.index()].from == entry
                && cfg.edges[edge.index()].to == candidate.header
                && transparent_jump_target(cfg, entry) == Some(candidate.header)
        })
}

fn refine_loop_iteration_if_else_branches(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    branch_candidates: &mut [BranchCandidate],
) {
    let mut candidates_by_header = vec![None; cfg.blocks.len()];
    for candidate in branch_candidates.iter().cloned() {
        let header = candidate.header;
        candidates_by_header[header.index()] = Some(candidate);
    }

    for candidate in branch_candidates {
        let Some(downstream_header) = candidate
            .else_entry
            .is_none()
            .then_some(candidate.merge)
            .flatten()
        else {
            continue;
        };
        let Some(downstream) = &candidates_by_header[downstream_header.index()] else {
            continue;
        };
        let Some((then_edge, else_edge)) = cfg.branch_edges(candidate.header) else {
            continue;
        };
        let then_entry = cfg.edges[then_edge.index()].to;
        let else_entry = cfg.edges[else_edge.index()].to;
        let Some(owner) = branch_index
            .endpoint_loops(candidate.header)
            .filter(|owner| {
                owner.blocks.contains(&candidate.header)
                    && owner.blocks.contains(&then_entry)
                    && owner.blocks.contains(&else_entry)
                    && owner.blocks.contains(&downstream.header)
                    && downstream.merge.is_some_and(|merge| {
                        owner.exits.contains(&merge)
                            || (downstream.kind == BranchKind::Guard
                                && downstream.else_entry.is_none()
                                && branch_has_loop_escape_arm(proto, cfg, owner, downstream)
                                && (owner.blocks.contains(&merge)
                                    || owner.body_scope_blocks.contains(&merge)))
                    })
            })
            .min_by_key(|owner| owner.blocks.len())
        else {
            continue;
        };
        let downstream_escape_merge = (downstream.kind == BranchKind::Guard
            && downstream.else_entry.is_none()
            && branch_has_loop_escape_arm(proto, cfg, owner, downstream))
        .then_some(downstream.merge)
        .flatten()
        .filter(|merge| *merge == then_entry || *merge == else_entry);
        if (branch_index.joins_at(then_entry, else_entry)
            || branch_index.joins_at(else_entry, then_entry))
            && downstream_escape_merge.is_none()
        {
            continue;
        }
        let Some(merge) = downstream_escape_merge.or_else(|| {
            find_soft_merge(cfg, graph_facts, candidate.header, then_entry, else_entry)
        }) else {
            continue;
        };
        if !owner.blocks.contains(&merge) && !owner.body_scope_blocks.contains(&merge) {
            continue;
        }

        candidate.then_entry = then_entry;
        candidate.else_entry = Some(else_entry);
        candidate.merge = Some(merge);
        candidate.kind = BranchKind::IfElse;
        candidate.invert_hint = false;
    }
}

pub(super) fn analyze_branch_regions(
    _cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_candidates: &[BranchCandidate],
    single_pass_fences: &BTreeMap<BlockRef, SinglePassFenceFact>,
) -> Vec<BranchRegionFact> {
    let mut branch_regions = branch_candidates
        .iter()
        .filter_map(|candidate| {
            let merge = candidate.merge?;
            let single_pass_fence = single_pass_fences.get(&candidate.header).cloned();
            Some(BranchRegionFact::new(
                graph_facts,
                candidate.header,
                merge,
                candidate.kind,
                single_pass_fence,
            ))
        })
        .collect::<Vec<_>>();

    branch_regions.sort_by_key(|fact| (fact.header, fact.merge));
    branch_regions
}

/// Branch 分析只消费已经计算好的 dominance frontier 与稠密 loop containment。
///
/// `dominance_frontier[from]` 包含 `to` 时，存在一条由 `from` 支配的路径真实汇入
/// `to`；这正是 branch arm 可以把 `to` 当作词法 continuation 的证明。它比任意
/// CFG reachability 更强，也避免按每个 branch source 重新遍历整张图。
struct BranchIndex<'a> {
    graph_facts: &'a GraphFacts,
    loop_candidates: &'a [LoopCandidate],
    loops_by_endpoint: Vec<Vec<usize>>,
    loops_by_body_block: Vec<Vec<usize>>,
    loop_headers: Vec<bool>,
    local_frontiers: Vec<FrontierShape>,
    exit_block: BlockRef,
}

#[derive(Clone, Copy)]
enum FrontierShape {
    Empty,
    One(BlockRef),
    Multiple,
}

impl FrontierShape {
    fn push(self, block: BlockRef) -> Self {
        match self {
            Self::Empty => Self::One(block),
            Self::One(existing) if existing == block => self,
            Self::One(_) | Self::Multiple => Self::Multiple,
        }
    }
}

impl<'a> BranchIndex<'a> {
    fn new(cfg: &Cfg, graph_facts: &'a GraphFacts, loop_candidates: &'a [LoopCandidate]) -> Self {
        let mut loops_by_endpoint = vec![Vec::new(); cfg.blocks.len()];
        let mut loops_by_body_block = vec![Vec::new(); cfg.blocks.len()];
        let mut loop_headers = vec![false; cfg.blocks.len()];
        let mut seen = vec![usize::MAX; cfg.blocks.len()];

        for (candidate_id, candidate) in loop_candidates.iter().enumerate() {
            loop_headers[candidate.header.index()] = true;
            for block in candidate.body_scope_blocks.iter().copied() {
                loops_by_body_block[block.index()].push(candidate_id);
            }

            let mut add_endpoint = |block: BlockRef| {
                if seen[block.index()] != candidate_id {
                    seen[block.index()] = candidate_id;
                    loops_by_endpoint[block.index()].push(candidate_id);
                }
            };
            for block in candidate
                .body_scope_blocks
                .iter()
                .chain(&candidate.blocks)
                .chain(&candidate.control_blocks)
                .copied()
            {
                add_endpoint(block);
            }
            if let Some(target) = candidate.continue_target {
                add_endpoint(target);
            }
            for edge in &candidate.backedges {
                add_endpoint(cfg.edges[edge.index()].from);
            }
        }

        let local_frontiers = graph_facts
            .dominance_frontier
            .iter()
            .map(|frontier| {
                frontier
                    .iter()
                    .copied()
                    .filter(|block| *block != cfg.exit_block && !loop_headers[block.index()])
                    .fold(FrontierShape::Empty, FrontierShape::push)
            })
            .collect();

        Self {
            graph_facts,
            loop_candidates,
            loops_by_endpoint,
            loops_by_body_block,
            loop_headers,
            local_frontiers,
            exit_block: cfg.exit_block,
        }
    }

    fn endpoint_loops(&self, block: BlockRef) -> impl Iterator<Item = &'a LoopCandidate> + '_ {
        self.loops_by_endpoint[block.index()]
            .iter()
            .map(|candidate| &self.loop_candidates[*candidate])
    }

    fn body_loops(&self, block: BlockRef) -> impl Iterator<Item = &'a LoopCandidate> + '_ {
        self.loops_by_body_block[block.index()]
            .iter()
            .map(|candidate| &self.loop_candidates[*candidate])
    }

    fn joins_at(&self, from: BlockRef, target: BlockRef) -> bool {
        self.graph_facts
            .dominance_frontier
            .get(from.index())
            .is_some_and(|frontier| frontier.contains(&target))
    }

    fn has_single_local_join(&self, from: BlockRef, target: BlockRef) -> bool {
        if target == self.exit_block || !self.joins_at(from, target) {
            return false;
        }
        match self.local_frontiers[from.index()] {
            FrontierShape::Empty => self.loop_headers[target.index()],
            FrontierShape::One(join) => join == target,
            FrontierShape::Multiple => false,
        }
    }
}

fn one_arm_candidate(
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    then_reaches_else: bool,
    else_reaches_then: bool,
) -> Option<BranchCandidate> {
    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        _ => None,
    }
}

fn classify_postdom_one_arm_branch(
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let then_reaches_else = graph_facts.post_dominates(else_entry, then_entry);
    let else_reaches_then = graph_facts.post_dominates(then_entry, else_entry);

    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}

fn classify_reachable_one_arm_branch(
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    // 唯一非 exit dominance-frontier 已经证明该臂真实汇入 continuation；再做一遍
    // 任意 CFG reachability 只会为每个 terminal branch 重扫全图。
    let then_reaches_else = branch_index.has_single_local_join(then_entry, else_entry);
    let else_reaches_then = branch_index.has_single_local_join(else_entry, then_entry);
    one_arm_candidate(
        header,
        then_entry,
        else_entry,
        then_reaches_else,
        else_reaches_then,
    )
}

fn refine_terminal_one_arm_branches(
    cfg: &Cfg,
    branch_index: &BranchIndex<'_>,
    irreducible_blocks: &[bool],
    candidates: &mut [BranchCandidate],
) {
    for candidate in candidates {
        if candidate.kind != BranchKind::IfElse
            || candidate.merge.is_some()
            || irreducible_blocks[candidate.header.index()]
        {
            continue;
        }
        let Some((truthy, falsy)) = cfg.branch_edges(candidate.header) else {
            continue;
        };
        let then_entry = cfg.edges[truthy.index()].to;
        let else_entry = cfg.edges[falsy.index()].to;
        if let Some(refined) = classify_reachable_one_arm_branch(
            branch_index,
            candidate.header,
            then_entry,
            else_entry,
        ) {
            *candidate = refined;
        }
    }
}

fn classify_infinite_loop_bounded_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let loop_candidate = branch_index
        .endpoint_loops(header)
        .filter(|candidate| {
            candidate.exits.is_empty()
                && candidate.blocks.contains(&header)
                && candidate.blocks.contains(&then_entry)
                && candidate.blocks.contains(&else_entry)
        })
        .min_by_key(|candidate| candidate.blocks.len())?;

    let reaches_local_tail = |from, to| {
        graph_facts.post_dominates(to, from)
            || branch_index.has_single_local_join(from, to)
                && !branch_index.joins_at(from, loop_candidate.header)
    };
    let then_reaches_else = reaches_local_tail(then_entry, else_entry);
    let else_reaches_then = reaches_local_tail(else_entry, then_entry);
    let local_merge = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry)
        .filter(|merge| *merge != header && *merge != loop_candidate.header)
        .filter(|merge| loop_candidate.blocks.contains(merge));

    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        (false, false) if local_merge.is_some() => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: local_merge,
            kind: BranchKind::IfElse,
            invert_hint: false,
        }),
        (false, false)
            if branch_index.joins_at(then_entry, loop_candidate.header)
                && branch_index.joins_at(else_entry, loop_candidate.header) =>
        {
            // 无出口循环没有严格后支配点，但两臂都在本轮结束后回到同一 header，
            // 该 header 就是源码层 if/else 的循环内合流边界。
            Some(BranchCandidate {
                header,
                then_entry,
                else_entry: Some(else_entry),
                merge: Some(loop_candidate.header),
                kind: BranchKind::IfElse,
                invert_hint: false,
            })
        }
        _ => None,
    }
}

fn classify_loop_exit_bounded_one_arm_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    // 局部 break 会把严格后支配点推到外层 loop exit；但若一臂进入单跳回边 pad，
    // 它表达的是下一轮 continue，不能把 loop-header frontier 当成普通 continuation。
    let enters_continue_pad = branch_index.endpoint_loops(header).any(|candidate| {
        candidate.blocks.contains(&header)
            && [then_entry, else_entry].into_iter().any(|entry| {
                transparent_jump_target(cfg, entry).is_some()
                    && candidate
                        .backedges
                        .iter()
                        .any(|edge| cfg.edges[edge.index()].from == entry)
            })
    });
    let owner = branch_index.endpoint_loops(header).find(|candidate| {
        candidate.blocks.contains(&header)
            && [then_entry, else_entry].into_iter().all(|entry| {
                candidate.body_scope_blocks.contains(&entry)
                    || candidate.blocks.contains(&entry)
                    || candidate.exits.contains(&entry)
            })
            && (loop_exits_at(cfg, candidate, strict_merge) || strict_merge == cfg.exit_block)
    })?;
    let then_continues =
        then_entry == owner.header || branch_index.joins_at(then_entry, owner.header);
    let else_continues =
        else_entry == owner.header || branch_index.joins_at(else_entry, owner.header);
    match (then_continues, else_continues) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::Guard,
            invert_hint: true,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::Guard,
            invert_hint: false,
        }),
        _ if enters_continue_pad => None,
        _ => classify_loop_bounded_one_arm_branch(branch_index, header, then_entry, else_entry),
    }
}

fn classify_for_loop_exit_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let strict_merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    let owner = find_for_loop_exit_owner(
        cfg,
        branch_index.endpoint_loops(header),
        header,
        then_entry,
        else_entry,
        strict_merge,
    )?;

    let body_entry = for_loop_body_entry(cfg, owner)?;
    match (
        cfg.unique_reachable_successor(then_entry) == Some(strict_merge),
        cfg.unique_reachable_successor(else_entry) == Some(strict_merge),
    ) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::Guard,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::Guard,
            invert_hint: true,
        }),
        _ if body_entry == header
            && owner.blocks.contains(&then_entry)
            && owner.blocks.contains(&else_entry) =>
        {
            let merge = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry)?;
            owner
                .body_scope_blocks
                .contains(&merge)
                .then_some(BranchCandidate {
                    header,
                    then_entry,
                    else_entry: Some(else_entry),
                    merge: Some(merge),
                    kind: BranchKind::IfElse,
                    invert_hint: false,
                })
        }
        _ => None,
    }
}

pub(super) fn for_loop_exit_owner<'a>(
    cfg: &Cfg,
    loop_candidates: &'a [LoopCandidate],
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    boundary: BlockRef,
) -> Option<&'a LoopCandidate> {
    find_for_loop_exit_owner(
        cfg,
        loop_candidates.iter(),
        header,
        then_entry,
        else_entry,
        boundary,
    )
}

fn find_for_loop_exit_owner<'a>(
    cfg: &Cfg,
    loop_candidates: impl Iterator<Item = &'a LoopCandidate>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
    boundary: BlockRef,
) -> Option<&'a LoopCandidate> {
    loop_candidates
        .filter(|candidate| {
            matches!(
                candidate.kind_hint,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            ) && candidate.body_scope_blocks.contains(&header)
                && candidate.body_scope_blocks.contains(&then_entry)
                && candidate.body_scope_blocks.contains(&else_entry)
                && loop_exits_at(cfg, candidate, boundary)
        })
        .min_by_key(|candidate| candidate.body_scope_blocks.len())
}

fn loop_exits_at(cfg: &Cfg, candidate: &LoopCandidate, boundary: BlockRef) -> bool {
    candidate.exits.contains(&boundary)
        || (!candidate.exits.is_empty()
            && candidate
                .exits
                .iter()
                .all(|exit| cfg.unique_reachable_successor(*exit) == Some(boundary)))
}

pub(super) fn for_loop_body_entry(cfg: &Cfg, candidate: &LoopCandidate) -> Option<BlockRef> {
    match candidate.kind_hint {
        LoopKindHint::NumericForLike => Some(candidate.header),
        LoopKindHint::GenericForLike => {
            let mut entries = cfg.succs[candidate.header.index()]
                .iter()
                .map(|edge| cfg.edges[edge.index()].to)
                .filter(|target| candidate.blocks.contains(target));
            let entry = entries.next()?;
            entries.next().is_none().then_some(entry)
        }
        LoopKindHint::Unknown
        | LoopKindHint::WhileLike
        | LoopKindHint::WhileTrueLike
        | LoopKindHint::RepeatLike => None,
    }
}

fn classify_loop_bounded_one_arm_branch(
    branch_index: &BranchIndex<'_>,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    // dominance frontier 只接受当前 arm 真正贡献前驱的 join，不会沿回边绕一整圈后
    // 把另一条 arm 误当 continuation；nested loop header 也已在稠密索引中单独标记。
    let then_reaches_else = branch_index.joins_at(then_entry, else_entry);
    let else_reaches_then = branch_index.joins_at(else_entry, then_entry);

    match (then_reaches_else, else_reaches_then) {
        (true, false) => Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        }),
        (false, true) => Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        }),
        _ => None,
    }
}

fn classify_if_else_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    if merge == cfg.exit_block {
        // 严格后支配合流是 exit block，说明两侧都有提前 return 的路径。
        // 若两臂仍有唯一共同 dominance frontier，它就是正常路径的 soft merge；
        // 提前 return 只作为 arm exit，不改变外层的词法 continuation。
        let soft = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry);
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: soft,
            kind: BranchKind::IfElse,
            invert_hint: false,
        });
    }

    if merge == then_entry {
        return Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        });
    }

    if merge == else_entry {
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        });
    }

    Some(BranchCandidate {
        header,
        then_entry,
        else_entry: Some(else_entry),
        merge: Some(merge),
        kind: BranchKind::IfElse,
        invert_hint: false,
    })
}

pub(super) fn transparent_jump_target(cfg: &Cfg, block: BlockRef) -> Option<BlockRef> {
    let [edge_ref] = cfg.succs[block.index()].as_slice() else {
        return None;
    };
    let edge = cfg.edges[edge_ref.index()];
    (cfg.blocks[block.index()].instrs.len == 1 && edge.kind == EdgeKind::Jump).then_some(edge.to)
}

fn classify_guard_branch(
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> BranchCandidate {
    // 前面的 postdom、loop-boundary 与 soft-merge 规则都无法证明 continuation 时，
    // 不再用“哪一臂可达块更多”猜 guard。保留无 merge 的双臂 owner，后续 plan 会
    // 分别声明两侧出口；这既不丢控制边，也避免每个 branch 做一次全图 DFS。
    BranchCandidate {
        header,
        then_entry,
        else_entry: Some(else_entry),
        merge: None,
        kind: BranchKind::IfElse,
        invert_hint: false,
    }
}

/// 当严格后支配合流 = exit block 时，从两臂共同的 dominance frontier 中找一个
/// "软合流"。它必须是两臂控制流真实汇入的 join，而不是只在全图上绕路可达。
///
/// 典型触发形状：
/// ```text
/// if A then        ← header
///     if B then return end   ← then 侧提前 return，导致 postdom(then)=exit
///     C
/// else
///     D
/// end
/// E                ← 软合流 = 两臂共同的 dominance frontier
/// ```
pub(super) fn find_soft_merge(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BlockRef> {
    let else_frontier = graph_facts.dominance_frontier.get(else_entry.index())?;
    let is_common = |candidate: &BlockRef| {
        *candidate != cfg.exit_block
            && graph_facts.dominates(header, *candidate)
            && else_frontier.contains(candidate)
    };
    let nearest = graph_facts
        .dominance_frontier_blocks(then_entry)
        .filter(is_common)
        .min_by_key(|candidate| {
            graph_facts.dominator_tree.depth[candidate.index()].unwrap_or(usize::MAX)
        })?;
    graph_facts
        .dominance_frontier_blocks(then_entry)
        .filter(is_common)
        .all(|candidate| graph_facts.dominates(nearest, candidate))
        .then_some(nearest)
}
