//! 细化 single-pass fence、loop escape merge 与 iteration if/else。
//!
//! 本模块依赖已经分类的 branch/loop 候选和支配事实，只把真正跨分支共享的线性 tail
//! 冻结成 single-pass fence；它不负责基础分支分类，也不会把两臂各自闭合到同一出口的
//! 普通 `if/else` 改写成合成 `repeat`。例如，嵌套 break 跳过共享 tail 时建立 fence，
//! 而一臂执行普通语句、另一臂执行 numeric-for 后共同结束时继续保留 `if/else`。
//! fence 也不能包住指向祖先 loop 的 break/continue；Lua 的无标签控制会被合成 repeat
//! 截获，因此这类 pre-exit 域必须保留普通 branch。

use super::*;

/// 恢复被编译器消去回边的 `repeat ... until true`。
///
/// 这类区域有一个被多条正常路径共享的线性 tail，同时若干早退路径直接进入 tail
/// 之后的严格合流点。把外层 branch 的 continuation 收到 tail 后，最终 plan 就能用
/// 一个 single-pass containment owner 承载所有跳过 tail 的 `break`。
///
/// 如果 tail 完全属于 strict `if/else` 的一臂、其余出口完全属于另一臂，那么 tail
/// 并未被两臂共享；这只是普通分支的两条完成路径，必须保留原 branch continuation。
pub(super) fn refine_single_pass_fences(
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
            || closed_if_else_partitions_tail_and_escapes(
                cfg,
                graph_facts,
                &branch_candidates[candidate_index],
                tail,
                exit,
                &escape_edges,
            )
            || closed_if_else_owns_value_result(
                cfg,
                graph_facts,
                dataflow,
                &branch_candidates[candidate_index],
                (tail, tail_edge),
                exit,
                &escape_edges,
            )
            || loop_candidates.iter().any(|owner| {
                let is_before_exit = |block| {
                    graph_facts.dominates(owner.header, block)
                        && !graph_facts.dominates(exit, block)
                };
                owner.exits.contains(&exit)
                    && is_before_exit(header)
                    && is_before_exit(tail)
                    && escape_edges
                        .iter()
                        .all(|edge_ref| is_before_exit(cfg.edges[edge_ref.index()].from))
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

/// strict `if/else` 的线性 tail 若完全属于一臂，则返回另一臂入口。
///
/// 两臂都不支配 tail 时，它才可能是 single-pass 的共享 tail；两臂都支配则候选边界
/// 已经歧义。这个查询同时供纯控制分区和 value-result 闭合证明使用。
fn opposite_if_else_arm_for_owned_tail(
    graph_facts: &GraphFacts,
    candidate: &BranchCandidate,
    tail: BlockRef,
    exit: BlockRef,
) -> Option<BlockRef> {
    let else_entry = candidate.else_entry?;
    if candidate.kind != BranchKind::IfElse
        || candidate.merge != Some(exit)
        || graph_facts.nearest_common_postdom(candidate.then_entry, else_entry) != Some(exit)
    {
        return None;
    }

    match (
        graph_facts.dominates(candidate.then_entry, tail),
        graph_facts.dominates(else_entry, tail),
    ) {
        (true, false) => Some(else_entry),
        (false, true) => Some(candidate.then_entry),
        (true, true) | (false, false) => None,
    }
}

/// 拒绝把两臂各自完成到 strict exit 的普通 `if/else` 伪装成 single-pass fence。
fn closed_if_else_partitions_tail_and_escapes(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    candidate: &BranchCandidate,
    tail: BlockRef,
    exit: BlockRef,
    escape_edges: &BTreeSet<EdgeRef>,
) -> bool {
    if graph_facts.block_is_cyclic(candidate.header) || graph_facts.block_is_cyclic(tail) {
        return false;
    }
    let Some(opposite_arm) =
        opposite_if_else_arm_for_owned_tail(graph_facts, candidate, tail, exit)
    else {
        return false;
    };

    !escape_edges.is_empty()
        && escape_edges
            .iter()
            .all(|edge| graph_facts.dominates(opposite_arm, cfg.edges[edge.index()].from))
}

/// value-result 已经证明两臂在严格后支配点闭合时，shared-tail 只是其中一臂的
/// 实现形状；改成 single-pass 会把正常分支的结果边误解释成 `break`。
pub(super) fn closed_if_else_owns_value_result(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    candidate: &BranchCandidate,
    tail: (BlockRef, EdgeRef),
    exit: BlockRef,
    escape_edges: &BTreeSet<EdgeRef>,
) -> bool {
    let (tail, tail_edge) = tail;
    let Some(else_entry) = candidate.else_entry else {
        return false;
    };
    let Some(result_arm) = opposite_if_else_arm_for_owned_tail(graph_facts, candidate, tail, exit)
    else {
        return false;
    };

    // Dataflow 的 block range 是稠密索引；每个 exit 只检查自身 canonical/live phi，
    // 并要求当前两臂的物理边给同一个非平凡 phi 提供不同值。
    let direct_result = dataflow.phi_candidates_in_block(exit).iter().any(|phi| {
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
    });
    if direct_result {
        return true;
    }

    if graph_facts.block_is_cyclic(candidate.header) || graph_facts.block_is_cyclic(tail) {
        return false;
    }

    // 嵌套短路臂会让同一源码臂的多个 leaf 直接进入 strict exit，浅层
    // `result_arm` 因此不再支配每条 escape。此时仍只信任原始 IfElse 两臂的支配归属，
    // 再复用 branch-value 的 phi 闭合证明；任意歧义 predecessor 都保守拒绝。
    let mut then_preds = BTreeSet::new();
    let mut else_preds = BTreeSet::new();
    for edge in &cfg.preds[exit.index()] {
        let pred = cfg.edges[edge.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }
        match (
            graph_facts.dominates(candidate.then_entry, pred),
            graph_facts.dominates(else_entry, pred),
        ) {
            (true, false) => {
                then_preds.insert(pred);
            }
            (false, true) => {
                else_preds.insert(pred);
            }
            (true, true) | (false, false) => return false,
        }
    }
    !then_preds.is_empty()
        && !else_preds.is_empty()
        && then_preds.is_disjoint(&else_preds)
        && !branch_value_merges_in_block(
            &BranchValueMergeContext::new(cfg, candidate.header, graph_facts, dataflow),
            exit,
            &then_preds,
            &else_preds,
            None,
        )
        .is_empty()
}

pub(super) fn refine_enclosing_loop_escape_merges(
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
    let mut nested_by_escape = vec![Vec::new(); cfg.blocks.len()];
    for candidate in &snapshot {
        if matches!(candidate.kind, BranchKind::IfThen | BranchKind::Guard)
            && candidate.else_entry.is_none()
            && let Some(merge) = candidate.merge
        {
            nested_by_merge[merge.index()].push(candidate);
            // loop-break guard 的 merge 是正常入口而非 exit；同时索引显式 arm 边界，
            // 最终仍由具体 loop owner 的 branch_has_loop_escape_arm 做精确资格判定。
            nested_by_escape[candidate.then_entry.index()].push(candidate);
            if let Some(exit) = cfg.unique_reachable_successor(candidate.then_entry) {
                nested_by_escape[exit.index()].push(candidate);
            }
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
            .flat_map(|exit| {
                nested_by_merge[exit.index()]
                    .iter()
                    .chain(&nested_by_escape[exit.index()])
            })
            .chain(&nested_by_merge[soft_merge.index()])
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
pub(super) fn classify_loop_continue_guard(
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
pub(super) fn classify_loop_break_guard(
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

pub(super) fn loop_break_entry(cfg: &Cfg, candidate: &LoopCandidate, entry: BlockRef) -> bool {
    candidate.continue_target != Some(entry)
        && candidate.condition_header != Some(entry)
        && !candidate.control_blocks.contains(&entry)
        && (candidate.exits.contains(&entry)
            || matches!(cfg.succs[entry.index()].as_slice(), [edge]
                if candidate.exits.contains(&cfg.edges[edge.index()].to))
            || transparent_jump_target(cfg, entry)
                .is_some_and(|target| candidate.exits.contains(&target)))
}

pub(super) fn loop_candidate_owns_endpoint(
    cfg: &Cfg,
    candidate: &LoopCandidate,
    block: BlockRef,
) -> bool {
    candidate.body_scope_blocks.contains(&block)
        || candidate.blocks.contains(&block)
        || candidate.control_blocks.contains(&block)
        || candidate.continue_target == Some(block)
        || candidate
            .backedges
            .iter()
            .any(|edge| cfg.edges[edge.index()].from == block)
}

pub(super) fn branch_has_loop_escape_arm(
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

pub(super) fn loop_iteration_escape_entry(
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

pub(super) fn refine_loop_iteration_if_else_branches(
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
        if let Some((then_entry, merge, invert_hint)) = loop_escape_prefix_refinement(
            proto,
            cfg,
            branch_index,
            candidate,
            &candidates_by_header,
        ) {
            candidate.then_entry = then_entry;
            candidate.else_entry = None;
            candidate.merge = Some(merge);
            candidate.kind = BranchKind::IfThen;
            candidate.invert_hint = invert_hint;
            continue;
        }
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

/// 收回 `if A then if B then escape end end` 的外层 one-arm prefix。
/// 嵌套 guard 必须由 outer 唯一进入，且正常/escape 两端分别精确等于 outer 的
/// sibling/strict merge，避免把共享或跨 loop 的 guard 强压进当前分支。
pub(super) fn loop_escape_prefix_refinement(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch_index: &BranchIndex<'_>,
    outer: &BranchCandidate,
    candidates_by_header: &[Option<BranchCandidate>],
) -> Option<(BlockRef, BlockRef, bool)> {
    let (Some(strict_merge), Some(else_entry)) = (outer.merge, outer.else_entry) else {
        return None;
    };
    if outer.kind != BranchKind::IfElse {
        return None;
    }

    let refinement = |nested_entry: BlockRef, sibling: BlockRef, invert_hint: bool| {
        let nested = candidates_by_header
            .get(nested_entry.index())
            .and_then(Option::as_ref)?;
        (nested.kind == BranchKind::Guard
            && nested_entry != outer.header
            && nested.else_entry.is_none()
            && nested.merge == Some(sibling)
            && nested.then_entry == strict_merge
            && cfg.unique_reachable_predecessor_matching(nested_entry, |_| true)
                == Some(outer.header))
        .then_some(())?;
        let owner = branch_index
            .body_loops(outer.header)
            .filter(|owner| {
                owner.body_scope_blocks.contains(&nested_entry)
                    && owner.body_scope_blocks.contains(&sibling)
                    && loop_candidate_owns_endpoint(cfg, owner, strict_merge)
            })
            .min_by_key(|owner| owner.body_scope_blocks.len())?;
        branch_has_loop_escape_arm(proto, cfg, owner, nested).then_some((
            nested_entry,
            sibling,
            invert_hint,
        ))
    };
    match (
        refinement(outer.then_entry, else_entry, false),
        refinement(else_entry, outer.then_entry, true),
    ) {
        (Some(refinement), None) | (None, Some(refinement)) => Some(refinement),
        _ => None,
    }
}
