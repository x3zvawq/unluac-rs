//! 条件 continue 与循环 escape 的结构改写。输入复合 condition、loop partitions 和方言能力，输出明确的 continue/break arm domains 与 forward routes；不负责最终 edge 分类。例如无原生 continue 的目标会把 guard 改写为包住 body tail 的 branch。

use super::*;

/// 先把复合 condition 的语义出口固化到 branch，再按目标能力规划 continue。
///
/// raw BranchCandidate 的 local join 可能落在 condition DAG 内部，不能拿它决定共享尾。
/// 原生 continue 目标保留已证明的 transfer；其余目标才把 Guard 改写为包住 tail 的
/// 单臂 branch。
pub(super) struct LoopRewriteIndex {
    /// 普通可规约 block 只保存最内层候选，祖先通过 `parent` 链按需查询。
    innermost_by_block: Vec<Option<usize>>,
    /// 非树形/交叠候选保留精确 owner 列表；这是安全退化路径，不参与普通嵌套成本。
    fallback_by_block: Vec<Option<Box<[usize]>>>,
    parent: Vec<Option<usize>>,
    preorder: Vec<usize>,
    subtree_end: Vec<usize>,
    loops_by_header: Vec<Vec<usize>>,
}

struct ContainingLoops<'a> {
    next: Option<usize>,
    parent: &'a [Option<usize>],
    fallback: Option<std::slice::Iter<'a, usize>>,
}

impl Iterator for ContainingLoops<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(fallback) = self.fallback.as_mut() {
            return fallback.next().copied();
        }
        let current = self.next?;
        self.next = self.parent.get(current).copied().flatten();
        Some(current)
    }
}

impl LoopRewriteIndex {
    fn build(cfg: &Cfg, loops: &[super::super::LoopPlanInput]) -> Result<Self, StructureError> {
        let score = |index: usize| {
            (
                loops[index].candidate.body_scope_blocks.len(),
                loops[index].candidate.blocks.len(),
                index,
            )
        };
        let mut loop_header_by_block = vec![false; cfg.blocks.len()];
        for loop_ in loops {
            let Some(slot) = loop_header_by_block.get_mut(loop_.candidate.header.index()) else {
                return Err(StructureError::invalid(
                    "loop rewrite header is outside the CFG block arena",
                ));
            };
            *slot = true;
        }
        let mut owners_by_loop_header = vec![Vec::new(); cfg.blocks.len()];
        let mut innermost_by_block = vec![None; cfg.blocks.len()];
        let mut membership_count_by_block = vec![0usize; cfg.blocks.len()];
        let mut epoch_by_block = vec![0u32; cfg.blocks.len()];
        let mut epoch = 0u32;
        for (index, loop_) in loops.iter().enumerate() {
            epoch = epoch.wrapping_add(1);
            if epoch == 0 {
                epoch_by_block.fill(0);
                epoch = 1;
            }
            for block in loop_
                .candidate
                .blocks
                .iter()
                .chain(&loop_.candidate.body_scope_blocks)
            {
                let Some(seen) = epoch_by_block.get_mut(block.index()) else {
                    return Err(StructureError::invalid(
                        "loop rewrite index references a block outside the CFG arena",
                    ));
                };
                if *seen == epoch {
                    continue;
                }
                *seen = epoch;
                membership_count_by_block[block.index()] += 1;
                if loop_header_by_block[block.index()] {
                    owners_by_loop_header[block.index()].push(index);
                }
                let replace = innermost_by_block[block.index()]
                    .is_none_or(|current| score(index) < score(current));
                if replace {
                    innermost_by_block[block.index()] = Some(index);
                }
            }
        }

        let mut parent = vec![None; loops.len()];
        for (header, owners) in owners_by_loop_header.iter_mut().enumerate() {
            owners.sort_unstable_by_key(|index| score(*index));
            owners.dedup();
            if loop_header_by_block[header] && owners.is_empty() {
                return Err(StructureError::invalid(format!(
                    "loop rewrite header block #{header} has no owning loop"
                )));
            }
        }
        for (index, loop_) in loops.iter().enumerate() {
            let owners = owners_by_loop_header
                .get(loop_.candidate.header.index())
                .ok_or_else(|| {
                    StructureError::invalid("loop rewrite header is outside the CFG block arena")
                })?;
            let self_position = owners.binary_search_by_key(&score(index), |owner| score(*owner));
            let Ok(self_position) = self_position else {
                return Err(StructureError::invalid(format!(
                    "loop rewrite node #{index} is absent from its header owner index"
                )));
            };
            parent[index] = owners.get(self_position + 1).copied();
        }
        let mut children = vec![Vec::new(); loops.len()];
        for (index, parent) in parent.iter().copied().enumerate() {
            if let Some(parent) = parent {
                children[parent].push(index);
            }
        }
        for children in &mut children {
            children.sort_unstable_by_key(|index| score(*index));
        }

        let mut preorder = vec![usize::MAX; loops.len()];
        let mut subtree_end = vec![usize::MAX; loops.len()];
        let mut depth = vec![0usize; loops.len()];
        let mut order = Vec::with_capacity(loops.len());
        let mut pending = parent
            .iter()
            .enumerate()
            .filter_map(|(index, parent)| parent.is_none().then_some(index))
            .rev()
            .map(|root| (root, false))
            .collect::<Vec<_>>();
        while let Some((node, leaving)) = pending.pop() {
            if leaving {
                subtree_end[node] = order.len();
                continue;
            }
            if preorder[node] != usize::MAX {
                return Err(StructureError::invalid(
                    "loop rewrite containment contains a cycle",
                ));
            }
            preorder[node] = order.len();
            order.push(node);
            pending.push((node, true));
            for child in children[node].iter().rev().copied() {
                depth[child] = depth[node] + 1;
                pending.push((child, false));
            }
        }
        if let Some(index) = preorder.iter().position(|preorder| *preorder == usize::MAX) {
            return Err(StructureError::invalid(format!(
                "loop rewrite node #{index} is disconnected from its containment forest"
            )));
        }

        // containing_by_block 的旧排序是 score（最内层优先），而 parent chain 只在
        // 每条边也保持该顺序时才等价。若语义候选出现反常 score，后面的 owner 会走
        // 显式 fallback，避免改变 continue/break 重写的候选优先级。
        let chain_order_is_score_order = parent
            .iter()
            .enumerate()
            .all(|(child, parent)| parent.is_none_or(|parent| score(child) < score(parent)));
        let mut fallback_blocks = vec![false; cfg.blocks.len()];
        for (block_index, owner) in innermost_by_block.iter().copied().enumerate() {
            let Some(owner) = owner else {
                continue;
            };
            let expected = depth[owner] + 1;
            if !chain_order_is_score_order || membership_count_by_block[block_index] != expected {
                fallback_blocks[block_index] = true;
            }
        }

        // 每个 candidate 的 domain 只再扫一遍，用 Euler 区间验证其 owner 是否真的是
        // selected innermost 的祖先。非 ancestor 表示交叠候选，转入精确 fallback；
        // 普通嵌套路径不会保存 block×ancestor 列表。
        for (index, loop_) in loops.iter().enumerate() {
            epoch = epoch.wrapping_add(1);
            if epoch == 0 {
                epoch_by_block.fill(0);
                epoch = 1;
            }
            for block in loop_
                .candidate
                .blocks
                .iter()
                .chain(&loop_.candidate.body_scope_blocks)
            {
                let Some(seen) = epoch_by_block.get_mut(block.index()) else {
                    return Err(StructureError::invalid(
                        "loop rewrite index references a block outside the CFG arena",
                    ));
                };
                if *seen == epoch {
                    continue;
                }
                *seen = epoch;
                let Some(selected) = innermost_by_block[block.index()] else {
                    continue;
                };
                if !is_ancestor_in_intervals(&preorder, &subtree_end, index, selected) {
                    fallback_blocks[block.index()] = true;
                }
            }
        }

        let mut fallback_by_block = vec![None; cfg.blocks.len()];
        for (index, loop_) in loops.iter().enumerate() {
            epoch = epoch.wrapping_add(1);
            if epoch == 0 {
                epoch_by_block.fill(0);
                epoch = 1;
            }
            for block in loop_
                .candidate
                .blocks
                .iter()
                .chain(&loop_.candidate.body_scope_blocks)
            {
                let Some(seen) = epoch_by_block.get_mut(block.index()) else {
                    return Err(StructureError::invalid(
                        "loop rewrite index references a block outside the CFG arena",
                    ));
                };
                if *seen == epoch {
                    continue;
                }
                *seen = epoch;
                if !fallback_blocks[block.index()] {
                    continue;
                }
                fallback_by_block[block.index()]
                    .get_or_insert_with(Vec::new)
                    .push(index);
            }
        }
        for owners in fallback_by_block.iter_mut().flatten() {
            owners.sort_unstable_by_key(|index| score(*index));
            owners.dedup();
        }

        let mut loops_by_header = vec![Vec::new(); cfg.blocks.len()];
        for (index, loop_) in loops.iter().enumerate() {
            loops_by_header[loop_.candidate.header.index()].push(index);
        }
        for entries in &mut loops_by_header {
            entries.sort_unstable_by_key(|index| score(*index));
        }
        Ok(Self {
            innermost_by_block,
            fallback_by_block: fallback_by_block
                .into_iter()
                .map(|owners| owners.map(Vec::into_boxed_slice))
                .collect(),
            parent,
            preorder,
            subtree_end,
            loops_by_header,
        })
    }

    fn containing(&self, block: BlockRef) -> ContainingLoops<'_> {
        let fallback = self
            .fallback_by_block
            .get(block.index())
            .and_then(Option::as_deref);
        ContainingLoops {
            next: fallback
                .is_none()
                .then(|| {
                    self.innermost_by_block
                        .get(block.index())
                        .copied()
                        .flatten()
                })
                .flatten(),
            parent: &self.parent,
            fallback: fallback.map(<[usize]>::iter),
        }
    }

    fn contains_loop(&self, ancestor: usize, descendant: usize) -> bool {
        is_ancestor_in_intervals(&self.preorder, &self.subtree_end, ancestor, descendant)
    }

    fn at_header(&self, block: BlockRef) -> &[usize] {
        self.loops_by_header
            .get(block.index())
            .map_or(&[], Vec::as_slice)
    }
}

fn is_ancestor_in_intervals(
    preorder: &[usize],
    subtree_end: &[usize],
    ancestor: usize,
    descendant: usize,
) -> bool {
    let Some(start) = preorder.get(ancestor).copied() else {
        return false;
    };
    let Some(end) = subtree_end.get(ancestor).copied() else {
        return false;
    };
    preorder
        .get(descendant)
        .is_some_and(|descendant| start <= *descendant && *descendant < end)
}

pub(super) fn legalize_conditional_continues(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    caps: ControlFlowCaps,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let loop_index = LoopRewriteIndex::build(cfg, &input.loops)?;
    if caps.continue_stmt {
        normalize_condition_continue_arms(proto, cfg, graph_facts, &loop_index, input)?;
    }
    let break_rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(index, branch)| {
            let mut domain = loop_break_arm_domain(cfg, branch, &input.loops, &loop_index)?;
            domain.included_blocks.push(branch.branch.header);
            Some((index, domain))
        })
        .collect::<Vec<_>>();
    let mut has_loop_break_arm = vec![false; input.branches.len()];
    for (index, domain) in break_rewrites {
        has_loop_break_arm[index] = true;
        if let Some(region) = &mut input.branches[index].region {
            region.replace_domain(domain);
        }
    }

    let rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(index, branch)| {
            // 同一物理出口可能先 break 内层 loop，再自然进入祖先 loop 的下一轮。
            // 此时内层词法 owner 必须优先，不能再把它翻成祖先 loop 的 continue guard。
            if has_loop_break_arm[index] || branch.branch.kind != BranchKind::Guard {
                return None;
            }
            let lexical_tail = branch.branch.merge?;
            let escape = branch.branch.then_entry;
            let conditional_loop =
                conditional_continue_loop(proto, cfg, branch, &input.loops, &loop_index);
            let body_tail_loop =
                body_tail_guard_loop(proto, cfg, branch, &input.loops, &loop_index);
            if caps.continue_stmt && conditional_loop.is_some() && body_tail_loop.is_none() {
                return None;
            }
            body_tail_loop.or(conditional_loop)?;
            let tail = lexical_tail;
            Some((index, tail, escape, branch.branch.header))
        })
        .collect::<Vec<_>>();
    for (index, tail, escape, header) in rewrites {
        rewrite_one_arm_branch(graph_facts, &mut input.branches[index], tail, escape);
        if let Some(region) = &mut input.branches[index].region {
            region.replace_domain(BranchRegionDomain {
                spans: Vec::new(),
                included_blocks: vec![header, tail],
            });
        }
    }

    if caps.continue_stmt {
        let rewrites = input
            .branches
            .iter()
            .enumerate()
            .filter_map(|(index, branch)| {
                let mut domain =
                    native_continue_arm_domain(proto, cfg, branch, &input.loops, &loop_index)?;
                domain.included_blocks.push(branch.branch.header);
                Some((index, domain))
            })
            .collect::<Vec<_>>();
        for (index, domain) in rewrites {
            if let Some(region) = &mut input.branches[index].region {
                // continue pad 可以同时承接正常 loop tail，因此不是 branch arm 的
                // containment child；该 edge 已由最终 Continue transfer 唯一表示。
                region.replace_domain(domain);
            }
        }
        return Ok(());
    }
    Ok(())
}

pub(super) fn normalize_condition_continue_arms(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_index: &LoopRewriteIndex,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    struct Rewrite {
        branch: usize,
        loop_: usize,
        continue_entry: BlockRef,
        normal_entry: BlockRef,
        domain: BranchRegionDomain,
        transfers: BTreeSet<EdgeRef>,
    }

    let rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(branch_index, branch)| {
            let condition = branch
                .condition
                .and_then(|condition| input.conditions.get(condition.index()))?;
            // 只修复 raw local-join 被短路折叠吸进 condition DAG 的候选。边界本来
            // 已落在 condition 外的 branch 由既有 continue evidence 处理，不能重选。
            if !branch
                .branch
                .merge
                .is_some_and(|merge| condition.candidate.blocks.contains(&merge))
            {
                return None;
            }
            let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
                return None;
            };
            [(truthy, falsy), (falsy, truthy)]
                .into_iter()
                .enumerate()
                .filter_map(|(orientation, (continue_entry, normal_entry))| {
                    condition_continue_rewrite_for_orientation(
                        proto,
                        cfg,
                        graph_facts,
                        input,
                        loop_index,
                        branch,
                        condition,
                        continue_entry,
                        normal_entry,
                    )
                    .map(|(loop_owner, arm, transfers)| {
                        (
                            (
                                input.loops[loop_owner].candidate.body_scope_blocks.len(),
                                input.loops[loop_owner].candidate.blocks.len(),
                                orientation,
                            ),
                            Rewrite {
                                branch: branch_index,
                                loop_: loop_owner,
                                continue_entry,
                                normal_entry,
                                domain: {
                                    let mut domain = arm;
                                    domain.included_blocks.push(branch.branch.header);
                                    domain
                                },
                                transfers,
                            },
                        )
                    })
                })
                .min_by_key(|(score, _)| *score)
                .map(|(_, rewrite)| rewrite)
        })
        .collect::<Vec<_>>();

    let mut semantic_edges = BTreeSet::new();
    for rewrite in rewrites {
        rewrite_one_arm_branch(
            graph_facts,
            &mut input.branches[rewrite.branch],
            rewrite.continue_entry,
            rewrite.normal_entry,
        );
        if let Some(region) = &mut input.branches[rewrite.branch].region {
            region.replace_domain(rewrite.domain);
        }
        input.loops[rewrite.loop_]
            .candidate
            .continue_edges
            .extend(rewrite.transfers.iter().copied());
        input.loops[rewrite.loop_]
            .semantic_continue_edges
            .extend(rewrite.transfers.iter().copied());
        semantic_edges.extend(rewrite.transfers);
    }
    input
        .residual_transfers
        .retain(|residual| !semantic_edges.contains(&residual.edge));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn condition_continue_rewrite_for_orientation(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    loop_index: &LoopRewriteIndex,
    branch: &super::super::BranchPlanInput,
    condition: &super::super::ConditionPlanInput,
    continue_entry: BlockRef,
    normal_entry: BlockRef,
) -> Option<(usize, BranchRegionDomain, BTreeSet<EdgeRef>)> {
    for owner in loop_index.containing(branch.branch.header) {
        let loop_ = &input.loops[owner];
        let candidate = &loop_.candidate;
        let contains_header = candidate.blocks.contains(&branch.branch.header)
            || candidate.body_scope_blocks.contains(&branch.branch.header);
        let contains_normal = candidate.blocks.contains(&normal_entry)
            || candidate.body_scope_blocks.contains(&normal_entry);
        if contains_header
            && contains_normal
            && candidate.backedges.len() > 1
            && !loop_iteration_escape_entry(proto, cfg, candidate, normal_entry)
            && let Some(arm) = collect_continue_arm_domain(
                proto,
                cfg,
                continue_entry,
                normal_entry,
                owner,
                &input.loops,
                loop_index,
            )
            && !arm.is_empty()
        {
            let transfers = semantic_continue_transfers(
                proto,
                cfg,
                graph_facts,
                condition,
                continue_entry,
                &arm,
                candidate,
            );
            if !transfers.is_empty() {
                return Some((owner, arm, transfers));
            }
        }
    }
    None
}

pub(super) fn semantic_continue_transfers(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    condition: &super::super::ConditionPlanInput,
    continue_entry: BlockRef,
    arm: &BranchRegionDomain,
    loop_: &crate::structure::LoopCandidate,
) -> BTreeSet<EdgeRef> {
    let mut transfers = loop_
        .backedges
        .iter()
        .copied()
        .filter(|edge| {
            let Some(edge_data) = cfg.edges.get(edge.index()) else {
                return false;
            };
            arm.contains(graph_facts, edge_data.from)
                && (loop_.continue_edges.contains(edge)
                    || loop_iteration_escape_entry(proto, cfg, loop_, edge_data.to))
        })
        .collect::<BTreeSet<_>>();
    if arm.is_empty() && loop_iteration_escape_entry(proto, cfg, loop_, continue_entry) {
        transfers.extend(condition.arcs.iter().filter_map(|arc| {
            arc.edges.last().copied().filter(|edge| {
                cfg.edges.get(edge.index()).map(|edge| edge.to) == Some(continue_entry)
            })
        }));
    }
    transfers
}

pub(super) fn loop_break_arm_domain(
    cfg: &Cfg,
    branch: &super::super::BranchPlanInput,
    loops: &[super::super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    if !matches!(branch.branch.kind, BranchKind::IfThen | BranchKind::Guard)
        || branch.branch.else_entry.is_some()
    {
        return None;
    }
    let merge = branch.branch.merge?;
    for owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        let candidate = &loop_.candidate;
        let eligible_header = !candidate.control_blocks.contains(&branch.branch.header)
            && candidate.condition_header != Some(branch.branch.header)
            && (candidate.blocks.contains(&branch.branch.header)
                || candidate.body_scope_blocks.contains(&branch.branch.header));
        if eligible_header
            && let Some(continuation) = loop_.continuation
            && continuation != cfg.exit_block
            && continuation != merge
            && (candidate.exits.contains(&continuation)
                || candidate.exits.contains(&branch.branch.then_entry))
            && (candidate.blocks.contains(&merge) || candidate.body_scope_blocks.contains(&merge))
            && let Some(span) = collect_linear_escape_span(
                cfg,
                branch.branch.then_entry,
                merge,
                continuation,
                candidate,
            )
        {
            return Some(BranchRegionDomain {
                spans: vec![span],
                included_blocks: Vec::new(),
            });
        }
    }
    None
}

pub(super) fn collect_linear_escape_span(
    cfg: &Cfg,
    start: BlockRef,
    merge: BlockRef,
    target: BlockRef,
    owner: &crate::structure::LoopCandidate,
) -> Option<BranchRegionSpan> {
    let mut current = start;
    let mut visited = BTreeSet::new();
    while current != target {
        if current == merge
            || !visited.insert(current)
            || !owner.blocks.contains(&current) && !owner.body_scope_blocks.contains(&current)
            || current != start
                && cfg.preds[current.index()]
                    .iter()
                    .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                    .take(2)
                    .count()
                    > 1
        {
            return None;
        }
        let [edge] = cfg.succs.get(current.index())?.as_slice() else {
            return None;
        };
        current = cfg.edges.get(edge.index())?.to;
    }
    Some(BranchRegionSpan {
        root: start,
        excluded_subtrees: vec![target],
    })
}

pub(super) fn conditional_continue_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::super::BranchPlanInput,
    loops: &[super::super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<usize> {
    (branch.branch.kind == BranchKind::Guard).then_some(())?;
    for owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if loop_.candidate.blocks.contains(&branch.branch.header)
            && loop_iteration_escape_entry(proto, cfg, &loop_.candidate, branch.branch.then_entry)
        {
            return Some(owner);
        }
    }
    None
}

pub(super) fn body_tail_guard_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::super::BranchPlanInput,
    loops: &[super::super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<usize> {
    (branch.branch.kind == BranchKind::Guard).then_some(())?;
    let tail = branch.branch.merge?;
    let [tail_edge] = cfg.succs[tail.index()].as_slice() else {
        return None;
    };
    (cfg.edges[tail_edge.index()].to == branch.branch.then_entry).then_some(())?;
    for owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if (loop_.candidate.blocks.contains(&branch.branch.header)
            || loop_
                .candidate
                .body_scope_blocks
                .contains(&branch.branch.header))
            && loop_.candidate.continue_target == Some(branch.branch.then_entry)
            && block_has_non_control_prefix(proto, cfg, branch.branch.then_entry)
        {
            return Some(owner);
        }
    }
    None
}

pub(super) fn native_continue_arm_domain(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::super::BranchPlanInput,
    loops: &[super::super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    if !matches!(branch.branch.kind, BranchKind::IfThen | BranchKind::Guard)
        || branch.branch.else_entry.is_some()
    {
        return None;
    }
    let merge = branch.branch.merge?;
    for owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if (loop_.candidate.blocks.contains(&branch.branch.header)
            || loop_
                .candidate
                .body_scope_blocks
                .contains(&branch.branch.header))
            && !loop_iteration_escape_entry(proto, cfg, &loop_.candidate, merge)
            && let Some(domain) = collect_continue_arm_domain(
                proto,
                cfg,
                branch.branch.then_entry,
                merge,
                owner,
                loops,
                loop_index,
            )
        {
            return Some(domain);
        }
    }
    None
}

pub(super) fn collect_continue_arm_domain(
    proto: &LoweredProto,
    cfg: &Cfg,
    start: BlockRef,
    merge: BlockRef,
    owner_index: usize,
    loops: &[super::super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    let owner = loops.get(owner_index)?;
    let mut current = start;
    let mut visited = BTreeSet::new();
    loop {
        if current == merge || !visited.insert(current) {
            return None;
        }
        if loop_iteration_escape_entry(proto, cfg, &owner.candidate, current) {
            return Some(if current != start {
                BranchRegionDomain::from_span(start, [current])
            } else {
                BranchRegionDomain {
                    spans: Vec::new(),
                    included_blocks: Vec::new(),
                }
            });
        }
        if !owner.candidate.blocks.contains(&current)
            && !owner.candidate.body_scope_blocks.contains(&current)
        {
            return None;
        }
        if current != start
            && cfg.preds[current.index()]
                .iter()
                .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                .take(2)
                .count()
                > 1
        {
            return None;
        }

        if let Some((nested, continuation)) = loop_index
            .at_header(current)
            .iter()
            .copied()
            .filter(|nested| {
                *nested != owner_index && loop_index.contains_loop(owner_index, *nested)
            })
            .filter_map(|nested| Some((nested, loops[nested].continuation?)))
            .find(|(_, continuation)| {
                loop_iteration_escape_entry(proto, cfg, &owner.candidate, *continuation)
            })
        {
            let nested = &loops[nested];
            let mut spans = Vec::new();
            if current != start {
                spans.push(BranchRegionSpan {
                    root: start,
                    excluded_subtrees: vec![current],
                });
            }
            let mut excluded_subtrees = nested.candidate.exits.iter().copied().collect::<Vec<_>>();
            excluded_subtrees.push(continuation);
            excluded_subtrees.push(cfg.exit_block);
            excluded_subtrees.sort_unstable();
            excluded_subtrees.dedup();
            spans.push(BranchRegionSpan {
                root: current,
                excluded_subtrees,
            });
            return Some(BranchRegionDomain {
                spans,
                included_blocks: Vec::new(),
            });
        }

        let [edge] = cfg.succs.get(current.index())?.as_slice() else {
            return None;
        };
        let target = cfg.edges.get(edge.index())?.to;
        if owner.candidate.continue_edges.contains(edge)
            || loop_iteration_escape_entry(proto, cfg, &owner.candidate, target)
        {
            return Some(BranchRegionDomain::from_span(start, [target]));
        }
        current = target;
    }
}

pub(super) fn loop_iteration_escape_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    entry: BlockRef,
) -> bool {
    let direct_continue = candidate.continue_target == Some(entry)
        && !(matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::Unknown
                | crate::structure::LoopKindHint::RepeatLike
                | crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::WhileTrueLike
        ) && block_has_non_control_prefix(proto, cfg, entry)
            && !control_prefix_is_movable(proto, cfg, entry));
    direct_continue
        || candidate.backedges.iter().any(|edge_ref| {
            cfg.edges.get(edge_ref.index()).is_some_and(|edge| {
                edge.from == entry
                    && edge.to == candidate.header
                    && cfg.blocks[entry.index()].instrs.len == 1
                    && cfg.succs[entry.index()].as_slice() == [*edge_ref]
            })
        })
}

pub(super) struct PureContinueForwardIndex {
    distance: Vec<Option<usize>>,
    last: Vec<Option<EdgeRef>>,
}

impl PureContinueForwardIndex {
    pub(super) fn build(
        cfg: &Cfg,
        arena: &RegionArena,
        partition: &LoopPartitions,
        target: BlockRef,
        barriers: &BTreeSet<BlockRef>,
        labels: &BTreeSet<BlockRef>,
    ) -> Result<Self, StructureError> {
        Self::build_filtered(cfg, target, |source, incoming| {
            if !partition.body.contains(&source)
                || barriers.contains(&source)
                || labels.contains(&source)
            {
                return false;
            }
            let Some(owner) = arena.region_by_block[source.index()] else {
                return false;
            };
            !arena.navigation.has_unstructured_ancestor(owner)
                && cfg.blocks[source.index()].instrs.len == 1
                && cfg.succs[source.index()].as_slice() == [incoming]
                && cfg.edges[incoming.index()].kind == EdgeKind::Jump
        })
    }

    pub(super) fn build_cfg(
        cfg: &Cfg,
        body: &BTreeSet<BlockRef>,
        target: BlockRef,
        barriers: &BTreeSet<BlockRef>,
        labels: &BTreeSet<BlockRef>,
    ) -> Result<Self, StructureError> {
        Self::build_filtered(cfg, target, |source, incoming| {
            body.contains(&source)
                && !barriers.contains(&source)
                && !labels.contains(&source)
                && cfg.blocks[source.index()].instrs.len == 1
                && cfg.succs[source.index()].as_slice() == [incoming]
                && cfg.edges[incoming.index()].kind == EdgeKind::Jump
        })
    }

    fn build_filtered(
        cfg: &Cfg,
        target: BlockRef,
        mut accepts: impl FnMut(BlockRef, EdgeRef) -> bool,
    ) -> Result<Self, StructureError> {
        let mut distance: Vec<Option<usize>> = vec![None; cfg.blocks.len()];
        let mut last = vec![None; cfg.blocks.len()];
        distance[target.index()] = Some(0);
        let mut pending = VecDeque::from([target]);
        while let Some(block) = pending.pop_front() {
            let suffix_len = distance[block.index()].ok_or_else(|| {
                StructureError::invalid("continue forward index lost a discovered block")
            })?;
            for &incoming in &cfg.preds[block.index()] {
                let source = cfg.edges[incoming.index()].from;
                if distance[source.index()].is_some() || !accepts(source, incoming) {
                    continue;
                }
                distance[source.index()] = Some(
                    suffix_len
                        .checked_add(1)
                        .ok_or_else(|| StructureError::invalid("forward route length overflow"))?,
                );
                last[source.index()] = if suffix_len == 0 {
                    Some(incoming)
                } else {
                    last[block.index()]
                };
                pending.push_back(source);
            }
        }
        Ok(Self { distance, last })
    }

    pub(super) fn route(&self, cfg: &Cfg, entry: EdgeRef) -> Option<FunctionalForwardPath> {
        let start = cfg.edges.get(entry.index())?.to;
        let len = self.distance.get(start.index()).copied().flatten()?;
        if len == 0 {
            return None;
        }
        let [first] = cfg.succs.get(start.index())?.as_slice() else {
            return None;
        };
        Some(FunctionalForwardPath {
            first: *first,
            last: self.last.get(start.index()).copied().flatten()?,
            len,
        })
    }
}

pub(super) fn repeat_continue_forwarding_route(
    cfg: &Cfg,
    arena: &RegionArena,
    partition: &LoopPartitions,
    candidate: &crate::structure::LoopCandidate,
    condition: BlockRef,
    barriers: &BTreeSet<BlockRef>,
    labels: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut loop_edges = cfg.succs[condition.index()]
        .iter()
        .copied()
        .filter(|edge| partition.owned.contains(&cfg.edges[edge.index()].to));
    let loop_edge = loop_edges.next()?;
    if loop_edges.next().is_some() {
        return None;
    }
    let mut route = vec![loop_edge];
    let mut block = cfg.edges[loop_edge.index()].to;
    let mut visited = BTreeSet::new();
    while block != candidate.header {
        if !visited.insert(block)
            || !partition.owned.contains(&block)
            || barriers.contains(&block)
            || labels.contains(&block)
        {
            return None;
        }
        let owner = arena
            .region_by_block
            .get(block.index())
            .copied()
            .flatten()?;
        if arena.navigation.has_unstructured_ancestor(owner) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        let cfg_edge = cfg.edges.get(edge.index())?;
        if range.len != 1 || cfg_edge.kind != EdgeKind::Jump {
            return None;
        }
        route.push(*edge);
        block = cfg_edge.to;
    }
    Some(route)
}

pub(super) fn direct_continue_latch_route(
    cfg: &Cfg,
    arena: &RegionArena,
    partition: &LoopPartitions,
    header: BlockRef,
    target: BlockRef,
    barriers: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut block = target;
    let mut visited = BTreeSet::new();
    let mut route = Vec::new();
    while block != header {
        if !visited.insert(block) || !partition.body.contains(&block) || barriers.contains(&block) {
            return None;
        }
        let owner = arena
            .region_by_block
            .get(block.index())
            .copied()
            .flatten()?;
        if arena.navigation.has_unstructured_ancestor(owner) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        let cfg_edge = cfg.edges.get(edge.index())?;
        if range.len != 1 || cfg_edge.kind != EdgeKind::Jump {
            return None;
        }
        route.push(*edge);
        block = cfg_edge.to;
    }
    (!route.is_empty()).then_some(route)
}

pub(super) fn continue_edge_bypasses_body(
    cfg: &Cfg,
    partition: &LoopPartitions,
    edge: EdgeRef,
) -> bool {
    continue_edge_bypasses_body_parts(cfg, &partition.body, edge)
}

pub(super) fn body_blocks_reaching_target(
    cfg: &Cfg,
    body: &BTreeSet<BlockRef>,
    target: BlockRef,
) -> BTreeSet<BlockRef> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![target];
    while let Some(block) = pending.pop() {
        for edge in &cfg.preds[block.index()] {
            let source = cfg.edges[edge.index()].from;
            if body.contains(&source) && reachable.insert(source) {
                pending.push(source);
            }
        }
    }
    reachable
}

pub(super) fn continue_edge_bypasses_body_parts(
    cfg: &Cfg,
    body: &BTreeSet<BlockRef>,
    edge: EdgeRef,
) -> bool {
    let Some(selected) = cfg.edges.get(edge.index()) else {
        return false;
    };
    let Some(successors) = cfg.succs.get(selected.from.index()) else {
        return false;
    };
    if successors.len() == 2
        && successors.iter().copied().any(|other| {
            other != edge
                && cfg
                    .edges
                    .get(other.index())
                    .is_some_and(|other| other.to != selected.to && body.contains(&other.to))
        })
    {
        return true;
    }
    successors.as_slice() == [edge]
        && cfg.preds[selected.from.index()]
            .iter()
            .copied()
            .any(|incoming| {
                let predecessor = cfg.edges[incoming.index()].from;
                cfg.succs[predecessor.index()].len() == 2
                    && cfg.succs[predecessor.index()]
                        .iter()
                        .copied()
                        .any(|sibling| {
                            sibling != incoming
                                && cfg.edges.get(sibling.index()).is_some_and(|sibling| {
                                    sibling.to != selected.from && body.contains(&sibling.to)
                                })
                        })
            })
}
