//! Region arena 的构建与物化。输入规范化 container/loop partitions，输出 containment tree、direct block owner 与导航索引；不负责冻结 edge transfer。例如 structured child 会先物化，再嵌入最小 residual island。

use super::*;

pub(super) fn build_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
) -> Result<RegionArena, StructureError> {
    let mut pending = Vec::new();
    let mut residuals = Vec::new();
    let mut unstructured_blocks = Vec::new();
    for (index, island) in input.unstructured.iter().enumerate() {
        let blocks = island.layout.as_ref().map_or_else(
            || island.fact.blocks.clone(),
            |layout| layout.blocks.clone(),
        );
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        if !blocks.is_empty() {
            unstructured_blocks.push(blocks.clone());
            pending.push(PendingContainer::exact(
                ContainerKind::Island(index),
                blocks,
                graph_facts,
            )?);
        }
    }
    let island_prefix = if unstructured_blocks.is_empty() {
        None
    } else {
        let mut island_by_preorder = vec![false; graph_facts.dominator_tree.order.len()];
        for block in unstructured_blocks.iter().flatten() {
            let position = graph_facts
                .dominator_tree
                .preorder_index
                .get(block.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "reachable island references block {block} outside dominator preorder"
                    ))
                })?;
            let slot = island_by_preorder.get_mut(position).ok_or_else(|| {
                StructureError::invalid("island block position exceeds dominator preorder")
            })?;
            *slot = true;
        }
        let mut prefix = Vec::with_capacity(island_by_preorder.len() + 1);
        prefix.push(0usize);
        for present in island_by_preorder {
            let count = prefix
                .last()
                .copied()
                .ok_or_else(|| StructureError::invalid("island prefix lost its initial count"))?
                .checked_add(usize::from(present))
                .ok_or_else(|| StructureError::invalid("island block count overflowed"))?;
            prefix.push(count);
        }
        Some(prefix)
    };

    for (index, branch) in input.branches.iter().enumerate() {
        let Some(region) = branch.region.as_ref() else {
            continue;
        };
        let Some(fence) = region.single_pass_fence.as_ref() else {
            continue;
        };
        let mut blocks = region
            .structured_blocks(graph_facts)
            .map_err(|block| {
                StructureError::invalid(format!(
                    "single-pass region references block {block} outside dominator preorder"
                ))
            })?
            .collect::<BTreeSet<_>>();
        blocks.insert(region.merge);
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        let valid_tail = matches!(
            cfg.succs.get(region.merge.index()).map(Vec::as_slice),
            Some([edge]) if cfg.edges.get(edge.index()).is_some_and(|edge| edge.to == fence.exit)
        );
        let valid_escapes = !fence.escape_edges.is_empty()
            && fence.escape_edges.iter().all(|edge| {
                cfg.edges.get(edge.index()).is_some_and(|edge| {
                    blocks.contains(&edge.from)
                        && edge.from != region.merge
                        && edge.to == fence.exit
                })
            });
        if !valid_tail || !valid_escapes || !single_entry(cfg, &blocks, branch.branch.header) {
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::SinglePass(super::super::BranchPlanId(index)),
            blocks,
            graph_facts,
        )?);
    }

    for (index, _) in input.loops.iter().enumerate() {
        let id = super::super::LoopPlanId(index);
        let blocks = partitions
            .get(index)
            .map_or_else(BTreeSet::new, |partition| {
                let mut blocks = partition.owned.clone();
                if let Some(normal_tail) = &partition.normal_tail {
                    blocks.extend(normal_tail.blocks.iter().copied());
                }
                blocks
            });
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        if blocks.is_empty() {
            continue;
        }
        let partition = partitions
            .get(id.index())
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        let entry = partition
            .preheader
            .unwrap_or(input.loops[id.index()].candidate.header);
        if !single_entry(cfg, &blocks, entry) {
            push_residual_seed(&mut residuals, entry, blocks);
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::Loop(id),
            blocks,
            graph_facts,
        )?);
    }

    let mut value_decision_blocks = BTreeSet::new();
    for (index, decision) in input.value_decisions.iter().enumerate() {
        let id = super::super::ValueDecisionPlanId(index);
        let blocks = reachable_nonempty_blocks(cfg, decision.candidate.blocks.clone());
        let decision = &input.value_decisions[id.index()].candidate;
        let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
            continue;
        };
        if blocks.is_empty()
            || blocks.contains(&continuation)
            || !single_entry(cfg, &blocks, decision.header)
            || !value_decision_is_closed(cfg, &blocks, continuation)
        {
            continue;
        }
        // 编译器会把 `a and b or c` 的控制子图压成“共享 tail + 跳过 tail”形状，
        // 与一次性 fence 的图形证据完全重合。闭合 ValueDecision 已证明所有 edge 和
        // result phi 都由表达式 DAG 消费，语义强于只描述控制跳出的 SinglePass；
        // 同一 block 集只能保留前者，不能让 fence 抢占 owner 后再把 decision 降成 goto。
        pending.retain(|candidate| {
            !matches!(candidate.kind, ContainerKind::SinglePass(_)) || candidate.blocks != blocks
        });
        value_decision_blocks.extend(blocks.iter().copied());
        pending.push(PendingContainer::exact(
            ContainerKind::ValueDecision(id),
            blocks,
            graph_facts,
        )?);
    }

    let loop_control_blocks = partitions
        .iter()
        .flat_map(|partition| partition.control.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut claimed_condition_headers = BTreeSet::new();
    for (index, loop_) in input.loops.iter().enumerate() {
        if let Some(condition) = loop_
            .condition
            .and_then(|id| input.conditions.get(id.index()))
            .filter(|condition| {
                partitions.get(index).is_some_and(|partition| {
                    condition
                        .candidate
                        .blocks
                        .iter()
                        .all(|block| partition.control.contains(block))
                })
            })
        {
            claimed_condition_headers.extend(condition.candidate.blocks.iter().copied());
        }
    }
    for branch in &input.branches {
        if let Some(condition) = branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
        {
            claimed_condition_headers.extend(
                condition
                    .candidate
                    .blocks
                    .iter()
                    .copied()
                    .filter(|block| *block != branch.branch.header),
            );
        }
    }
    let mut loop_owned_by_block = vec![false; cfg.blocks.len()];
    for partition in partitions {
        for block in partition.owned.iter().copied().chain(
            partition
                .normal_tail
                .iter()
                .flat_map(|tail| tail.blocks.iter().copied()),
        ) {
            loop_owned_by_block[block.index()] = true;
        }
    }
    for (index, branch) in input.branches.iter().enumerate() {
        if loop_control_blocks.contains(&branch.branch.header)
            || claimed_condition_headers.contains(&branch.branch.header)
            || value_decision_blocks.contains(&branch.branch.header)
        {
            continue;
        }
        let id = super::super::BranchPlanId(index);
        if !loop_owned_by_block[branch.branch.header.index()]
            && let Some(ranges) = ordinary_branch_ranges(cfg, graph_facts, input, branch)?
        {
            let intersects_island = if let Some(prefix) = &island_prefix {
                preorder_ranges_intersect_prefix(&ranges, prefix)?
            } else {
                false
            };
            if !intersects_island {
                pending.push(PendingContainer::intervals(
                    ContainerKind::Branch(id),
                    ranges,
                    graph_facts,
                )?);
                continue;
            }
        }
        // branch-region evidence 只证明已识别的结构片段，不承诺穷尽整个 arm。
        // 最终 containment 必须从 header 的支配子树补齐，否则短路条件后的单臂
        // exit block 会掉到 branch sibling，原本有条件的 goto/break 将变成无条件。
        let normalize = |mut blocks: BTreeSet<BlockRef>| {
            blocks.insert(branch.branch.header);
            if let Some(condition) = branch
                .condition
                .and_then(|id| input.conditions.get(id.index()))
            {
                blocks.extend(condition.candidate.blocks.iter().copied());
            }
            for partition in partitions
                .iter()
                .filter(|partition| partition.owned.contains(&branch.branch.header))
            {
                let claimed = if partition.control.contains(&branch.branch.header) {
                    &partition.control
                } else if partition.preheader == Some(branch.branch.header) {
                    continue;
                } else {
                    &partition.body
                };
                blocks.retain(|block| claimed.contains(block));
            }
            // structured branch 必须由 header 单入口支配；共享 continuation 的 sibling
            // 只能由外层 region 持有，不能污染当前 branch containment。
            blocks.retain(|block| graph_facts.dominates(branch.branch.header, *block));
            blocks.retain(|block| branch_part(branch, input, graph_facts, *block).is_some());
            reachable_nonempty_blocks(cfg, blocks)
        };
        let evidence = branch
            .region
            .as_ref()
            .map(|region| {
                region
                    .structured_blocks(graph_facts)
                    .map(|blocks| blocks.collect::<BTreeSet<_>>())
                    .map_err(|block| {
                        StructureError::invalid(format!(
                            "branch region references block {block} outside dominator preorder"
                        ))
                    })
            })
            .transpose()?;
        let mut expanded = branch_default_blocks(graph_facts, branch);
        if let Some(evidence) = &evidence {
            expanded.extend(evidence);
        }
        let mut blocks = normalize(expanded);
        if !single_entry(cfg, &blocks, branch.branch.header)
            && let Some(evidence) = evidence
        {
            // 一个 default arm target 也可能是嵌套结构的共享 continuation。此时扩展
            // 会制造假多入口；退回已验证 evidence，而不是把可规约图升级成 island。
            let evidence = normalize(evidence);
            if single_entry(cfg, &evidence, branch.branch.header) {
                blocks = evidence;
            }
        }
        let branch = &input.branches[id.index()];
        if blocks.is_empty() {
            continue;
        }
        if unstructured_blocks.iter().any(|island| {
            island.is_subset(&blocks)
                && branch_part_for_blocks(branch, input, graph_facts, island).is_none()
        }) {
            // island 内部图可以跨越一个表面 branch 的两条 arm；这种 branch 不能再做
            // island 的 containment parent，否则树 ownership 与 island 的真实图边矛盾。
            continue;
        }
        if !single_entry(cfg, &blocks, branch.branch.header) {
            push_residual_seed(&mut residuals, branch.branch.header, blocks);
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::Branch(id),
            blocks,
            graph_facts,
        )?);
    }

    if !unstructured_blocks.is_empty() {
        let mut islands_by_block = vec![Vec::new(); cfg.blocks.len()];
        for (island, blocks) in unstructured_blocks.iter().enumerate() {
            for block in blocks {
                islands_by_block[block.index()].push(island);
            }
        }
        let mut protected_pending = Vec::with_capacity(pending.len());
        for mut candidate in pending {
            if matches!(candidate.kind, ContainerKind::Island(_)) {
                protected_pending.push(candidate);
                continue;
            }
            let mut intersections = BTreeMap::<usize, usize>::new();
            for block in &candidate.blocks {
                for island in &islands_by_block[block.index()] {
                    *intersections.entry(*island).or_default() += 1;
                }
            }
            let crossed_islands = intersections
                .into_iter()
                .filter_map(|(island, intersection)| {
                    (intersection < unstructured_blocks[island].len()
                        && candidate.blocks.len() > intersection)
                        .then_some(island)
                })
                .collect::<Vec<_>>();
            for island in &crossed_islands {
                candidate
                    .blocks
                    .extend(unstructured_blocks[*island].iter().copied());
            }
            if !crossed_islands.is_empty() {
                push_residual_seed(
                    &mut residuals,
                    container_entry(candidate.kind, input, partitions),
                    candidate.blocks,
                );
            } else {
                protected_pending.push(candidate);
            }
        }
        pending = protected_pending;
    }

    pending.sort_by_key(|pending| {
        (
            Reverse(pending.block_count),
            Reverse(container_same_size_rank(pending.kind)),
            pending_kind_index(pending.kind),
        )
    });
    let mut specs = Vec::with_capacity(pending.len());
    let mut owners = RangeOwnerTree::new(graph_facts.dominator_tree.order.len());
    for candidate in pending {
        let kind = candidate.kind;
        match try_insert_candidate(&mut specs, &mut owners, candidate)? {
            InsertDisposition::Inserted => {}
            InsertDisposition::Rejected(_) if matches!(kind, ContainerKind::Island(_)) => {
                return Err(StructureError::invalid(format!(
                    "protected island #{} was rejected from containment",
                    pending_kind_index(kind)
                )));
            }
            InsertDisposition::Rejected(_) if matches!(kind, ContainerKind::ValueDecision(_)) => {}
            InsertDisposition::Rejected(candidate) => {
                let entry = match kind {
                    ContainerKind::Loop(id) => partitions[id.index()]
                        .preheader
                        .unwrap_or(input.loops[id.index()].candidate.header),
                    ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => {
                        input.branches[id.index()].branch.header
                    }
                    ContainerKind::ValueDecision(_)
                    | ContainerKind::Island(_)
                    | ContainerKind::Residual(_) => continue,
                };
                push_residual_seed(
                    &mut residuals,
                    entry,
                    candidate.materialize_blocks(graph_facts)?,
                );
            }
        }
    }

    let mut dispositions = normalize_residual_specs(cfg, graph_facts, &mut specs, &residuals)?;
    let mut owner_by_block = build_container_topology(cfg, graph_facts, &mut specs)?;
    flatten_nested_unstructured_specs(&mut specs, &mut owner_by_block, &mut dispositions)?;
    validate_aggregate_seed_dispositions(cfg, input, &residuals, &specs, &dispositions)?;

    materialize_regions(cfg, graph_facts, input, partitions, specs, owner_by_block)
}

pub(super) fn push_residual_seed(
    residuals: &mut Vec<ResidualSeed>,
    entry: BlockRef,
    blocks: BTreeSet<BlockRef>,
) {
    residuals.push(ResidualSeed {
        id: ResidualSeedId(residuals.len()),
        entry,
        blocks,
    });
}

pub(super) fn materialize_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    specs: Vec<ContainerSpec>,
    owner_by_block: Vec<Option<usize>>,
) -> Result<RegionArena, StructureError> {
    let root = RegionId(0);
    let mut regions = vec![Some(RegionPlan::Sequence {
        parent: None,
        children: Vec::new(),
    })];
    let mut slots = Vec::with_capacity(specs.len());
    for spec in &specs {
        let region = reserve(&mut regions);
        let slot = match spec.kind {
            ContainerKind::SinglePass(_) => ContainerSlots::SinglePass { region },
            ContainerKind::Branch(id) => {
                let condition = reserve_sequence(&mut regions, region);
                let then_arm = reserve_sequence(&mut regions, region);
                let else_arm = input.branches[id.index()]
                    .branch
                    .else_entry
                    .map(|_| reserve_sequence(&mut regions, region));
                ContainerSlots::Branch {
                    region,
                    condition,
                    then_arm,
                    else_arm,
                }
            }
            ContainerKind::Loop(id) => ContainerSlots::Loop {
                region,
                preheader: partitions[id.index()]
                    .preheader
                    .map(|_| reserve_sequence(&mut regions, region)),
                control: reserve_sequence(&mut regions, region),
                body: reserve_sequence(&mut regions, region),
                normal_tail: partitions[id.index()]
                    .normal_tail
                    .as_ref()
                    .map(|_| reserve_sequence(&mut regions, region)),
            },
            ContainerKind::ValueDecision(_) => ContainerSlots::ValueDecision { region },
            ContainerKind::Island(_) | ContainerKind::Residual(_) => {
                ContainerSlots::Island { region }
            }
        };
        slots.push(slot);
    }

    let mut sequence_items = vec![Vec::<(usize, RegionId)>::new(); regions.len()];
    let mut island_items = vec![Vec::<(usize, UnstructuredLayoutItem)>::new(); regions.len()];
    let mut island_regions = vec![false; regions.len()];
    for slot in &slots {
        if let ContainerSlots::Island { region } = slot {
            island_regions[region.index()] = true;
        }
    }
    let rank = block_ranks(cfg);
    let mut loop_region_by_plan = vec![root; input.loops.len()];
    let mut value_decision_region_by_plan = vec![root; input.value_decisions.len()];
    let mut single_pass_region_by_branch = vec![None; input.branches.len()];

    for (index, spec) in specs.iter().enumerate() {
        let slot = slots[index];
        let parent = attachment_for_container(
            spec.parent,
            spec,
            &specs,
            &slots,
            input,
            partitions,
            graph_facts,
        )?;
        append_region(
            parent,
            slot.region(),
            spec.first_rank,
            &island_regions,
            &mut sequence_items,
            &mut island_items,
        )?;

        let plan = match (spec.kind, slot) {
            (ContainerKind::SinglePass(id), ContainerSlots::SinglePass { region }) => {
                single_pass_region_by_branch[id.index()] = Some(region);
                RegionPlan::Sequence {
                    parent: Some(parent),
                    children: Vec::new(),
                }
            }
            (
                ContainerKind::Branch(id),
                ContainerSlots::Branch {
                    region: _,
                    condition,
                    then_arm,
                    else_arm,
                },
            ) => {
                let branch = &input.branches[id.index()].branch;
                RegionPlan::Branch {
                    parent,
                    plan: id,
                    entry: branch.header,
                    condition,
                    then_arm,
                    else_arm,
                    continuation: branch.merge,
                }
            }
            (
                ContainerKind::Loop(id),
                ContainerSlots::Loop {
                    preheader,
                    control,
                    body,
                    normal_tail,
                    ..
                },
            ) => {
                loop_region_by_plan[id.index()] = slot.region();
                let loop_ = &input.loops[id.index()];
                let partition = &partitions[id.index()];
                RegionPlan::Loop {
                    parent,
                    plan: id,
                    entry: partition.preheader.unwrap_or(loop_.candidate.header),
                    preheader,
                    control,
                    body,
                    normal_tail,
                }
            }
            (ContainerKind::ValueDecision(id), ContainerSlots::ValueDecision { .. }) => {
                let decision = &input.value_decisions[id.index()].candidate;
                let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
                    return Err(StructureError::invalid(
                        "value decision container does not have a value merge",
                    ));
                };
                value_decision_region_by_plan[id.index()] = slot.region();
                RegionPlan::ValueDecision {
                    parent,
                    plan: id,
                    entry: decision.header,
                    continuation,
                }
            }
            (ContainerKind::Island(island), ContainerSlots::Island { .. }) => {
                RegionPlan::Unstructured {
                    parent,
                    entry: input.unstructured[island].fact.entry,
                    entries: Vec::new(),
                    layout: Vec::new(),
                    exits: Vec::new(),
                }
            }
            (ContainerKind::Residual(entry), ContainerSlots::Island { .. }) => {
                RegionPlan::Unstructured {
                    parent,
                    entry,
                    entries: Vec::new(),
                    layout: Vec::new(),
                    exits: Vec::new(),
                }
            }
            _ => return Err(StructureError::invalid("container slot kind mismatch")),
        };
        regions[slot.region().index()] = Some(plan);
    }

    let mut region_by_block = vec![None; cfg.blocks.len()];
    for block in cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| cfg.reachable_blocks.contains(block))
    {
        let owner = owner_by_block[block.index()];
        if owner.is_some_and(|index| {
            matches!(
                specs[index].kind,
                ContainerKind::Island(_)
                    | ContainerKind::Residual(_)
                    | ContainerKind::ValueDecision(_)
            )
        }) {
            let owner = owner.ok_or_else(|| {
                StructureError::invalid(format!("aggregate block {block} has no container owner"))
            })?;
            let region = slots[owner].region();
            region_by_block[block.index()] = Some(region);
            if matches!(
                specs[owner].kind,
                ContainerKind::Island(_) | ContainerKind::Residual(_)
            ) {
                island_items[region.index()]
                    .push((rank[block.index()], UnstructuredLayoutItem::Block(block)));
            }
            continue;
        }
        let parent =
            attachment_for_block(owner, block, &specs, &slots, input, partitions, graph_facts)?;
        let region = reserve(&mut regions);
        if sequence_items.len() < regions.len() {
            sequence_items.push(Vec::new());
            island_items.push(Vec::new());
        }
        regions[region.index()] = Some(RegionPlan::Block { parent, block });
        region_by_block[block.index()] = Some(region);
        sequence_items[parent.index()].push((rank[block.index()], region));
    }

    for (index, items) in sequence_items.iter_mut().enumerate() {
        items.sort_by_key(|(rank, region)| (*rank, region.index()));
        if let Some(RegionPlan::Sequence { children, .. }) = regions[index].as_mut() {
            *children = items.iter().map(|(_, region)| *region).collect();
        }
    }
    for (index, items) in island_items.iter_mut().enumerate() {
        items.sort_by_key(|(rank, item)| {
            let tie = match item {
                UnstructuredLayoutItem::Block(block) => block.index(),
                UnstructuredLayoutItem::Region(region) => region.index(),
            };
            (*rank, tie)
        });
        if let Some(RegionPlan::Unstructured { layout, .. }) = regions[index].as_mut() {
            *layout = items.iter().map(|(_, item)| *item).collect();
        }
    }

    let mut regions = regions
        .into_iter()
        .enumerate()
        .map(|(index, region)| {
            region.ok_or_else(|| StructureError::invalid(format!("region #{index} was not filled")))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let navigation = RegionNavigation::build(cfg, root, &regions, &region_by_block)?;
    order_sequence_children_by_flow(cfg, graph_facts, &mut regions, &navigation)?;
    let mut ports = navigation.collect_island_ports(cfg, &regions)?;
    for (index, region) in regions.iter_mut().enumerate() {
        let RegionPlan::Unstructured { entries, exits, .. } = region else {
            continue;
        };
        *entries = std::mem::take(&mut ports.entries[index]);
        *exits = std::mem::take(&mut ports.exits[index]);
    }
    let mut single_passes = Vec::new();
    let mut single_pass_by_region = vec![None; regions.len()];
    for (branch_index, region) in single_pass_region_by_branch.into_iter().enumerate() {
        let Some(region) = region else {
            continue;
        };
        let branch = input.branches.get(branch_index).ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing branch evidence")
        })?;
        let branch_region = branch.region.as_ref().ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing branch region")
        })?;
        let fence = branch_region.single_pass_fence.as_ref().ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing fence evidence")
        })?;
        let id = super::super::SinglePassPlanId(single_passes.len());
        single_pass_by_region[region.index()] = Some(id);
        single_passes.push(super::super::SinglePassPlan {
            region,
            entry: branch.branch.header,
            tail: branch_region.merge,
            continuation: fence.exit,
            escape_edges: fence.escape_edges.iter().copied().collect(),
        });
    }
    Ok(RegionArena {
        regions,
        region_by_block,
        navigation,
        loop_region_by_plan,
        value_decision_region_by_plan,
        single_passes,
        single_pass_by_region,
        specs,
        slots,
    })
}

/// 物理指令顺序不是结构化 sequence 的执行顺序：编译器可以把 loop tail 放到 header
/// 之前，再用回边连接。这里按 sibling 之间真实存在的 CFG 边做稳定拓扑排序；若 sibling
/// 图本身含环，则它属于必须保留显式 transfer 的图形，继续使用稳定物理 layout。
pub(super) fn order_sequence_children_by_flow(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    regions: &mut [RegionPlan],
    navigation: &RegionNavigation,
) -> Result<(), StructureError> {
    let mut is_backedge = vec![false; cfg.edges.len()];
    for edge in &graph_facts.backedges {
        is_backedge[edge.index()] = true;
    }
    let mut successors = vec![Vec::new(); regions.len()];
    let mut indegree = vec![0usize; regions.len()];
    for (edge_index, _edge) in cfg.edges.iter().enumerate() {
        if is_backedge[edge_index] {
            continue;
        }
        let Some(relation) = navigation.edge_relation(EdgeRef(edge_index)) else {
            continue;
        };
        let Some(owner) = relation.lca else {
            continue;
        };
        if !matches!(
            regions.get(owner.index()),
            Some(RegionPlan::Sequence { .. })
        ) {
            continue;
        }
        let Some(source) = relation.source_child else {
            continue;
        };
        let Some(target) = relation.target_child else {
            continue;
        };
        if source == target {
            continue;
        }
        successors[source.index()].push(target);
        indegree[target.index()] = indegree[target.index()]
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("sequence sibling indegree overflowed"))?;
    }

    for region in regions {
        let RegionPlan::Sequence { children, .. } = region else {
            continue;
        };
        if children.len() < 2 {
            continue;
        }
        let original = children.clone();
        let mut ready = original
            .iter()
            .copied()
            .filter(|child| indegree[child.index()] == 0)
            .collect::<VecDeque<_>>();
        let mut ordered = Vec::with_capacity(original.len());
        while let Some(child) = ready.pop_front() {
            ordered.push(child);
            for successor in &successors[child.index()] {
                let degree = indegree.get_mut(successor.index()).ok_or_else(|| {
                    StructureError::invalid("sequence successor is outside the region arena")
                })?;
                *degree = degree.checked_sub(1).ok_or_else(|| {
                    StructureError::invalid("sequence sibling indegree underflowed")
                })?;
                if *degree == 0 {
                    ready.push_back(*successor);
                }
            }
        }
        if ordered.len() == original.len() {
            *children = ordered;
        }
    }
    Ok(())
}
