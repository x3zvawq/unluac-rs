//! 候选插入与 residual 归一化。输入是已经冻结边界的 container specs，输出唯一 containment 插入结果；不负责重判 branch/loop 语义。例如 branch arm 与 loop part 的集合关系会在这里转换成插入位置。

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BranchPart {
    Condition,
    Then,
    Else,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LoopPart {
    Preheader,
    Control,
    Body,
    NormalTail,
}

pub(super) fn reachable_nonempty_blocks(
    cfg: &Cfg,
    mut blocks: BTreeSet<BlockRef>,
) -> BTreeSet<BlockRef> {
    blocks.retain(|block| *block != cfg.exit_block && cfg.reachable_blocks.contains(block));
    blocks
}

pub(super) fn single_entry(cfg: &Cfg, blocks: &BTreeSet<BlockRef>, entry: BlockRef) -> bool {
    blocks.contains(&entry)
        && blocks.iter().copied().all(|block| {
            cfg.preds[block.index()].iter().all(|edge| {
                let predecessor = cfg.edges[edge.index()].from;
                !cfg.reachable_blocks.contains(&predecessor)
                    || blocks.contains(&predecessor)
                    || block == entry
            })
        })
}

pub(super) fn value_decision_is_closed(
    cfg: &Cfg,
    blocks: &BTreeSet<BlockRef>,
    continuation: BlockRef,
) -> bool {
    blocks.iter().copied().all(|block| {
        cfg.succs[block.index()].iter().all(|edge| {
            let target = cfg.edges[edge.index()].to;
            blocks.contains(&target) || target == continuation
        })
    })
}

pub(super) enum InsertDisposition {
    Inserted,
    Rejected(PendingContainer),
}

pub(super) fn pending_kind_index(kind: ContainerKind) -> usize {
    match kind {
        ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => id.index(),
        ContainerKind::ValueDecision(id) => id.index(),
        ContainerKind::Loop(id) => id.index(),
        ContainerKind::Island(index) => index,
        ContainerKind::Residual(entry) => entry.index(),
    }
}

pub(super) fn container_entry(
    kind: ContainerKind,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
) -> BlockRef {
    match kind {
        ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => {
            input.branches[id.index()].branch.header
        }
        ContainerKind::ValueDecision(id) => input.value_decisions[id.index()].candidate.header,
        ContainerKind::Loop(id) => partitions[id.index()]
            .preheader
            .unwrap_or(input.loops[id.index()].candidate.header),
        ContainerKind::Island(index) => input.unstructured[index].fact.entry,
        ContainerKind::Residual(entry) => entry,
    }
}

pub(super) fn branch_default_blocks(
    graph_facts: &GraphFacts,
    branch: &super::super::BranchPlanInput,
) -> BTreeSet<BlockRef> {
    let Some(start) = graph_facts.dominator_tree.preorder_index[branch.branch.header.index()]
    else {
        return BTreeSet::new();
    };
    let Some(end) = graph_facts.dominator_tree.subtree_end[branch.branch.header.index()] else {
        return BTreeSet::new();
    };
    let merge = branch.branch.merge;
    let backward_continuation = merge.is_some_and(|merge| {
        merge != branch.branch.header && graph_facts.dominates(merge, branch.branch.header)
    });
    graph_facts.dominator_tree.order[start..end]
        .iter()
        .copied()
        .filter(|block| {
            merge.is_none_or(|merge| {
                *block != merge && (backward_continuation || !graph_facts.dominates(merge, *block))
            })
        })
        .collect()
}

pub(super) fn ordinary_branch_ranges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    branch: &super::super::BranchPlanInput,
) -> Result<Option<Vec<std::ops::Range<usize>>>, StructureError> {
    if branch
        .region
        .as_ref()
        .is_some_and(|region| region.single_pass_fence.is_some())
        || branch.branch.merge.is_some_and(|merge| {
            merge == branch.branch.header || graph_facts.dominates(merge, branch.branch.header)
        })
    {
        return Ok(None);
    }
    let position = |block: BlockRef| {
        graph_facts
            .dominator_tree
            .preorder_index
            .get(block.index())
            .copied()
            .flatten()
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "ordinary branch references unreachable block {block}"
                ))
            })
    };
    let subtree = |block: BlockRef| {
        Ok(position(block)?
            ..graph_facts
                .dominator_tree
                .subtree_end
                .get(block.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "ordinary branch has no dominator subtree for {block}"
                    ))
                })?)
    };

    let header_range = subtree(branch.branch.header)?;
    let mut ranges = if let Some(merge) = branch.branch.merge {
        BranchRegionFact::new(
            graph_facts,
            branch.branch.header,
            merge,
            branch.branch.kind,
            None,
        )
        .preorder_intervals(graph_facts)
        .map_err(|block| {
            StructureError::invalid(format!(
                "ordinary branch boundary references unreachable block {block}"
            ))
        })?
    } else {
        vec![header_range.clone()]
    };
    if let Some(region) = &branch.region {
        ranges.extend(region.preorder_intervals(graph_facts).map_err(|block| {
            StructureError::invalid(format!(
                "branch evidence references unreachable block {block}"
            ))
        })?);
    }
    ranges = intersect_preorder_ranges(
        &merge_preorder_ranges(ranges),
        std::slice::from_ref(&header_range),
    );

    if branch.branch.else_entry.is_some() {
        let Some((then_entry, Some(else_entry))) = branch_arm_entries(branch, input) else {
            return Ok(None);
        };
        if graph_facts.dominates(then_entry, else_entry)
            || graph_facts.dominates(else_entry, then_entry)
        {
            return Ok(None);
        }
        let allowed = merge_preorder_ranges(vec![subtree(then_entry)?, subtree(else_entry)?]);
        ranges = intersect_preorder_ranges(&ranges, &allowed);
        ranges.push(position(branch.branch.header)?..position(branch.branch.header)? + 1);
        if let Some(condition) = branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
        {
            ranges.extend(preorder_ranges_for_block_iter(
                graph_facts,
                condition
                    .candidate
                    .blocks
                    .iter()
                    .copied()
                    .filter(|block| graph_facts.dominates(branch.branch.header, *block)),
            )?);
        }
    }

    let exit_position = graph_facts
        .dominator_tree
        .preorder_index
        .get(cfg.exit_block.index())
        .copied()
        .flatten();
    let ranges = exclude_preorder_position(merge_preorder_ranges(ranges), exit_position);
    Ok((!ranges.is_empty()).then_some(ranges))
}

pub(super) fn try_insert_candidate(
    specs: &mut Vec<ContainerSpec>,
    owners: &mut RangeOwnerTree,
    candidate: PendingContainer,
) -> Result<InsertDisposition, StructureError> {
    let RangeOwnerState::Uniform(parent) = owners.uniform_owner(&candidate.ranges)? else {
        return Ok(InsertDisposition::Rejected(candidate));
    };
    let kind = candidate.kind;
    if let Some(parent_index) = parent {
        let parent_spec = &specs[parent_index];
        if parent_spec.block_count == candidate.block_count {
            let duplicate_allowed = matches!(
                (parent_spec.kind, kind),
                (ContainerKind::Loop(_), ContainerKind::Branch(_))
            );
            let value_decision_exact = matches!(kind, ContainerKind::ValueDecision(_));
            if !duplicate_allowed || value_decision_exact {
                return Ok(InsertDisposition::Rejected(candidate));
            }
        } else if matches!(kind, ContainerKind::ValueDecision(_))
            && matches!(parent_spec.kind, ContainerKind::ValueDecision(_))
        {
            return Ok(InsertDisposition::Rejected(candidate));
        }
    }
    let index = specs.len();
    owners.assign(&candidate.ranges, index)?;
    specs.push(candidate.into_spec());
    Ok(InsertDisposition::Inserted)
}

pub(super) fn normalize_residual_specs(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    specs: &mut Vec<ContainerSpec>,
    residuals: &[ResidualSeed],
) -> Result<AggregateSeedDispositions, StructureError> {
    if residuals.is_empty() {
        let mut islands = vec![
            None;
            specs
                .iter()
                .filter_map(|spec| match spec.kind {
                    ContainerKind::Island(index) => Some(index + 1),
                    _ => None,
                })
                .max()
                .unwrap_or(0)
        ];
        for (index, spec) in specs.iter().enumerate() {
            if let ContainerKind::Island(island) = spec.kind {
                let slot = islands.get_mut(island).ok_or_else(|| {
                    StructureError::invalid("island seed index overflowed its disposition arena")
                })?;
                if slot.replace(index).is_some() {
                    return Err(StructureError::invalid(format!(
                        "protected island #{island} has multiple final dispositions"
                    )));
                }
            }
        }
        return Ok(AggregateSeedDispositions {
            residuals: Vec::new(),
            islands,
        });
    }

    // Residual 聚合本来就需要精确 block incidence；只在这条异常路径展开
    // interval domain，正常 structured containment 保持区间表示。
    for spec in specs.iter_mut() {
        if spec.blocks.is_empty() {
            spec.blocks = materialize_preorder_ranges(graph_facts, &spec.ranges)?;
        }
    }

    let mut seed_dsu = DisjointSet::new(residuals.len());
    let mut seed_by_block = vec![None; cfg.blocks.len()];
    for seed in residuals {
        if seed.id.index() >= residuals.len() {
            return Err(StructureError::invalid(
                "residual seed id is outside the seed arena",
            ));
        }
        for block in &seed.blocks {
            let slot = seed_by_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid("residual seed references a missing block")
            })?;
            if let Some(other) = *slot {
                seed_dsu.union(seed.id.index(), other);
            } else {
                *slot = Some(seed.id.index());
            }
        }
    }

    let mut component_by_seed_root = vec![None; residuals.len()];
    let mut initial_components = Vec::<ResidualComponent>::new();
    for seed in residuals {
        let root = seed_dsu.find(seed.id.index());
        let component = if let Some(component) = component_by_seed_root[root] {
            component
        } else {
            let component = initial_components.len();
            component_by_seed_root[root] = Some(component);
            initial_components.push(ResidualComponent {
                blocks: BTreeSet::new(),
                seeds: Vec::new(),
            });
            component
        };
        initial_components[component]
            .blocks
            .extend(seed.blocks.iter().copied());
        initial_components[component].seeds.push(seed.id);
    }

    let mut initial_component_by_block = vec![None; cfg.blocks.len()];
    for (index, component) in initial_components.iter().enumerate() {
        for block in &component.blocks {
            let slot = &mut initial_component_by_block[block.index()];
            if slot.replace(index).is_some_and(|owner| owner != index) {
                return Err(StructureError::invalid(format!(
                    "overlapping residual seeds at block {block} were not merged"
                )));
            }
        }
    }

    // 现有 spec 已经是 laminar family。residual component 只有在同时拥有 spec
    // 内外 block、又没有覆盖完整 spec 时才构成交叉；吸收该 spec 只会合并已经与它
    // 相交的 component，不会再与无关 spec 产生新交叉。因此按 block incidence
    // 扫描一次即可求完整闭包，不需要 restart scan。
    let mut component_dsu = DisjointSet::new(initial_components.len());
    let mut crossed_specs = vec![false; specs.len()];
    let mut intersections = DenseIntersectionWorkspace::new(initial_components.len());
    for (spec_index, spec) in specs.iter().enumerate() {
        intersections.populate(&spec.blocks, &initial_component_by_block);
        let crossed = intersections.touched.iter().copied().any(|component| {
            intersections.counts[component] < spec.blocks.len()
                && initial_components[component].blocks.len() > intersections.counts[component]
        });
        if !crossed {
            continue;
        }
        crossed_specs[spec_index] = true;
        let mut incident = intersections.touched.iter().copied();
        let Some(first) = incident.next() else {
            return Err(StructureError::invalid(
                "crossed container has no incident residual component",
            ));
        };
        for component in incident {
            component_dsu.union(first, component);
        }
    }

    let mut component_by_root = vec![None; initial_components.len()];
    let mut components = Vec::<ResidualComponent>::new();
    for (initial, component) in initial_components.iter().enumerate() {
        let root = component_dsu.find(initial);
        let final_index = if let Some(index) = component_by_root[root] {
            index
        } else {
            let index = components.len();
            component_by_root[root] = Some(index);
            components.push(ResidualComponent {
                blocks: BTreeSet::new(),
                seeds: Vec::new(),
            });
            index
        };
        components[final_index]
            .blocks
            .extend(component.blocks.iter().copied());
        components[final_index]
            .seeds
            .extend(component.seeds.iter().copied());
    }
    for (index, spec) in specs.iter().enumerate() {
        if !crossed_specs[index] {
            continue;
        }
        let initial = spec
            .blocks
            .iter()
            .find_map(|block| initial_component_by_block[block.index()])
            .ok_or_else(|| {
                StructureError::invalid("crossed container lost its residual component")
            })?;
        let root = component_dsu.find(initial);
        let component = component_by_root[root].ok_or_else(|| {
            StructureError::invalid("crossed container references a missing residual component")
        })?;
        components[component]
            .blocks
            .extend(spec.blocks.iter().copied());
    }

    let rank = block_ranks(cfg);
    components.sort_by_key(|component| {
        component
            .blocks
            .iter()
            .map(|block| (rank[block.index()], block.index()))
            .min()
            .unwrap_or((usize::MAX, usize::MAX))
    });
    let mut component_by_block = vec![None; cfg.blocks.len()];
    let mut component_by_seed = vec![None; residuals.len()];
    for (index, component) in components.iter().enumerate() {
        for block in &component.blocks {
            let slot = &mut component_by_block[block.index()];
            if slot.replace(index).is_some_and(|owner| owner != index) {
                return Err(StructureError::invalid(format!(
                    "normalized residual components still overlap at block {block}"
                )));
            }
        }
        for seed in &component.seeds {
            let slot = component_by_seed.get_mut(seed.index()).ok_or_else(|| {
                StructureError::invalid("residual component contains a missing seed")
            })?;
            if slot.replace(index).is_some() {
                return Err(StructureError::invalid(format!(
                    "residual seed #{} belongs to multiple normalized components",
                    seed.index()
                )));
            }
        }
    }

    let mut removed = vec![false; specs.len()];
    let mut exact_island_by_component = vec![None; components.len()];
    let mut intersections = DenseIntersectionWorkspace::new(components.len());
    for (index, spec) in specs.iter().enumerate() {
        intersections.populate(&spec.blocks, &component_by_block);
        for component in intersections.touched.iter().copied() {
            let intersection = intersections.counts[component];
            if intersection < spec.blocks.len() && components[component].blocks.len() > intersection
            {
                return Err(StructureError::invalid(format!(
                    "residual component #{component} still partially crosses container #{index}"
                )));
            }
        }
        let exact_component = intersections.touched.iter().copied().find(|component| {
            intersections.counts[*component] == spec.blocks.len()
                && components[*component].blocks.len() == spec.blocks.len()
        });
        match spec.kind {
            ContainerKind::Island(island) => {
                if let Some(component) = exact_component {
                    let slot = &mut exact_island_by_component[component];
                    if slot.replace(island).is_some() {
                        return Err(StructureError::invalid(format!(
                            "residual component #{component} exactly matches multiple islands"
                        )));
                    }
                }
            }
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Residual(_) => {
                removed[index] = crossed_specs[index] || exact_component.is_some();
            }
        }
    }

    let mut retained = Vec::with_capacity(specs.len() + components.len());
    let mut islands = Vec::<Option<usize>>::new();
    for (index, spec) in specs.drain(..).enumerate() {
        if removed[index] {
            continue;
        }
        let final_index = retained.len();
        if let ContainerKind::Island(island) = spec.kind {
            if islands.len() <= island {
                islands.resize(island + 1, None);
            }
            if islands[island].replace(final_index).is_some() {
                return Err(StructureError::invalid(format!(
                    "protected island #{island} has multiple final dispositions"
                )));
            }
        }
        retained.push(spec);
    }

    let mut component_dispositions = vec![None; components.len()];
    for (component_index, component) in components.into_iter().enumerate() {
        if let Some(island) = exact_island_by_component[component_index] {
            component_dispositions[component_index] =
                Some(AggregateSeedDisposition::Island(island));
            continue;
        }
        let entry = component
            .seeds
            .iter()
            .filter_map(|seed| residuals.get(seed.index()))
            .map(|seed| seed.entry)
            .filter(|entry| component.blocks.contains(entry))
            .min_by_key(|entry| (rank[entry.index()], entry.index()))
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "residual component #{component_index} has no contained seed entry"
                ))
            })?;
        let spec_index = retained.len();
        retained.push(
            PendingContainer::exact(
                ContainerKind::Residual(entry),
                component.blocks,
                graph_facts,
            )?
            .into_spec(),
        );
        component_dispositions[component_index] =
            Some(AggregateSeedDisposition::Residual(spec_index));
    }

    let mut seed_dispositions = vec![None; residuals.len()];
    for seed in residuals {
        let component = component_by_seed[seed.id.index()].ok_or_else(|| {
            StructureError::invalid(format!(
                "residual seed #{} has no normalized component",
                seed.id.index()
            ))
        })?;
        let disposition = component_dispositions[component].ok_or_else(|| {
            StructureError::invalid(format!(
                "residual component #{component} has no final disposition"
            ))
        })?;
        if seed_dispositions[seed.id.index()]
            .replace(disposition)
            .is_some()
        {
            return Err(StructureError::invalid(format!(
                "residual seed #{} has multiple final dispositions",
                seed.id.index()
            )));
        }
    }
    *specs = retained;
    Ok(AggregateSeedDispositions {
        residuals: seed_dispositions
            .into_iter()
            .enumerate()
            .map(|(index, disposition)| {
                disposition.ok_or_else(|| {
                    StructureError::invalid(format!(
                        "residual seed #{index} has no final disposition"
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?,
        islands,
    })
}

pub(super) fn validate_aggregate_seed_dispositions(
    cfg: &Cfg,
    input: &FinalPlanInput,
    residuals: &[ResidualSeed],
    specs: &[ContainerSpec],
    dispositions: &AggregateSeedDispositions,
) -> Result<(), StructureError> {
    if dispositions.residuals.len() != residuals.len() {
        return Err(StructureError::invalid(format!(
            "residual disposition arena has {} entries for {} seeds",
            dispositions.residuals.len(),
            residuals.len()
        )));
    }
    let mut used_residual_specs = vec![false; specs.len()];
    for seed in residuals {
        let disposition = dispositions.residuals[seed.id.index()];
        let spec_index = match disposition {
            AggregateSeedDisposition::Residual(index) => {
                if !matches!(
                    specs.get(index).map(|spec| spec.kind),
                    Some(ContainerKind::Residual(_))
                ) {
                    return Err(StructureError::invalid(format!(
                        "residual seed #{} references non-residual disposition #{index}",
                        seed.id.index()
                    )));
                }
                used_residual_specs[index] = true;
                index
            }
            AggregateSeedDisposition::Island(island) => dispositions
                .islands
                .get(island)
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "residual seed #{} references missing island #{island}",
                        seed.id.index()
                    ))
                })?,
        };
        let spec = &specs[spec_index];
        if !seed.blocks.is_subset(&spec.blocks) {
            return Err(StructureError::invalid(format!(
                "residual seed #{} is not contained by disposition #{spec_index}",
                seed.id.index()
            )));
        }
    }
    for (index, spec) in specs.iter().enumerate() {
        if matches!(spec.kind, ContainerKind::Residual(_)) && !used_residual_specs[index] {
            return Err(StructureError::invalid(format!(
                "residual disposition #{index} has no source seed"
            )));
        }
    }

    for (island, input_island) in input.unstructured.iter().enumerate() {
        let seed_blocks = input_island.layout.as_ref().map_or_else(
            || input_island.fact.blocks.clone(),
            |layout| layout.blocks.clone(),
        );
        let seed_blocks = reachable_nonempty_blocks(cfg, seed_blocks);
        let disposition = dispositions.islands.get(island).copied().flatten();
        if seed_blocks.is_empty() {
            if disposition.is_some() {
                return Err(StructureError::invalid(format!(
                    "unreachable island #{island} has a final disposition"
                )));
            }
            continue;
        }
        let spec_index = disposition.ok_or_else(|| {
            StructureError::invalid(format!(
                "reachable protected island #{island} has no final disposition"
            ))
        })?;
        let Some(spec) = specs.get(spec_index) else {
            return Err(StructureError::invalid(format!(
                "protected island #{island} references missing disposition #{spec_index}"
            )));
        };
        if !matches!(
            spec.kind,
            ContainerKind::Island(_) | ContainerKind::Residual(_)
        ) || !seed_blocks.is_subset(&spec.blocks)
        {
            return Err(StructureError::invalid(format!(
                "protected island #{island} is not contained by its flattened disposition"
            )));
        }
    }
    Ok(())
}

pub(super) fn branch_part(
    branch: &super::super::BranchPlanInput,
    input: &FinalPlanInput,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BranchPart> {
    if block == branch.branch.header
        || branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
            .is_some_and(|condition| condition.candidate.blocks.contains(&block))
    {
        return Some(BranchPart::Condition);
    }
    let (then_entry, else_entry) = branch_arm_entries(branch, input)?;
    let in_then = graph_facts.dominates(then_entry, block);
    let in_else = else_entry.is_some_and(|entry| graph_facts.dominates(entry, block));
    match (in_then, in_else) {
        (true, false) => Some(BranchPart::Then),
        (false, true) => Some(BranchPart::Else),
        (false, false) if else_entry.is_none() => Some(BranchPart::Then),
        (true, true) | (false, false) => None,
    }
}

pub(super) fn branch_arm_entries(
    branch: &super::super::BranchPlanInput,
    input: &FinalPlanInput,
) -> Option<(BlockRef, Option<BlockRef>)> {
    let Some(condition) = branch
        .condition
        .and_then(|id| input.conditions.get(id.index()))
    else {
        return Some((branch.branch.then_entry, branch.branch.else_entry));
    };
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
        return None;
    };
    let then_is_truthy = resolve_branch_then_polarity(
        &branch.branch,
        truthy,
        falsy,
        condition
            .candidate
            .blocks
            .contains(&branch.branch.then_entry),
        None,
    )?;
    let (then_entry, other_entry) = if then_is_truthy {
        (truthy, falsy)
    } else {
        (falsy, truthy)
    };
    Some((then_entry, branch.branch.else_entry.map(|_| other_entry)))
}

pub(super) fn branch_part_for_blocks(
    branch: &super::super::BranchPlanInput,
    input: &FinalPlanInput,
    graph_facts: &GraphFacts,
    blocks: &BTreeSet<BlockRef>,
) -> Option<BranchPart> {
    let mut parts = blocks
        .iter()
        .copied()
        .filter_map(|block| branch_part(branch, input, graph_facts, block));
    let first = parts.next()?;
    parts.all(|part| part == first).then_some(first)
}

pub(super) fn loop_part(
    partition: &LoopPartitions,
    block: BlockRef,
) -> Result<LoopPart, StructureError> {
    if partition.preheader == Some(block) {
        Ok(LoopPart::Preheader)
    } else if partition.control.contains(&block) {
        Ok(LoopPart::Control)
    } else if partition.body.contains(&block) {
        Ok(LoopPart::Body)
    } else if partition
        .normal_tail
        .as_ref()
        .is_some_and(|tail| tail.blocks.contains(&block))
    {
        Ok(LoopPart::NormalTail)
    } else {
        Err(StructureError::invalid(format!(
            "block {block} is outside its loop partitions"
        )))
    }
}

pub(super) fn loop_part_for_blocks(
    partition: &LoopPartitions,
    blocks: &BTreeSet<BlockRef>,
) -> Result<Option<LoopPart>, StructureError> {
    let mut parts = blocks
        .iter()
        .copied()
        .map(|block| loop_part(partition, block));
    let Some(first) = parts.next().transpose()? else {
        return Ok(None);
    };
    for part in parts {
        if part? != first {
            return Ok(None);
        }
    }
    Ok(Some(first))
}

pub(super) fn reserve(regions: &mut Vec<Option<RegionPlan>>) -> RegionId {
    let id = RegionId(regions.len());
    regions.push(None);
    id
}

pub(super) fn reserve_sequence(
    regions: &mut Vec<Option<RegionPlan>>,
    parent: RegionId,
) -> RegionId {
    let id = RegionId(regions.len());
    regions.push(Some(RegionPlan::Sequence {
        parent: Some(parent),
        children: Vec::new(),
    }));
    id
}

pub(super) fn attachment_for_container(
    parent: Option<usize>,
    child: &ContainerSpec,
    specs: &[ContainerSpec],
    slots: &[ContainerSlots],
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    graph_facts: &GraphFacts,
) -> Result<RegionId, StructureError> {
    let Some(parent) = parent else {
        return Ok(RegionId(0));
    };
    match (specs[parent].kind, slots[parent]) {
        (ContainerKind::SinglePass(_), ContainerSlots::SinglePass { region }) => Ok(region),
        (
            ContainerKind::Loop(id),
            ContainerSlots::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            },
        ) => match if child.blocks.is_empty() {
            Some(loop_part(&partitions[id.index()], child.representative)?)
        } else {
            loop_part_for_blocks(&partitions[id.index()], &child.blocks)?
        } {
            Some(LoopPart::Preheader) => preheader.ok_or_else(|| {
                StructureError::invalid("loop child requires a missing preheader region")
            }),
            Some(LoopPart::Control) => Ok(control),
            Some(LoopPart::Body) => Ok(body),
            Some(LoopPart::NormalTail) => normal_tail.ok_or_else(|| {
                StructureError::invalid("loop child requires a missing normal-tail region")
            }),
            None => Err(StructureError::invalid(format!(
                "child {:?} ranges {:?} cross loop #{} partitions: preheader={:?} control={:?} body={:?} normal_tail={:?}",
                child.kind,
                child.ranges,
                id.index(),
                partitions[id.index()].preheader,
                partitions[id.index()].control,
                partitions[id.index()].body,
                partitions[id.index()]
                    .normal_tail
                    .as_ref()
                    .map(|tail| &tail.blocks),
            ))),
        },
        (
            ContainerKind::Island(_) | ContainerKind::Residual(_),
            ContainerSlots::Island { region },
        ) => Ok(region),
        (
            ContainerKind::Branch(id),
            ContainerSlots::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            },
        ) => {
            let part = if child.blocks.is_empty() {
                branch_part(
                    &input.branches[id.index()],
                    input,
                    graph_facts,
                    child.representative,
                )
            } else {
                branch_part_for_blocks(
                    &input.branches[id.index()],
                    input,
                    graph_facts,
                    &child.blocks,
                )
            };
            match part {
                Some(BranchPart::Condition) => Ok(condition),
                Some(BranchPart::Then) => Ok(then_arm),
                Some(BranchPart::Else) => else_arm.ok_or_else(|| {
                    StructureError::invalid("branch child requires a missing else arm")
                }),
                None => Err(StructureError::invalid(format!(
                    "child {:?} ranges {:?} cross branch #{} arms: then=#{} else={:?} continuation={:?}",
                    child.kind,
                    child.ranges,
                    id.index(),
                    input.branches[id.index()].branch.then_entry.index(),
                    input.branches[id.index()]
                        .branch
                        .else_entry
                        .map(BlockRef::index),
                    input.branches[id.index()].branch.merge.map(BlockRef::index),
                ))),
            }
        }
        _ => Err(StructureError::invalid("container parent slot mismatch")),
    }
}

pub(super) fn attachment_for_block(
    owner: Option<usize>,
    block: BlockRef,
    specs: &[ContainerSpec],
    slots: &[ContainerSlots],
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    graph_facts: &GraphFacts,
) -> Result<RegionId, StructureError> {
    let Some(owner) = owner else {
        return Ok(RegionId(0));
    };
    match (specs[owner].kind, slots[owner]) {
        (ContainerKind::SinglePass(_), ContainerSlots::SinglePass { region }) => Ok(region),
        (
            ContainerKind::Loop(id),
            ContainerSlots::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            },
        ) => match loop_part(&partitions[id.index()], block)? {
            LoopPart::Preheader => preheader.ok_or_else(|| {
                StructureError::invalid("loop block requires a missing preheader region")
            }),
            LoopPart::Control => Ok(control),
            LoopPart::Body => Ok(body),
            LoopPart::NormalTail => normal_tail.ok_or_else(|| {
                StructureError::invalid("loop block requires a missing normal-tail region")
            }),
        },
        (
            ContainerKind::Branch(id),
            ContainerSlots::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            },
        ) => match branch_part(&input.branches[id.index()], input, graph_facts, block) {
            Some(BranchPart::Condition) => Ok(condition),
            Some(BranchPart::Then) => Ok(then_arm),
            Some(BranchPart::Else) => else_arm
                .ok_or_else(|| StructureError::invalid("branch block requires a missing else arm")),
            None => Err(StructureError::invalid(format!(
                "block {block} is not owned by one branch arm"
            ))),
        },
        (
            ContainerKind::Island(_) | ContainerKind::Residual(_),
            ContainerSlots::Island { region },
        ) => Ok(region),
        _ => Err(StructureError::invalid("block owner slot mismatch")),
    }
}

pub(super) fn append_region(
    parent: RegionId,
    child: RegionId,
    rank: usize,
    island_regions: &[bool],
    sequences: &mut [Vec<(usize, RegionId)>],
    islands: &mut [Vec<(usize, UnstructuredLayoutItem)>],
) -> Result<(), StructureError> {
    if island_regions.get(parent.index()).copied().unwrap_or(false) {
        islands[parent.index()].push((rank, UnstructuredLayoutItem::Region(child)));
    } else {
        let sequence = sequences.get_mut(parent.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "missing sequence parent region #{}",
                parent.index()
            ))
        })?;
        sequence.push((rank, child));
    }
    Ok(())
}
