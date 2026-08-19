//! container 拓扑排序与同尺寸冲突消解。输入候选集合和 preorder ranges，输出父子拓扑；不负责物化 RegionPlan。例如同块 value decision 与 branch 会按语义优先级形成唯一 owner。

use super::*;

pub(super) fn block_ranks(cfg: &Cfg) -> Vec<usize> {
    let mut ranks = vec![usize::MAX; cfg.blocks.len()];
    for (rank, block) in cfg.block_order.iter().copied().enumerate() {
        ranks[block.index()] = rank;
    }
    ranks
}

pub(super) fn container_same_size_rank(kind: ContainerKind) -> u8 {
    match kind {
        ContainerKind::ValueDecision(_) => 0,
        ContainerKind::Branch(_) => 1,
        ContainerKind::SinglePass(_) => 2,
        ContainerKind::Loop(_) => 3,
        ContainerKind::Island(_) | ContainerKind::Residual(_) => 4,
    }
}

pub(super) fn build_container_topology(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    specs: &mut [ContainerSpec],
) -> Result<Vec<Option<usize>>, StructureError> {
    let mut order = (0..specs.len()).collect::<Vec<_>>();
    order.sort_by_key(|index| {
        let spec = &specs[*index];
        (
            Reverse(spec.block_count),
            Reverse(container_same_size_rank(spec.kind)),
            *index,
        )
    });

    let mut owners = RangeOwnerTree::new(graph_facts.dominator_tree.order.len());
    for index in order {
        let RangeOwnerState::Uniform(parent) = owners.uniform_owner(&specs[index].ranges)? else {
            return Err(StructureError::invalid(format!(
                "container #{index} is not laminar at block {}",
                specs[index].representative
            )));
        };
        specs[index].parent = parent;
        owners.assign(&specs[index].ranges, index)?;
    }
    let preorder_owners = owners.materialize()?;
    let mut owner_by_block = vec![None; cfg.blocks.len()];
    for (position, owner) in preorder_owners.into_iter().enumerate() {
        let block = graph_facts
            .dominator_tree
            .order
            .get(position)
            .copied()
            .ok_or_else(|| {
                StructureError::invalid("owner projection exceeds dominator preorder")
            })?;
        let slot = owner_by_block.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("dominator preorder references a missing CFG block")
        })?;
        *slot = owner;
    }

    let parent_by_spec = specs.iter().map(|spec| spec.parent).collect::<Vec<_>>();
    let mut children = vec![Vec::new(); specs.len()];
    for (index, parent) in parent_by_spec.iter().copied().enumerate() {
        if let Some(parent) = parent {
            children
                .get_mut(parent)
                .ok_or_else(|| {
                    StructureError::invalid("container parent is outside the spec arena")
                })?
                .push(index);
        }
    }
    let mut visited = vec![false; specs.len()];
    let roots = parent_by_spec
        .iter()
        .enumerate()
        .filter_map(|(index, parent)| parent.is_none().then_some(index))
        .collect::<Vec<_>>();
    let mut pending = roots;
    let mut traversal = Vec::with_capacity(specs.len());
    while let Some(parent) = pending.pop() {
        if std::mem::replace(&mut visited[parent], true) {
            return Err(StructureError::invalid(
                "container containment contains a cycle",
            ));
        }
        traversal.push(parent);
        for &child in &children[parent] {
            pending.push(child);
        }
    }
    if let Some(index) = visited.iter().position(|visited| !visited) {
        return Err(StructureError::invalid(format!(
            "container #{index} is disconnected from the containment forest"
        )));
    }

    let rank = block_ranks(cfg);
    for (block_index, owner) in owner_by_block.iter().copied().enumerate() {
        let Some(owner) = owner else {
            continue;
        };
        specs[owner].first_rank = specs[owner].first_rank.min(rank[block_index]);
    }
    for child in traversal.into_iter().rev() {
        let first_rank = specs[child].first_rank;
        if let Some(parent) = specs[child].parent {
            specs[parent].first_rank = specs[parent].first_rank.min(first_rank);
        }
    }
    if let Some(index) = specs.iter().position(|spec| spec.first_rank == usize::MAX) {
        return Err(StructureError::invalid(format!(
            "container #{index} has no ranked CFG block"
        )));
    }
    Ok(owner_by_block)
}

pub(super) fn flatten_nested_unstructured_specs(
    specs: &mut Vec<ContainerSpec>,
    owner_by_block: &mut [Option<usize>],
    dispositions: &mut AggregateSeedDispositions,
) -> Result<(), StructureError> {
    let is_unstructured =
        |kind| matches!(kind, ContainerKind::Island(_) | ContainerKind::Residual(_));
    let mut children = vec![Vec::new(); specs.len()];
    let mut roots = Vec::new();
    for (index, spec) in specs.iter().enumerate() {
        if let Some(parent) = spec.parent {
            let Some(parent_children) = children.get_mut(parent) else {
                return Err(StructureError::invalid(
                    "container parent is outside the spec arena while flattening islands",
                ));
            };
            parent_children.push(index);
        } else {
            roots.push(index);
        }
    }

    let mut removed = vec![false; specs.len()];
    let mut top_unstructured = vec![None; specs.len()];
    let mut pending = roots
        .iter()
        .rev()
        .copied()
        .map(|root| (root, None))
        .collect::<Vec<_>>();
    while let Some((index, inherited)) = pending.pop() {
        let current = if is_unstructured(specs[index].kind) {
            if let Some(outer) = inherited {
                removed[index] = true;
                Some(outer)
            } else {
                Some(index)
            }
        } else {
            inherited
        };
        top_unstructured[index] = current;
        for child in children[index].iter().rev().copied() {
            pending.push((child, current));
        }
    }
    if !removed.iter().any(|removed| *removed) {
        return Ok(());
    }

    let mut nearest_retained = vec![None; specs.len()];
    let mut pending = roots
        .iter()
        .rev()
        .copied()
        .map(|root| (root, None))
        .collect::<Vec<_>>();
    while let Some((index, inherited)) = pending.pop() {
        let current = if removed[index] {
            inherited
        } else {
            Some(index)
        };
        nearest_retained[index] = current;
        for child in children[index].iter().rev().copied() {
            pending.push((child, current));
        }
    }

    let mut new_index = vec![None; specs.len()];
    let mut retained_count = 0usize;
    for (index, removed) in removed.iter().copied().enumerate() {
        if removed {
            continue;
        }
        new_index[index] = Some(retained_count);
        retained_count = retained_count
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("flattened spec count overflowed"))?;
    }
    let flattened_target = |old: usize| -> Result<usize, StructureError> {
        if !removed.get(old).copied().ok_or_else(|| {
            StructureError::invalid("aggregate disposition references a missing spec")
        })? {
            return Ok(old);
        }
        top_unstructured[old].ok_or_else(|| {
            StructureError::invalid("nested island has no retained unstructured ancestor")
        })
    };
    let disposition_for = |old: usize| -> Result<AggregateSeedDisposition, StructureError> {
        let target = flattened_target(old)?;
        let index = new_index[target].ok_or_else(|| {
            StructureError::invalid("flattened aggregate target has no new spec index")
        })?;
        match specs[target].kind {
            ContainerKind::Island(island) => Ok(AggregateSeedDisposition::Island(island)),
            ContainerKind::Residual(_) => Ok(AggregateSeedDisposition::Residual(index)),
            _ => Err(StructureError::invalid(
                "flattened aggregate target is not unstructured",
            )),
        }
    };

    let old_islands = dispositions.islands.clone();
    for disposition in &mut dispositions.residuals {
        let old = match *disposition {
            AggregateSeedDisposition::Residual(index) => index,
            AggregateSeedDisposition::Island(island) => {
                old_islands.get(island).copied().flatten().ok_or_else(|| {
                    StructureError::invalid(
                        "residual seed references a missing island while flattening",
                    )
                })?
            }
        };
        *disposition = disposition_for(old)?;
    }
    for disposition in &mut dispositions.islands {
        let Some(old) = *disposition else {
            continue;
        };
        let target = flattened_target(old)?;
        *disposition = Some(new_index[target].ok_or_else(|| {
            StructureError::invalid("flattened island target has no new spec index")
        })?);
    }

    for owner in owner_by_block {
        let Some(old) = *owner else {
            continue;
        };
        let retained = nearest_retained[old].ok_or_else(|| {
            StructureError::invalid("nested island block has no retained container owner")
        })?;
        *owner = Some(new_index[retained].ok_or_else(|| {
            StructureError::invalid("retained block owner has no new spec index")
        })?);
    }

    let old_specs = std::mem::take(specs);
    let mut retained = Vec::with_capacity(retained_count);
    for (old, mut spec) in old_specs.into_iter().enumerate() {
        if removed[old] {
            continue;
        }
        spec.parent = spec
            .parent
            .and_then(|parent| nearest_retained[parent])
            .map(|parent| {
                new_index[parent]
                    .ok_or_else(|| StructureError::invalid("retained parent has no new spec index"))
            })
            .transpose()?;
        retained.push(spec);
    }
    *specs = retained;
    Ok(())
}
