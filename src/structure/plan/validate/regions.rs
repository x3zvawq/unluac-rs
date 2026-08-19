//! 校验区域包含关系、块覆盖与入口约束；依赖冻结后的区域树和导航索引，不负责构造区域；例如确保每个可达块只被一个叶区域拥有。

use super::*;

pub(super) fn validate_containment(plan: &StructurePlan) -> Result<(), StructureError> {
    let mut references = vec![0usize; plan.regions.len()];
    let mut children = vec![Vec::new(); plan.regions.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let owner = RegionId(index);
        if let RegionPlan::Unstructured { layout, .. } = region {
            for child in layout.iter().filter_map(|item| match item {
                UnstructuredLayoutItem::Region(child) => Some(*child),
                UnstructuredLayoutItem::Block(_) => None,
            }) {
                if matches!(
                    plan.regions.get(child.index()),
                    Some(RegionPlan::Unstructured { .. })
                ) {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} directly contains island child #{}",
                        child.index()
                    )));
                }
            }
        }
        let owned = match region {
            RegionPlan::Block { .. } => Vec::new(),
            RegionPlan::Sequence { children, .. } => children.clone(),
            RegionPlan::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            } => [Some(*condition), Some(*then_arm), *else_arm]
                .into_iter()
                .flatten()
                .collect(),
            RegionPlan::ValueDecision { .. } => Vec::new(),
            RegionPlan::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            } => [*preheader, Some(*control), Some(*body), *normal_tail]
                .into_iter()
                .flatten()
                .collect(),
            RegionPlan::Unstructured { layout, .. } => layout
                .iter()
                .filter_map(|item| match item {
                    UnstructuredLayoutItem::Region(region) => Some(*region),
                    UnstructuredLayoutItem::Block(_) => None,
                })
                .collect(),
        };
        for child in owned {
            let Some(child_plan) = plan.regions.get(child.index()) else {
                return Err(StructureError::invalid(format!(
                    "region {owner:?} references missing child {child:?}"
                )));
            };
            if child_plan.parent() != Some(owner) {
                return Err(StructureError::invalid(format!(
                    "region {child:?} parent disagrees with owner {owner:?}"
                )));
            }
            references[child.index()] += 1;
            children[index].push(child);
        }
    }
    for (index, count) in references.into_iter().enumerate() {
        let expected = usize::from(index != plan.root.index());
        if count != expected {
            return Err(StructureError::invalid(format!(
                "region #{index} has {count} containment references; expected {expected}"
            )));
        }
    }
    let mut pending = vec![(plan.root, false)];
    while let Some((region, inside_island)) = pending.pop() {
        let is_island = matches!(
            plan.regions.get(region.index()),
            Some(RegionPlan::Unstructured { .. })
        );
        if inside_island && is_island {
            return Err(StructureError::invalid(format!(
                "unstructured region #{} is nested inside another island",
                region.index()
            )));
        }
        pending.extend(
            children[region.index()]
                .iter()
                .copied()
                .map(|child| (child, inside_island || is_island)),
        );
    }
    Ok(())
}

pub(super) struct RegionBlockStats {
    subtree_counts: Vec<usize>,
}

impl RegionBlockStats {
    pub(super) fn new(
        plan: &StructurePlan,
        intervals: &RegionNavigation,
    ) -> Result<Self, StructureError> {
        let mut subtree_counts = vec![0usize; plan.regions.len()];
        for owner in plan.region_by_block.iter().copied().flatten() {
            *subtree_counts.get_mut(owner.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "block owner references missing region {:?} while building validation stats",
                    owner
                ))
            })? += 1;
        }
        for region in &intervals.postorder {
            if let Some(parent) = intervals.parent[region.index()] {
                subtree_counts[parent.index()] += subtree_counts[region.index()];
            }
        }
        Ok(Self { subtree_counts })
    }

    pub(super) fn subtree_count(&self, region: RegionId) -> usize {
        self.subtree_counts[region.index()]
    }
}

pub(super) fn region_contains_block(
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    region: RegionId,
    block: BlockRef,
) -> bool {
    plan.region_for_block(block)
        .is_some_and(|owner| intervals.contains(region, owner))
}

pub(super) fn region_matches_exact_blocks<I>(
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    stats: &RegionBlockStats,
    region: RegionId,
    expected_len: usize,
    expected_blocks: I,
) -> bool
where
    I: IntoIterator<Item = BlockRef>,
{
    stats.subtree_count(region) == expected_len
        && expected_blocks
            .into_iter()
            .all(|block| region_contains_block(plan, intervals, region, block))
}

pub(super) fn validate_block_coverage(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let mut claims = vec![None; cfg.blocks.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let owner = RegionId(index);
        let blocks = match region {
            RegionPlan::Block { block, .. } => vec![*block],
            RegionPlan::Unstructured { layout, .. } => layout
                .iter()
                .filter_map(|item| match item {
                    UnstructuredLayoutItem::Block(block) => Some(*block),
                    UnstructuredLayoutItem::Region(_) => None,
                })
                .collect(),
            RegionPlan::ValueDecision { plan: decision, .. } => plan
                .value_decision(*decision)
                .map(|decision| decision.blocks().collect())
                .unwrap_or_default(),
            RegionPlan::Sequence { .. } | RegionPlan::Branch { .. } | RegionPlan::Loop { .. } => {
                Vec::new()
            }
        };
        for block in blocks {
            let Some(slot) = claims.get_mut(block.index()) else {
                return Err(StructureError::invalid(format!(
                    "region {owner:?} claims missing block {block}"
                )));
            };
            if slot.replace(owner).is_some() {
                return Err(StructureError::invalid(format!(
                    "block {block} is claimed by multiple regions"
                )));
            }
        }
    }
    for block in &cfg.block_order {
        let expected = cfg.reachable_blocks.contains(block);
        if claims[block.index()].is_some() != expected {
            return Err(StructureError::invalid(format!(
                "block {block} coverage disagrees with reachability"
            )));
        }
        if plan.region_by_block[block.index()] != claims[block.index()] {
            return Err(StructureError::invalid(format!(
                "block {block} owner index disagrees with arena claim"
            )));
        }
    }
    Ok(())
}

pub(super) fn validate_region_entries(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    let expected_island_ports = intervals.collect_island_ports(cfg, &plan.regions)?;
    for (index, region) in plan.regions.iter().enumerate() {
        let region_id = RegionId(index);
        let boundary = intervals.boundary(region_id).ok_or_else(|| {
            StructureError::invalid(format!("region #{index} has no boundary summary"))
        })?;
        match region {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => {
                let through_entry = cfg.preds[entry.index()]
                    .iter()
                    .filter(|edge| {
                        let source = cfg.edges[edge.index()].from;
                        cfg.reachable_blocks.contains(&source)
                            && plan
                                .region_for_block(source)
                                .is_some_and(|owner| !intervals.contains(region_id, owner))
                    })
                    .count();
                if boundary.entry_count != through_entry {
                    return Err(StructureError::invalid(format!(
                        "structured region #{index} has a non-entry incoming edge"
                    )));
                }
            }
            RegionPlan::Unstructured {
                entry,
                entries,
                exits,
                ..
            } => {
                if !region_contains_block(plan, intervals, region_id, *entry) {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} entry block is outside its containment"
                    )));
                }
                let expected_entries = &expected_island_ports.entries[index];
                let expected_exits = &expected_island_ports.exits[index];
                if entries != expected_entries || exits != expected_exits {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} has stale or unordered boundary ports: entries={entries:?}, expected={expected_entries:?}, exits={exits:?}, expected={expected_exits:?}"
                    )));
                }
                if boundary.entry_count != entries.len() || boundary.exit_count != exits.len() {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} boundary summary disagrees with its ports"
                    )));
                }
            }
            RegionPlan::Block { .. } | RegionPlan::Sequence { .. } => {}
        }
    }
    Ok(())
}
