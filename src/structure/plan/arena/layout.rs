//! region layout edge、label 与方言 requirement 的冻结。输入 containment/navigation 与 edge plans，输出自然布局事实、label placement 和 required features；不负责 edge 语义分类。例如跨 island 的非自然边会要求显式 goto label。

use super::*;

#[derive(Debug, Clone, Copy, Default)]
pub(in crate::structure::plan) struct LayoutEdgeFact {
    pub(in crate::structure::plan) natural: bool,
    pub(in crate::structure::plan) crosses_island_layout: bool,
}

pub(in crate::structure::plan) fn layout_edge_facts(
    cfg: &Cfg,
    regions: &[RegionPlan],
    navigation: &RegionNavigation,
) -> Result<Vec<LayoutEdgeFact>, StructureError> {
    let mut sequence_positions = vec![None; regions.len()];
    let mut island_block_positions = vec![None; cfg.blocks.len()];
    let mut island_region_positions = vec![None; regions.len()];
    for (index, region) in regions.iter().enumerate() {
        match region {
            RegionPlan::Sequence { children, .. } => {
                for (position, child) in children.iter().copied().enumerate() {
                    sequence_positions[child.index()] = Some((RegionId(index), position));
                }
            }
            RegionPlan::Unstructured { layout, .. } => {
                for (position, item) in layout.iter().enumerate() {
                    match item {
                        UnstructuredLayoutItem::Block(block) => {
                            island_block_positions[block.index()] =
                                Some((RegionId(index), position));
                        }
                        UnstructuredLayoutItem::Region(region) => {
                            island_region_positions[region.index()] =
                                Some((RegionId(index), position));
                        }
                    }
                }
            }
            RegionPlan::Block { .. }
            | RegionPlan::Branch { .. }
            | RegionPlan::ValueDecision { .. }
            | RegionPlan::Loop { .. } => {}
        }
    }

    Ok(cfg
        .edges
        .iter()
        .enumerate()
        .map(|(edge_index, edge)| {
            let Some(relation) = navigation.edge_relation(EdgeRef(edge_index)) else {
                return LayoutEdgeFact::default();
            };
            let Some(source) = relation.source_owner else {
                return LayoutEdgeFact::default();
            };
            let Some(target) = relation.target_owner else {
                return LayoutEdgeFact::default();
            };
            let Some(owner) = relation.lca else {
                return LayoutEdgeFact::default();
            };
            match &regions[owner.index()] {
                RegionPlan::Sequence { .. } => {
                    let source_owner = source;
                    let Some(source) = relation.source_child else {
                        return LayoutEdgeFact::default();
                    };
                    let Some(target) = relation.target_child else {
                        return LayoutEdgeFact::default();
                    };
                    let natural = sequence_positions[source.index()]
                        .zip(sequence_positions[target.index()])
                        .is_some_and(|((source_parent, source), (target_parent, target))| {
                            source_parent == owner && target_parent == owner && target == source + 1
                        })
                        && navigation.region_can_complete_from(source, source_owner, edge.from);
                    LayoutEdgeFact {
                        natural,
                        crosses_island_layout: matches!(
                            regions.get(source.index()),
                            Some(RegionPlan::Unstructured { .. })
                        ),
                    }
                }
                RegionPlan::Unstructured { .. } => {
                    let source_owner = source;
                    let source_region = if source_owner == owner {
                        None
                    } else {
                        relation.source_child
                    };
                    let source = if source_owner == owner {
                        island_block_positions[edge.from.index()]
                            .filter(|(island, _)| *island == owner)
                            .map(|(_, position)| position)
                    } else {
                        source_region.and_then(|region| {
                            island_region_positions[region.index()]
                                .filter(|(island, _)| *island == owner)
                                .map(|(_, position)| position)
                        })
                    };
                    let target = if target == owner {
                        island_block_positions[edge.to.index()]
                            .filter(|(island, _)| *island == owner)
                            .map(|(_, position)| position)
                    } else {
                        relation.target_child.and_then(|region| {
                            island_region_positions[region.index()]
                                .filter(|(island, _)| *island == owner)
                                .map(|(_, position)| position)
                        })
                    };
                    let crosses_island_layout = source
                        .zip(target)
                        .is_some_and(|(source, target)| source != target);
                    let natural = source
                        .zip(target)
                        .is_some_and(|(source, target)| target == source + 1)
                        && source_region.is_none_or(|region| {
                            navigation.region_can_complete_from(region, source_owner, edge.from)
                        });
                    LayoutEdgeFact {
                        natural,
                        crosses_island_layout,
                    }
                }
                RegionPlan::Block { .. }
                | RegionPlan::Branch { .. }
                | RegionPlan::ValueDecision { .. }
                | RegionPlan::Loop { .. } => LayoutEdgeFact::default(),
            }
        })
        .collect())
}

pub(super) fn freeze_labels(
    cfg: &Cfg,
    arena: &RegionArena,
    edge_plans: &mut [EdgePlan],
    tbc_flow: &crate::structure::scope::TbcFlowFacts,
) -> Result<(Vec<LabelPlan>, Vec<Option<LabelPlanId>>), StructureError> {
    let label_region_by_block = label_regions_by_entry(
        cfg,
        &arena.regions,
        &arena.navigation,
        &arena.single_passes,
        &arena.single_pass_by_region,
    )?;
    let mut targets = BTreeMap::<BlockRef, LabelPlacement>::new();
    for edge_plan in edge_plans.iter() {
        let EdgeTransfer::Goto(label, _) = edge_plan.transfer else {
            continue;
        };
        // classify 阶段临时以 block index 承载尚未冻结的 label identity。
        let block = BlockRef(label.index());
        record_label_target(
            &mut targets,
            block,
            label_placement_for_edge(cfg, &label_region_by_block, edge_plan.edge, block)?,
        )?;
    }
    let multi_entry_prefix = arena.navigation.multi_entry_island_prefix(&arena.regions);
    for (index, edge) in cfg.edges.iter().enumerate() {
        if arena
            .navigation
            .edge_enters_prefixed_region(EdgeRef(index), &multi_entry_prefix)
        {
            record_label_target(
                &mut targets,
                edge.to,
                label_placement_for_edge(cfg, &label_region_by_block, EdgeRef(index), edge.to)?,
            )?;
        }
    }

    let mut labels = Vec::with_capacity(targets.len());
    let mut label_by_block = vec![None; cfg.blocks.len()];
    for block in cfg.block_order.iter().copied() {
        let Some(placement) = targets.remove(&block) else {
            continue;
        };
        let id = LabelPlanId(labels.len());
        label_by_block[block.index()] = Some(id);
        labels.push(LabelPlan {
            block,
            tbc_barriers: tbc_flow
                .active_at_entry(block)
                .ok_or_else(|| StructureError::invalid("label block has no TBC entry facts"))?
                .iter()
                .copied()
                .collect(),
            placement,
        });
    }
    if !targets.is_empty() {
        return Err(StructureError::invalid(
            "planned label target is absent from stable block order",
        ));
    }

    for edge_plan in edge_plans {
        let EdgeTransfer::Goto(pending, reason) = edge_plan.transfer else {
            continue;
        };
        let target = BlockRef(pending.index());
        let label = label_by_block
            .get(target.index())
            .copied()
            .flatten()
            .ok_or_else(|| StructureError::invalid("goto target has no frozen label"))?;
        edge_plan.transfer = EdgeTransfer::Goto(label, reason);
    }

    Ok((labels, label_by_block))
}

pub(super) fn record_label_target(
    targets: &mut BTreeMap<BlockRef, LabelPlacement>,
    block: BlockRef,
    placement: LabelPlacement,
) -> Result<(), StructureError> {
    if let Some(existing) = targets.insert(block, placement)
        && existing != placement
    {
        return Err(StructureError::invalid(format!(
            "label target {block} requires conflicting placements {existing:?} and {placement:?}"
        )));
    }
    Ok(())
}

pub(super) fn label_placement_for_edge(
    cfg: &Cfg,
    label_region_by_block: &[Option<RegionId>],
    edge: EdgeRef,
    target: BlockRef,
) -> Result<LabelPlacement, StructureError> {
    if cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(target) {
        return Err(StructureError::invalid(format!(
            "label edge {edge} does not enter target {target}"
        )));
    }
    Ok(label_region_by_block
        .get(target.index())
        .copied()
        .flatten()
        .map_or(LabelPlacement::BeforeBlock, LabelPlacement::BeforeRegion))
}

/// 同一 CFG target 只能对应一个源码 label，所以 placement 也必须按 target 冻结。
/// 若多个嵌套 region 共享入口，选择最外层会生成源码控制壳的 region；从其内部或
/// 外部进入该 block 都会先执行同一份 region 语义，且 label 不会被藏进 `if`、loop
/// 或 single-pass `repeat` 的更深词法块。
pub(super) fn label_regions_by_entry(
    cfg: &Cfg,
    regions: &[RegionPlan],
    navigation: &RegionNavigation,
    single_passes: &[super::super::SinglePassPlan],
    single_pass_by_region: &[Option<super::super::SinglePassPlanId>],
) -> Result<Vec<Option<RegionId>>, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    for (index, node) in regions.iter().enumerate() {
        let region = RegionId(index);
        let entry = match node {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => *entry,
            RegionPlan::Sequence { .. } => {
                let Some(id) = single_pass_by_region.get(index).copied().flatten() else {
                    continue;
                };
                single_passes
                    .get(id.index())
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "single-pass label placement references a missing payload",
                        )
                    })?
                    .entry
            }
            // island layout 直接内联到父层，不会生成独立的源码词法壳；把它当
            // `BeforeRegion` 会把入口 label 错移到 layout 首项之前。
            RegionPlan::Block { .. } | RegionPlan::Unstructured { .. } => continue,
        };
        let slot = by_block.get_mut(entry.index()).ok_or_else(|| {
            StructureError::invalid("structured label entry is outside the CFG arena")
        })?;
        match *slot {
            None => *slot = Some(region),
            Some(outer) if navigation.contains(outer, region) => {}
            Some(inner) if navigation.contains(region, inner) => *slot = Some(region),
            Some(other) => {
                return Err(StructureError::invalid(format!(
                    "block {entry} is the entry of incomparable structured regions #{} and #{}",
                    other.index(),
                    region.index()
                )));
            }
        }
    }
    Ok(by_block)
}

pub(super) fn build_requirements(
    cfg: &Cfg,
    caps: ControlFlowCaps,
    arena: &RegionArena,
    edge_plans: &[EdgePlan],
) -> Result<PlanRequirements, StructureError> {
    let mut entries = Vec::new();
    let mut by_edge = vec![Vec::new(); cfg.edges.len()];
    let mut required_features = BTreeSet::new();
    let mut unavailable_features = BTreeSet::new();

    for edge_plan in edge_plans.iter() {
        let requirement = match edge_plan.transfer {
            EdgeTransfer::Goto(label, reason) => {
                required_features.insert(ControlFlowFeature::GotoLabel);
                if !caps.goto_label {
                    unavailable_features.insert(ControlFlowFeature::GotoLabel);
                }
                Some(PlanRequirement::Goto {
                    edge: edge_plan.edge,
                    label,
                    reason,
                })
            }
            EdgeTransfer::Continue(loop_region) => {
                required_features.insert(ControlFlowFeature::ContinueStatement);
                if !caps.continue_stmt {
                    unavailable_features.insert(ControlFlowFeature::ContinueStatement);
                }
                Some(PlanRequirement::Continue {
                    edge: edge_plan.edge,
                    loop_region,
                })
            }
            EdgeTransfer::Unreachable
            | EdgeTransfer::Fallthrough
            | EdgeTransfer::BranchArm(_)
            | EdgeTransfer::LoopBack(_)
            | EdgeTransfer::Break(_)
            | EdgeTransfer::Return
            | EdgeTransfer::TailCall => None,
        };
        if let Some(requirement) = requirement {
            let id = PlanRequirementId(entries.len());
            entries.push(requirement);
            by_edge[edge_plan.edge.index()].push(id);
        }
    }
    for (index, spec) in arena.specs.iter().enumerate() {
        if !matches!(
            spec.kind,
            ContainerKind::Island(_) | ContainerKind::Residual(_)
        ) {
            continue;
        }
        let region = arena.slots[index].region();
        let entry_count = match &arena.regions[region.index()] {
            RegionPlan::Unstructured { entries, .. } => entries.len(),
            _ => return Err(StructureError::invalid("island slot is not unstructured")),
        };
        if entry_count > 1 {
            required_features.insert(ControlFlowFeature::GotoLabel);
            if !caps.goto_label {
                unavailable_features.insert(ControlFlowFeature::GotoLabel);
            }
            entries.push(PlanRequirement::MultiEntryIsland {
                region,
                entry_count,
            });
        }
    }

    Ok(PlanRequirements {
        entries,
        by_edge,
        unresolved_by_block: vec![false; cfg.blocks.len()],
        required_features,
        unavailable_features,
        caps,
    })
}
