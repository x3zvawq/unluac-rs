//! loop containment 与控制目标的稠密查询索引。输入最终 RegionArena 和 LoopPartitions，输出 block/edge 到最内层 loop、break/continue owner 及传播 break 的映射；不负责修改候选。例如 edge 分类可 O(1) 判断 source 是否离开最内层 loop。

use super::*;

pub(super) struct LoopQueryIndex {
    pub(super) innermost_by_block: Vec<Option<RegionId>>,
    pub(super) control_by_block: Vec<Option<RegionId>>,
    pub(super) loop_parent: Vec<Option<RegionId>>,
    pub(super) spec_by_region: Vec<Option<usize>>,
    pub(super) continuation: Vec<Option<BlockRef>>,
    pub(super) normal_tail_entry: Vec<Option<BlockRef>>,
    pub(super) break_owner_by_edge: Vec<Option<RegionId>>,
    pub(super) continue_owner_by_edge: Vec<Option<RegionId>>,
    pub(super) leaves_innermost_loop: Vec<bool>,
    pub(super) propagated_break_by_region: Vec<Option<RegionId>>,
    pub(super) propagated_break_target_by_region: Vec<Option<RegionId>>,
}

impl LoopQueryIndex {
    pub(super) fn build(
        cfg: &Cfg,
        arena: &RegionArena,
        input: &FinalPlanInput,
        partitions: &[LoopPartitions],
        layout_edges: &[LayoutEdgeFact],
    ) -> Result<Self, StructureError> {
        let region_count = arena.regions.len();
        let mut spec_by_region = vec![None; region_count];
        let mut continuation = vec![None; region_count];
        let mut continue_target = vec![None; region_count];
        let mut normal_tail_entry = vec![None; region_count];
        let mut control_marker = vec![None; region_count];
        for (spec_index, spec) in arena.specs.iter().enumerate() {
            let ContainerKind::Loop(id) = spec.kind else {
                continue;
            };
            let region = arena.slots[spec_index].region();
            let loop_ = input
                .loops
                .get(id.index())
                .ok_or_else(|| StructureError::invalid("loop query references missing evidence"))?;
            let partition = partitions.get(id.index()).ok_or_else(|| {
                StructureError::invalid("loop query references missing partition")
            })?;
            spec_by_region[region.index()] = Some(spec_index);
            continuation[region.index()] = partition.continuation;
            continue_target[region.index()] = loop_.candidate.continue_target;
            normal_tail_entry[region.index()] = partition
                .normal_tail
                .as_ref()
                .map(|tail| tail.contract.entry);
            let Some(RegionPlan::Loop {
                preheader, control, ..
            }) = arena.regions.get(region.index())
            else {
                return Err(StructureError::invalid("loop query region is not a loop"));
            };
            control_marker[control.index()] = Some(region);
            if let Some(preheader) = preheader {
                control_marker[preheader.index()] = Some(region);
            }
        }

        let mut nearest_by_region = vec![None; region_count];
        let mut control_by_region = vec![None; region_count];
        let mut loop_parent = vec![None; region_count];
        for region in &arena.navigation.preorder {
            let inherited_loop = arena.navigation.parent[region.index()]
                .and_then(|parent| nearest_by_region[parent.index()]);
            let inherited_control = arena.navigation.parent[region.index()]
                .and_then(|parent| control_by_region[parent.index()]);
            if spec_by_region[region.index()].is_some() {
                loop_parent[region.index()] = inherited_loop;
                nearest_by_region[region.index()] = Some(*region);
            } else {
                nearest_by_region[region.index()] = inherited_loop;
            }
            control_by_region[region.index()] =
                control_marker[region.index()].or(inherited_control);
        }

        let mut blocks_by_owner = vec![Vec::new(); region_count];
        let mut innermost_by_block = vec![None; cfg.blocks.len()];
        let mut control_by_block = vec![None; cfg.blocks.len()];
        for (index, owner) in arena.region_by_block.iter().copied().enumerate() {
            let Some(owner) = owner else { continue };
            let block = BlockRef(index);
            blocks_by_owner[owner.index()].push(block);
            innermost_by_block[index] = nearest_by_region[owner.index()];
            control_by_block[index] = control_by_region[owner.index()];
        }

        #[derive(Clone, Copy)]
        struct ActiveLoopTargets {
            end: usize,
            break_target: Option<(BlockRef, Option<RegionId>)>,
            continue_target: Option<(BlockRef, Option<RegionId>)>,
        }
        let mut active_break = vec![None; cfg.blocks.len()];
        let mut active_continue = vec![None; cfg.blocks.len()];
        let mut active = Vec::<ActiveLoopTargets>::new();
        let mut break_owner_by_edge = vec![None; cfg.edges.len()];
        let mut continue_owner_by_edge = vec![None; cfg.edges.len()];
        for (position, region) in arena.navigation.preorder.iter().copied().enumerate() {
            while active.last().is_some_and(|frame| frame.end <= position) {
                let frame = active.pop().ok_or_else(|| {
                    StructureError::invalid("loop query active stack underflowed")
                })?;
                if let Some((target, previous)) = frame.break_target {
                    active_break[target.index()] = previous;
                }
                if let Some((target, previous)) = frame.continue_target {
                    active_continue[target.index()] = previous;
                }
            }
            if spec_by_region[region.index()].is_some() {
                let break_target = continuation[region.index()].map(|target| {
                    let previous = active_break[target.index()];
                    active_break[target.index()] = previous.or(Some(region));
                    (target, previous)
                });
                let continue_target = continue_target[region.index()].map(|target| {
                    let previous = active_continue[target.index()];
                    active_continue[target.index()] = Some(region);
                    (target, previous)
                });
                active.push(ActiveLoopTargets {
                    end: arena.navigation.subtree_end[region.index()],
                    break_target,
                    continue_target,
                });
            }
            for block in &blocks_by_owner[region.index()] {
                for edge in &cfg.succs[block.index()] {
                    let target = cfg.edges[edge.index()].to;
                    break_owner_by_edge[edge.index()] = active_break[target.index()];
                    continue_owner_by_edge[edge.index()] = active_continue[target.index()];
                }
            }
        }

        let mut leaves_innermost_loop = vec![false; cfg.edges.len()];
        for (index, edge) in cfg.edges.iter().enumerate() {
            let Some(loop_region) = innermost_by_block[edge.from.index()] else {
                continue;
            };
            leaves_innermost_loop[index] = arena
                .region_by_block
                .get(edge.to.index())
                .copied()
                .flatten()
                .is_none_or(|target| !arena.navigation.contains(loop_region, target));
        }

        let mut propagated_break_by_region = vec![None; region_count];
        for (region_index, spec) in spec_by_region.iter().copied().enumerate() {
            let Some(spec) = spec else { continue };
            let region = RegionId(region_index);
            let ContainerKind::Loop(loop_id) = arena.specs[spec].kind else {
                continue;
            };
            let partition = &partitions[loop_id.index()];
            let mut target = None;
            let mut valid = true;
            for block in &partition.owned {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];
                    if partition.owned.contains(&edge.to)
                        || matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        || (!layout_edges
                            .get(edge_ref.index())
                            .is_some_and(|fact| fact.natural)
                            && shared_pure_terminal_kind(cfg, edge.to).is_some())
                    {
                        continue;
                    }
                    let Some(owner) = break_owner_by_edge[edge_ref.index()] else {
                        valid = false;
                        target = None;
                        break;
                    };
                    if owner == region
                        || target.replace(owner).is_some_and(|target| target != owner)
                    {
                        valid = false;
                        target = None;
                        break;
                    }
                }
                if !valid {
                    break;
                }
            }
            if valid && target.is_some() {
                propagated_break_by_region[region.index()] = target;
            }
        }
        // `propagates_break` 位于逐 edge 分类热路径。把“从当前最内 loop 到目标
        // loop 的每一层都声明相同 propagated break”在 loop preorder 中压缩一次，
        // 避免每条跨层 break 再按嵌套深度上爬。
        let mut propagated_break_target_by_region = vec![None; region_count];
        for region in arena.navigation.preorder.iter().copied() {
            let Some(target) = propagated_break_by_region[region.index()] else {
                continue;
            };
            let parent = loop_parent[region.index()];
            if parent == Some(target)
                || parent.is_some_and(|parent| {
                    propagated_break_target_by_region[parent.index()] == Some(target)
                })
            {
                propagated_break_target_by_region[region.index()] = Some(target);
            }
        }

        Ok(Self {
            innermost_by_block,
            control_by_block,
            loop_parent,
            spec_by_region,
            continuation,
            normal_tail_entry,
            break_owner_by_edge,
            continue_owner_by_edge,
            leaves_innermost_loop,
            propagated_break_by_region,
            propagated_break_target_by_region,
        })
    }

    pub(super) fn innermost(&self, block: BlockRef) -> Option<RegionId> {
        self.innermost_by_block
            .get(block.index())
            .copied()
            .flatten()
    }

    pub(super) fn innermost_spec(&self, block: BlockRef) -> Option<(usize, RegionId)> {
        let region = self.innermost(block)?;
        self.loop_parent.get(region.index())?;
        self.spec_by_region[region.index()].map(|spec| (spec, region))
    }

    pub(super) fn propagates_break(&self, source: BlockRef, target: RegionId) -> bool {
        self.innermost(source).is_some_and(|region| {
            region == target
                || self
                    .propagated_break_target_by_region
                    .get(region.index())
                    .copied()
                    .flatten()
                    == Some(target)
        })
    }
}
