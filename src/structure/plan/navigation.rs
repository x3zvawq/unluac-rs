//! 最终 region containment、CFG 端点关系与源码布局完成位置的共享索引。
//!
//! parent/Euler 事实来自最终 arena；完成路径只穿过 Sequence/island 的末项与
//! structured owner 的语法子区，不能用任意 descendant 代替正常完成。比如
//! `Branch { then: island [A, B] }; C` 中 A -> C 必须保留显式跳转，只有 B 能
//! 从 island 落底后结束 branch。这里不替代 loop 的 break/continue/条件出口分类。
//! 构建时先冻结不依赖 sibling 顺序的拓扑供 layout 排序，排序完成后才冻结完成路径；
//! RegionArena 只发布 finish_layout 返回的最终索引。
//! reachable block 按最终 owner 的 Euler 位置只存一份，子树查询借用连续区间；
//! 例如 island 直接拥有的块与其 structured child 的块共同属于 island，不能只枚举 Block 节点。

use crate::structure::{BlockRef, Cfg, EdgeRef, StructurePlan};

use super::{RegionId, RegionPlan, StructureError, UnstructuredLayoutItem};

/// 一条 CFG edge 的两个端点在最终 containment tree 上的唯一关系。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct EdgeRegionRelation {
    pub source_owner: Option<RegionId>,
    pub target_owner: Option<RegionId>,
    pub lca: Option<RegionId>,
    pub source_child: Option<RegionId>,
    pub target_child: Option<RegionId>,
}

/// region 的派生压缩边界；真实 crossing edge 由 `EdgeRegionRelation` 按需判定。
///
/// `Unstructured` 的权威边界是它冻结的 `entries/exits`，本摘要只服务通用导航查询。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RegionBoundarySummary {
    pub entry_count: usize,
    pub exit_count: usize,
}

/// island 的冻结边界端口；两个外层 Vec 都以 `RegionId` 稠密索引。
pub(super) struct IslandBoundaryPorts {
    pub(super) entries: Vec<Vec<EdgeRef>>,
    pub(super) exits: Vec<Vec<EdgeRef>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum DirectCompletion {
    #[default]
    None,
    ExactBlock(BlockRef),
    ValueDecision,
}

/// 最终 region arena 的共享导航索引。
///
/// containment 只存稠密 parent/Euler 表；每条 CFG edge 只存一条端点关系，
/// 不把 crossing edge 沿所有祖先 region 展开。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionNavigation {
    pub(super) root: RegionId,
    pub(super) parent: Vec<Option<RegionId>>,
    pub(super) depth: Vec<usize>,
    pub(super) preorder: Vec<RegionId>,
    pub(super) postorder: Vec<RegionId>,
    pub(super) preorder_index: Vec<usize>,
    pub(super) subtree_end: Vec<usize>,
    reachable_blocks_by_owner: Vec<BlockRef>,
    owned_block_offsets: Vec<usize>,
    edge_relations: Vec<EdgeRegionRelation>,
    boundaries: Vec<RegionBoundarySummary>,
    has_unstructured_ancestor: Vec<bool>,
    completion_root: Vec<RegionId>,
    direct_completion: Vec<DirectCompletion>,
}

impl RegionNavigation {
    pub(super) fn build_topology(
        cfg: &Cfg,
        root: RegionId,
        regions: &[RegionPlan],
        region_by_block: &[Option<RegionId>],
    ) -> Result<Self, StructureError> {
        if regions.is_empty() || root.index() >= regions.len() {
            return Err(StructureError::invalid(
                "cannot navigate an empty or rootless region arena",
            ));
        }

        let mut parent = vec![None; regions.len()];
        let mut children = vec![Vec::new(); regions.len()];
        for (index, region) in regions.iter().enumerate() {
            let id = RegionId(index);
            match region.parent() {
                None if id == root => {}
                None => {
                    return Err(StructureError::invalid(format!(
                        "non-root region #{index} has no parent"
                    )));
                }
                Some(_) if id == root => {
                    return Err(StructureError::invalid(
                        "root region unexpectedly has a parent",
                    ));
                }
                Some(owner) => {
                    let Some(owned) = children.get_mut(owner.index()) else {
                        return Err(StructureError::invalid(format!(
                            "region #{index} references missing parent #{}",
                            owner.index()
                        )));
                    };
                    parent[index] = Some(owner);
                    owned.push(id);
                }
            }
        }

        let mut depth = vec![0usize; regions.len()];
        let mut preorder = Vec::with_capacity(regions.len());
        let mut postorder = Vec::with_capacity(regions.len());
        let mut preorder_index = vec![usize::MAX; regions.len()];
        let mut subtree_end = vec![usize::MAX; regions.len()];
        let mut pending = vec![(root, false)];
        while let Some((region, leaving)) = pending.pop() {
            if leaving {
                subtree_end[region.index()] = preorder.len();
                postorder.push(region);
                continue;
            }
            if preorder_index[region.index()] != usize::MAX {
                return Err(StructureError::invalid(
                    "region containment contains a cycle or duplicate parent",
                ));
            }
            preorder_index[region.index()] = preorder.len();
            preorder.push(region);
            if let Some(owner) = parent[region.index()] {
                depth[region.index()] = depth[owner.index()]
                    .checked_add(1)
                    .ok_or_else(|| StructureError::invalid("region depth overflowed"))?;
            }
            pending.push((region, true));
            pending.extend(
                children[region.index()]
                    .iter()
                    .rev()
                    .map(|child| (*child, false)),
            );
        }
        if let Some(index) = preorder_index
            .iter()
            .position(|position| *position == usize::MAX)
        {
            return Err(StructureError::invalid(format!(
                "region #{index} is disconnected from root"
            )));
        }

        let mut navigation = Self {
            root,
            parent,
            depth,
            preorder,
            postorder,
            preorder_index,
            subtree_end,
            reachable_blocks_by_owner: Vec::new(),
            owned_block_offsets: Vec::new(),
            edge_relations: vec![EdgeRegionRelation::default(); cfg.edges.len()],
            boundaries: vec![RegionBoundarySummary::default(); regions.len()],
            has_unstructured_ancestor: vec![false; regions.len()],
            completion_root: (0..regions.len()).map(RegionId).collect(),
            direct_completion: vec![DirectCompletion::None; regions.len()],
        };
        navigation.freeze_region_facts(regions)?;
        navigation.freeze_edges_and_boundaries(cfg, region_by_block, &children)?;
        navigation.freeze_owned_blocks(cfg, region_by_block)?;
        Ok(navigation)
    }

    fn freeze_owned_blocks(
        &mut self,
        cfg: &Cfg,
        region_by_block: &[Option<RegionId>],
    ) -> Result<(), StructureError> {
        self.owned_block_offsets = vec![0; self.preorder.len() + 1];
        for block in &cfg.reachable_blocks {
            let Some(owner) = region_by_block.get(block.index()).copied().flatten() else {
                continue;
            };
            let position = self.preorder_index.get(owner.index()).ok_or_else(|| {
                StructureError::invalid("reachable block references a missing region")
            })?;
            self.owned_block_offsets[position + 1] += 1;
        }
        for position in 1..self.owned_block_offsets.len() {
            self.owned_block_offsets[position] += self.owned_block_offsets[position - 1];
        }
        let mut next = self.owned_block_offsets[..self.preorder.len()].to_vec();
        self.reachable_blocks_by_owner =
            vec![BlockRef::default(); self.owned_block_offsets[self.preorder.len()]];
        for block in &cfg.reachable_blocks {
            let Some(owner) = region_by_block.get(block.index()).copied().flatten() else {
                continue;
            };
            let position = self.preorder_index[owner.index()];
            self.reachable_blocks_by_owner[next[position]] = *block;
            next[position] += 1;
        }
        Ok(())
    }

    /// 按 containment 查询可达块；返回顺序不代表 CFG 或源码执行顺序。
    pub(crate) fn blocks(&self, region: RegionId) -> &[BlockRef] {
        let Some(&start) = self.preorder_index.get(region.index()) else {
            return &[];
        };
        let end = self.subtree_end[region.index()];
        &self.reachable_blocks_by_owner
            [self.owned_block_offsets[start]..self.owned_block_offsets[end]]
    }

    /// 只借出当前 owner 的可达块，排除子 region，供 preorder 中的活动控制目标查询。
    pub(super) fn direct_blocks(&self, region: RegionId) -> &[BlockRef] {
        let Some(&position) = self.preorder_index.get(region.index()) else {
            return &[];
        };
        &self.reachable_blocks_by_owner
            [self.owned_block_offsets[position]..self.owned_block_offsets[position + 1]]
    }

    pub(super) fn finish_layout(mut self, regions: &[RegionPlan]) -> Result<Self, StructureError> {
        self.freeze_completion_paths(regions)?;
        Ok(self)
    }

    fn freeze_region_facts(&mut self, regions: &[RegionPlan]) -> Result<(), StructureError> {
        for region in &self.preorder {
            let inherited = self.parent[region.index()]
                .is_some_and(|parent| self.has_unstructured_ancestor[parent.index()]);
            let current = matches!(
                regions.get(region.index()),
                Some(RegionPlan::Unstructured { .. })
            );
            if inherited && current {
                return Err(StructureError::invalid(format!(
                    "unstructured region #{} is nested inside another island",
                    region.index()
                )));
            }
            self.has_unstructured_ancestor[region.index()] = inherited || current;
        }
        Ok(())
    }

    fn freeze_completion_paths(&mut self, regions: &[RegionPlan]) -> Result<(), StructureError> {
        let mut completes_parent = vec![false; regions.len()];
        let mut empty = vec![false; regions.len()];
        for &region in &self.postorder {
            let mut connect = |child: RegionId| -> Result<(), StructureError> {
                if self.parent.get(child.index()).copied().flatten() != Some(region) {
                    return Err(StructureError::invalid(
                        "region completion references a child with a different owner",
                    ));
                }
                completes_parent[child.index()] = true;
                Ok(())
            };
            match &regions[region.index()] {
                RegionPlan::Block { block, .. } => {
                    self.direct_completion[region.index()] = DirectCompletion::ExactBlock(*block);
                }
                RegionPlan::ValueDecision { .. } => {
                    // 整个 DAG 由 value-decision payload 吸收；其 leaf 出口不按块排序。
                    self.direct_completion[region.index()] = DirectCompletion::ValueDecision;
                }
                RegionPlan::Sequence { parent, children } => {
                    let syntax_control = parent
                        .and_then(|parent| regions.get(parent.index()))
                        .is_some_and(|parent| match parent {
                            RegionPlan::Branch { condition, .. } => *condition == region,
                            RegionPlan::Loop { control, .. } => *control == region,
                            _ => false,
                        });
                    empty[region.index()] = true;
                    for &child in children.iter().rev() {
                        connect(child)?;
                        if !empty[child.index()] {
                            empty[region.index()] = false;
                            // 条件 DAG/VM loop control 由 syntax payload 发射，不是源码
                            // 顺序语句；短路 terminal arc 可以从任一 control block 退出。
                            if !syntax_control {
                                break;
                            }
                        }
                    }
                }
                RegionPlan::Unstructured { layout, .. } => {
                    empty[region.index()] = true;
                    for item in layout.iter().rev() {
                        match *item {
                            UnstructuredLayoutItem::Block(block) => {
                                self.direct_completion[region.index()] =
                                    DirectCompletion::ExactBlock(block);
                                empty[region.index()] = false;
                                break;
                            }
                            UnstructuredLayoutItem::Region(child) => {
                                connect(child)?;
                                if !empty[child.index()] {
                                    empty[region.index()] = false;
                                    break;
                                }
                            }
                        }
                    }
                }
                RegionPlan::Branch {
                    condition,
                    then_arm,
                    else_arm,
                    ..
                } => {
                    // 各 arm 互斥，其内部 Sequence 仍必须真正落底。condition 的出口
                    // 角色由冻结的 condition arcs 决定，不能把另一个 arm 当作后继尾部。
                    connect(*condition)?;
                    connect(*then_arm)?;
                    if let Some(else_arm) = else_arm {
                        connect(*else_arm)?;
                    }
                }
                RegionPlan::Loop {
                    preheader,
                    control,
                    body,
                    normal_tail,
                    ..
                } => {
                    // 这里只传递各语法子区的布局完成位置；提前 break、continue 与 VM
                    // control 出口仍由 EdgeSemantics/LoopControlEdges 决定，不能从顺序猜测。
                    for child in preheader.iter().chain([control, body]).chain(normal_tail) {
                        connect(*child)?;
                    }
                }
            }
        }
        // 允许完成的 parent 边构成 containment 子森林；同一分量内的祖先查询即为
        // 完成路径，避免每条 CFG edge 沿深层 Sequence/branch/island 重复爬祖先。
        for &region in &self.preorder {
            if completes_parent[region.index()]
                && let Some(parent) = self.parent[region.index()]
            {
                self.completion_root[region.index()] = self.completion_root[parent.index()];
            }
        }
        Ok(())
    }

    fn freeze_edges_and_boundaries(
        &mut self,
        cfg: &Cfg,
        region_by_block: &[Option<RegionId>],
        children: &[Vec<RegionId>],
    ) -> Result<(), StructureError> {
        self.freeze_edge_relations(cfg, region_by_block, children)?;
        let mut entry_delta = vec![0isize; self.parent.len()];
        let mut exit_delta = vec![0isize; self.parent.len()];
        for (index, edge) in cfg.edges.iter().enumerate() {
            let relation = self.edge_relations[index];
            let source_owner = relation.source_owner;
            let target_owner = relation.target_owner;
            let lca = relation.lca;

            if !cfg.reachable_blocks.contains(&edge.from) {
                continue;
            }
            if let Some(source) = source_owner
                && Some(source) != lca
            {
                exit_delta[source.index()] += 1;
                if let Some(owner) = lca {
                    exit_delta[owner.index()] -= 1;
                }
            }
            if let Some(target) = target_owner
                && Some(target) != lca
            {
                entry_delta[target.index()] += 1;
                if let Some(owner) = lca {
                    entry_delta[owner.index()] -= 1;
                }
            }
        }
        for region in &self.postorder {
            let Some(owner) = self.parent[region.index()] else {
                continue;
            };
            entry_delta[owner.index()] += entry_delta[region.index()];
            exit_delta[owner.index()] += exit_delta[region.index()];
        }
        for index in 0..self.boundaries.len() {
            self.boundaries[index] = RegionBoundarySummary {
                entry_count: usize::try_from(entry_delta[index]).map_err(|_| {
                    StructureError::invalid("region entry boundary count became negative")
                })?,
                exit_count: usize::try_from(exit_delta[index]).map_err(|_| {
                    StructureError::invalid("region exit boundary count became negative")
                })?,
            };
        }
        Ok(())
    }

    /// Tarjan 离线 LCA 一次回答所有 CFG edge 端点，再按 descendant
    /// 分组用同一次 preorder path 回答 LCA 下的直接 child。
    fn freeze_edge_relations(
        &mut self,
        cfg: &Cfg,
        region_by_block: &[Option<RegionId>],
        children: &[Vec<RegionId>],
    ) -> Result<(), StructureError> {
        let region_count = self.parent.len();
        let mut queries = vec![Vec::<(RegionId, usize)>::new(); region_count];
        for (index, edge) in cfg.edges.iter().enumerate() {
            let source_owner = region_by_block.get(edge.from.index()).copied().flatten();
            let target_owner = region_by_block.get(edge.to.index()).copied().flatten();
            for owner in [source_owner, target_owner].into_iter().flatten() {
                if owner.index() >= region_count {
                    return Err(StructureError::invalid(format!(
                        "CFG edge #{index} references missing region #{}",
                        owner.index()
                    )));
                }
            }
            self.edge_relations[index].source_owner = source_owner;
            self.edge_relations[index].target_owner = target_owner;
            let Some((source, target)) = source_owner.zip(target_owner) else {
                continue;
            };
            if source == target {
                self.edge_relations[index].lca = Some(source);
                continue;
            }
            queries[source.index()].push((target, index));
            queries[target.index()].push((source, index));
        }

        let mut union_find = UnionFind::new(region_count);
        let mut ancestor = (0..region_count).map(RegionId).collect::<Vec<_>>();
        let mut finished = vec![false; region_count];
        let mut pending = vec![TarjanEvent::Enter(self.root)];
        while let Some(event) = pending.pop() {
            match event {
                TarjanEvent::Enter(region) => {
                    ancestor[union_find.find(region.index())] = region;
                    pending.push(TarjanEvent::Exit(region));
                    for child in children[region.index()].iter().rev() {
                        pending.push(TarjanEvent::AfterChild {
                            parent: region,
                            child: *child,
                        });
                        pending.push(TarjanEvent::Enter(*child));
                    }
                }
                TarjanEvent::AfterChild { parent, child } => {
                    union_find.union(parent.index(), child.index());
                    ancestor[union_find.find(parent.index())] = parent;
                }
                TarjanEvent::Exit(region) => {
                    finished[region.index()] = true;
                    for (other, edge) in &queries[region.index()] {
                        if finished[other.index()] {
                            self.edge_relations[*edge].lca =
                                Some(ancestor[union_find.find(other.index())]);
                        }
                    }
                }
            }
        }
        if let Some(index) = self.edge_relations.iter().position(|relation| {
            relation.source_owner.is_some()
                && relation.target_owner.is_some()
                && relation.lca.is_none()
        }) {
            return Err(StructureError::invalid(format!(
                "failed to resolve region LCA for CFG edge #{index}"
            )));
        }

        #[derive(Clone, Copy)]
        enum Endpoint {
            Source,
            Target,
        }
        let mut child_queries = vec![Vec::<(usize, RegionId, Endpoint)>::new(); region_count];
        for (edge, relation) in self.edge_relations.iter().copied().enumerate() {
            let Some(lca) = relation.lca else {
                continue;
            };
            if let Some(source) = relation.source_owner
                && source != lca
            {
                child_queries[source.index()].push((edge, lca, Endpoint::Source));
            }
            if let Some(target) = relation.target_owner
                && target != lca
            {
                child_queries[target.index()].push((edge, lca, Endpoint::Target));
            }
        }
        let mut path = Vec::new();
        for descendant in &self.preorder {
            path.truncate(self.depth[descendant.index()]);
            path.push(*descendant);
            for (edge, ancestor, endpoint) in &child_queries[descendant.index()] {
                let child = path
                    .get(self.depth[ancestor.index()] + 1)
                    .copied()
                    .ok_or_else(|| {
                        StructureError::invalid("edge LCA is not an ancestor of its endpoint owner")
                    })?;
                match endpoint {
                    Endpoint::Source => self.edge_relations[*edge].source_child = Some(child),
                    Endpoint::Target => self.edge_relations[*edge].target_child = Some(child),
                }
            }
        }
        Ok(())
    }

    pub(super) fn validate(&self, cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
        let expected = Self::build_topology(cfg, plan.root, &plan.regions, &plan.region_by_block)?
            .finish_layout(&plan.regions)?;
        if *self != expected {
            return Err(StructureError::invalid(
                "region navigation or edge relation index is stale",
            ));
        }
        Ok(())
    }

    pub fn contains(&self, outer: RegionId, inner: RegionId) -> bool {
        self.preorder_index
            .get(outer.index())
            .zip(self.subtree_end.get(outer.index()))
            .zip(self.preorder_index.get(inner.index()))
            .is_some_and(|((start, end), position)| {
                *start != usize::MAX && *start <= *position && *position < *end
            })
    }

    pub fn edge_relation(&self, edge: EdgeRef) -> Option<EdgeRegionRelation> {
        self.edge_relations.get(edge.index()).copied()
    }

    pub fn boundary(&self, region: RegionId) -> Option<RegionBoundarySummary> {
        self.boundaries.get(region.index()).copied()
    }

    /// 按 containment crossing 精确收集每个 island 的 CFG entry/exit edge。
    ///
    /// 每条 edge 只沿实际跨越的 island ancestor 链追加。最终计划禁止 island 嵌套，
    /// 因而端口总量至多为 `2 * edges`，整体复杂度保持线性。
    pub(super) fn collect_island_ports(
        &self,
        cfg: &Cfg,
        regions: &[RegionPlan],
    ) -> Result<IslandBoundaryPorts, StructureError> {
        if regions.len() != self.parent.len() || cfg.edges.len() != self.edge_relations.len() {
            return Err(StructureError::invalid(
                "cannot collect island ports from stale region navigation",
            ));
        }

        let mut parent_island = vec![None; regions.len()];
        let mut nearest_island = vec![None; regions.len()];
        for region in &self.preorder {
            let inherited =
                self.parent[region.index()].and_then(|parent| nearest_island[parent.index()]);
            parent_island[region.index()] = inherited;
            nearest_island[region.index()] =
                if matches!(regions[region.index()], RegionPlan::Unstructured { .. }) {
                    Some(*region)
                } else {
                    inherited
                };
        }

        let mut ports = IslandBoundaryPorts {
            entries: vec![Vec::new(); regions.len()],
            exits: vec![Vec::new(); regions.len()],
        };
        for (index, edge) in cfg.edges.iter().enumerate() {
            if !cfg.reachable_blocks.contains(&edge.from) {
                continue;
            }
            let edge_ref = EdgeRef(index);
            let relation = self.edge_relations[index];

            let mut island = relation
                .target_owner
                .and_then(|owner| nearest_island[owner.index()]);
            while let Some(region) = island {
                if relation
                    .source_owner
                    .is_some_and(|owner| self.contains(region, owner))
                {
                    break;
                }
                ports.entries[region.index()].push(edge_ref);
                island = parent_island[region.index()];
            }

            let mut island = relation
                .source_owner
                .and_then(|owner| nearest_island[owner.index()]);
            while let Some(region) = island {
                if relation
                    .target_owner
                    .is_some_and(|owner| self.contains(region, owner))
                {
                    break;
                }
                ports.exits[region.index()].push(edge_ref);
                island = parent_island[region.index()];
            }
        }
        Ok(ports)
    }

    pub(crate) fn postorder(&self) -> &[RegionId] {
        &self.postorder
    }

    pub(crate) fn postorder_rank(&self, region: RegionId) -> Option<usize> {
        let end = *self.subtree_end.get(region.index())?;
        // 子树退出时，已进入的节点中仅自身和 depth 个祖先尚未退出。
        Some(end - self.depth[region.index()] - 1)
    }

    pub(super) fn has_unstructured_ancestor(&self, region: RegionId) -> bool {
        self.has_unstructured_ancestor
            .get(region.index())
            .copied()
            .unwrap_or(true)
    }

    pub(super) fn multi_entry_island_prefix(&self, regions: &[RegionPlan]) -> Vec<usize> {
        let mut prefix = vec![0usize; self.parent.len()];
        for region in &self.preorder {
            let inherited = self.parent[region.index()].map_or(0, |parent| prefix[parent.index()]);
            let current = matches!(
                regions.get(region.index()),
                Some(RegionPlan::Unstructured { entries, .. }) if entries.len() > 1
            );
            prefix[region.index()] = inherited + usize::from(current);
        }
        prefix
    }

    pub(super) fn edge_enters_prefixed_region(&self, edge: EdgeRef, prefix: &[usize]) -> bool {
        let Some(relation) = self.edge_relation(edge) else {
            return false;
        };
        let Some(target) = relation.target_owner else {
            return false;
        };
        let target_count = prefix.get(target.index()).copied().unwrap_or(0);
        let shared_count = relation
            .lca
            .and_then(|owner| prefix.get(owner.index()).copied())
            .unwrap_or(0);
        target_count > shared_count
    }

    pub(super) fn region_can_complete_from(
        &self,
        region: RegionId,
        source_owner: RegionId,
        source_block: BlockRef,
    ) -> bool {
        self.contains(region, source_owner)
            && self.completion_root[region.index()] == self.completion_root[source_owner.index()]
            && match self.direct_completion[source_owner.index()] {
                DirectCompletion::ExactBlock(block) => source_block == block,
                DirectCompletion::ValueDecision => true,
                DirectCompletion::None => false,
            }
    }
}

#[derive(Debug, Clone, Copy)]
enum TarjanEvent {
    Enter(RegionId),
    AfterChild { parent: RegionId, child: RegionId },
    Exit(RegionId),
}

struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
            rank: vec![0; len],
        }
    }

    fn find(&mut self, mut value: usize) -> usize {
        let mut root = value;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        while self.parent[value] != value {
            let parent = self.parent[value];
            self.parent[value] = root;
            value = parent;
        }
        root
    }

    fn union(&mut self, left: usize, right: usize) {
        let mut left_root = self.find(left);
        let mut right_root = self.find(right);
        if left_root == right_root {
            return;
        }
        if self.rank[left_root] < self.rank[right_root] {
            std::mem::swap(&mut left_root, &mut right_root);
        }
        self.parent[right_root] = left_root;
        if self.rank[left_root] == self.rank[right_root] {
            self.rank[left_root] += 1;
        }
    }
}
