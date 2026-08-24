//! GraphFacts 层的稳定事实与树查询。
//!
//! 这里负责支配树、后支配树、SCC、backedge、natural loop 这些“已经脱离原始 CFG 结构、
//! 但仍属于通用图分析”的事实。StructureFacts/HIR 只应该调这些查询接口，不应再回头
//! 自己揉 parent 数组、重新实现最近公共祖先或重复扫描图判断环。NaturalLoopForest
//! 额外冻结 loop parent、innermost owner 和 direct block，供后层按 ancestor iterator 查询。

use std::collections::BTreeSet;

use super::cfg::{BlockRef, EdgeRef};

/// 一个 proto 的图分析事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphFacts {
    pub rpo: Vec<BlockRef>,
    pub dominator_tree: DominatorTree,
    pub post_dominator_tree: PostDominatorTree,
    pub dominance_frontier: Vec<BTreeSet<BlockRef>>,
    pub(crate) strongly_connected_components: Vec<Vec<BlockRef>>,
    pub(crate) cyclic_blocks: Vec<bool>,
    pub backedges: Vec<EdgeRef>,
    pub loop_headers: BTreeSet<BlockRef>,
    pub natural_loops: Vec<NaturalLoop>,
    /// natural-loop evidence 的唯一 containment 索引。
    ///
    /// `natural_loops` 仍保留完整 domain 供现有 Structure 证据使用；新消费者应优先
    /// 使用这份 forest 的 direct block 与 ancestor 查询，避免再次把一个 block 复制到
    /// 每个祖先 loop 的临时集合中。
    pub natural_loop_forest: NaturalLoopForest,
    pub children: Vec<GraphFacts>,
}

impl GraphFacts {
    pub(crate) fn strongly_connected_components(&self) -> impl Iterator<Item = &[BlockRef]> {
        self.strongly_connected_components.iter().map(Vec::as_slice)
    }

    pub fn block_is_cyclic(&self, block: BlockRef) -> bool {
        self.cyclic_blocks
            .get(block.index())
            .copied()
            .unwrap_or(false)
    }

    /// 返回某个 block 的 dominance frontier。
    ///
    /// 调用方应通过这个查询接口消费 frontier，而不是依赖底层当前恰好用
    /// `Vec<BTreeSet<_>>` 存储。这样后续如果要把 frontier 换成更贴合主路径的表示，
    /// 下游分析不需要再跟着改字段访问方式。
    pub fn dominance_frontier_blocks(
        &self,
        block: BlockRef,
    ) -> impl Iterator<Item = BlockRef> + '_ {
        self.dominance_frontier
            .get(block.index())
            .into_iter()
            .flat_map(|frontier| frontier.iter().copied())
    }

    pub fn dominance_frontier_is_empty(&self, block: BlockRef) -> bool {
        self.dominance_frontier
            .get(block.index())
            .is_none_or(BTreeSet::is_empty)
    }

    /// 返回 natural-loop 的共享 containment 查询索引。
    pub fn natural_loop_forest(&self) -> &NaturalLoopForest {
        &self.natural_loop_forest
    }

    pub fn dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        self.dominator_tree.dominates(dom, block)
    }

    pub fn post_dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        self.post_dominator_tree.dominates(dom, block)
    }

    pub fn nearest_common_postdom(&self, left: BlockRef, right: BlockRef) -> Option<BlockRef> {
        self.post_dominator_tree
            .nearest_common_ancestor(left, right)
    }
}

/// 支配树。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DominatorTree {
    pub parent: Vec<Option<BlockRef>>,
    pub children: Vec<Vec<BlockRef>>,
    pub order: Vec<BlockRef>,
    pub(crate) preorder_index: Vec<Option<usize>>,
    pub(crate) subtree_end: Vec<Option<usize>>,
    pub(crate) depth: Vec<Option<usize>>,
    pub(crate) ancestors: Vec<Vec<Option<BlockRef>>>,
}

impl DominatorTree {
    pub fn dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        tree_dominates(&self.preorder_index, &self.subtree_end, dom, block)
    }

    pub fn nearest_common_ancestor(&self, left: BlockRef, right: BlockRef) -> Option<BlockRef> {
        nearest_common_tree_ancestor(&self.parent, &self.depth, &self.ancestors, left, right)
    }
}

/// 后支配树。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PostDominatorTree {
    pub parent: Vec<Option<BlockRef>>,
    pub children: Vec<Vec<BlockRef>>,
    pub order: Vec<BlockRef>,
    pub(crate) preorder_index: Vec<Option<usize>>,
    pub(crate) subtree_end: Vec<Option<usize>>,
    pub(crate) depth: Vec<Option<usize>>,
    pub(crate) ancestors: Vec<Vec<Option<BlockRef>>>,
}

impl PostDominatorTree {
    pub fn dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        tree_dominates(&self.preorder_index, &self.subtree_end, dom, block)
    }

    pub fn nearest_common_ancestor(&self, left: BlockRef, right: BlockRef) -> Option<BlockRef> {
        nearest_common_tree_ancestor(&self.parent, &self.depth, &self.ancestors, left, right)
    }
}

/// 同一个 header 的完整 natural-loop 事实。
///
/// `backedges` 按 CFG edge id 稳定排序，`blocks` 是这些回边 natural domain 的并集。
/// 图层不会把同一 header 拆成多份候选；源码级 loop containment 由 Structure 在消费
/// 这一个事实时一次决定。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaturalLoop {
    pub header: BlockRef,
    pub backedges: Vec<EdgeRef>,
    pub blocks: BTreeSet<BlockRef>,
}

/// Natural-loop 的稠密 containment 事实。
///
/// 图层先把同一 header 的回边合并成一个 `NaturalLoop`，再根据支配树上的严格包含关系
/// 建立 parent/children。每个 reachable block 只保存一个 innermost owner；因此
/// `direct_blocks` 的总长度最多为 block 数，而不是 `block × loop-depth`。遇到不可规约
/// 的交叠 domain 时，owner 会标记为不确定并保守返回 `None`，绝不猜一个祖先关系。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NaturalLoopForest {
    loop_by_header: Vec<Option<NaturalLoopId>>,
    parent: Vec<Option<NaturalLoopId>>,
    children: Vec<Vec<NaturalLoopId>>,
    direct_blocks: Vec<Vec<BlockRef>>,
    innermost_by_block: Vec<Option<NaturalLoopId>>,
    preorder_index: Vec<Option<usize>>,
    subtree_end: Vec<Option<usize>>,
    ambiguous_blocks: Vec<bool>,
}

/// Natural-loop 在 `GraphFacts::natural_loops` 中的稠密 ID。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NaturalLoopId(usize);

impl NaturalLoopId {
    /// 返回该 loop 在 `GraphFacts::natural_loops` 中的稠密下标。
    pub const fn index(self) -> usize {
        self.0
    }
}

impl NaturalLoopForest {
    pub(crate) fn build(
        loops: &[NaturalLoop],
        dominator_tree: &DominatorTree,
        block_count: usize,
    ) -> Self {
        let loop_count = loops.len();
        let mut loop_by_header = vec![None; block_count];
        for (index, natural_loop) in loops.iter().enumerate() {
            let Some(slot) = loop_by_header.get_mut(natural_loop.header.index()) else {
                continue;
            };
            // GraphFacts 已在 CFG 校验后生成；重复 header 理论上不可能，因为
            // compute_natural_loops 会先按 header 合并回边。冲突时保留第一份并让
            // 后续 domain containment 证明自然失败，而不是覆盖已有身份。
            if slot.is_none() {
                *slot = Some(NaturalLoopId(index));
            }
        }

        let mut parent = vec![None; loop_count];
        for (index, natural_loop) in loops.iter().enumerate() {
            let mut cursor = dominator_tree
                .parent
                .get(natural_loop.header.index())
                .copied()
                .flatten();
            while let Some(block) = cursor {
                if let Some(candidate) = loop_by_header.get(block.index()).copied().flatten() {
                    let candidate_index = candidate.index();
                    let candidate_loop = &loops[candidate_index];
                    if candidate_loop.blocks.len() > natural_loop.blocks.len()
                        && natural_loop
                            .blocks
                            .iter()
                            .all(|member| candidate_loop.blocks.contains(member))
                    {
                        parent[index] = Some(candidate);
                        break;
                    }
                }
                cursor = dominator_tree.parent.get(block.index()).copied().flatten();
            }
        }

        let mut children = vec![Vec::new(); loop_count];
        for (index, ancestor) in parent.iter().copied().enumerate() {
            if let Some(ancestor) = ancestor {
                children[ancestor.index()].push(NaturalLoopId(index));
            }
        }
        for child_list in &mut children {
            child_list.sort_unstable();
        }

        // 先冻结 loop containment 的 Euler 区间。后面的 block owner 判定只需要一次
        // 区间查询；如果沿 parent 链逐个回溯，深层嵌套会把同一份 evidence 放大为
        // `block × loop-depth` 的重复工作。
        let mut preorder_index = vec![None; loop_count];
        let mut subtree_end = vec![None; loop_count];
        let mut preorder_len = 0;
        let roots = parent
            .iter()
            .enumerate()
            .filter_map(|(index, parent)| parent.is_none().then_some(NaturalLoopId(index)));
        let mut pending = roots.rev().map(|root| (root, true)).collect::<Vec<_>>();
        while let Some((loop_id, entering)) = pending.pop() {
            if entering {
                preorder_index[loop_id.index()] = Some(preorder_len);
                preorder_len += 1;
                pending.push((loop_id, false));
                pending.extend(
                    children[loop_id.index()]
                        .iter()
                        .rev()
                        .copied()
                        .map(|child| (child, true)),
                );
            } else {
                subtree_end[loop_id.index()] = Some(preorder_len);
            }
        }

        // A block can belong to several natural domains only when the domains are nested in
        // the reducible case. Compare the domains explicitly so an overlapping irreducible
        // pair never receives an invented innermost owner.
        let mut innermost_by_block = vec![None; block_count];
        let mut ambiguous_blocks = vec![false; block_count];
        for (index, natural_loop) in loops.iter().enumerate() {
            let current_id = NaturalLoopId(index);
            for &block in &natural_loop.blocks {
                let Some(current_slot) = innermost_by_block.get_mut(block.index()) else {
                    continue;
                };
                if ambiguous_blocks[block.index()] {
                    continue;
                }
                let Some(previous_id) = *current_slot else {
                    *current_slot = Some(current_id);
                    continue;
                };
                if previous_id == current_id {
                    continue;
                }
                let previous = &loops[previous_id.index()];
                // `parent` points from an inner loop to its outer loop.  Keep the
                // smaller domain as the innermost owner, regardless of the order in
                // which headers were discovered.  A strict subset without the same
                // forest relation is an overlap (or malformed evidence), so it must
                // stay ambiguous instead of inventing an owner.
                if natural_loop.blocks.len() < previous.blocks.len()
                    && natural_loop.blocks.is_subset(&previous.blocks)
                    && strict_loop_ancestor(&preorder_index, &subtree_end, previous_id, current_id)
                {
                    *current_slot = Some(current_id);
                } else if previous.blocks.len() < natural_loop.blocks.len()
                    && previous.blocks.is_subset(&natural_loop.blocks)
                    && strict_loop_ancestor(&preorder_index, &subtree_end, current_id, previous_id)
                {
                    // The existing owner is the strict inner loop.
                } else {
                    *current_slot = None;
                    ambiguous_blocks[block.index()] = true;
                }
            }
        }

        let mut direct_blocks = vec![Vec::new(); loop_count];
        for (block_index, owner) in innermost_by_block.iter().copied().enumerate() {
            if let Some(owner) = owner {
                direct_blocks[owner.index()].push(BlockRef(block_index));
            }
        }

        Self {
            loop_by_header,
            parent,
            children,
            direct_blocks,
            innermost_by_block,
            preorder_index,
            subtree_end,
            ambiguous_blocks,
        }
    }

    /// 返回 forest 中的 loop 数量。
    pub fn len(&self) -> usize {
        self.parent.len()
    }

    /// 判断 forest 是否没有 natural loop。
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    /// 返回一个 loop 的直接父 loop；根 loop 返回 `None`。
    pub fn parent_of(&self, loop_id: NaturalLoopId) -> Option<NaturalLoopId> {
        self.parent.get(loop_id.index()).copied().flatten()
    }

    /// 按 header 查询对应的 merged natural loop。
    pub fn loop_for_header(&self, header: BlockRef) -> Option<NaturalLoopId> {
        self.loop_by_header.get(header.index()).copied().flatten()
    }

    /// 迭代一个 loop 的直接子 loop。
    pub fn children_of(&self, loop_id: NaturalLoopId) -> impl Iterator<Item = NaturalLoopId> + '_ {
        self.children
            .get(loop_id.index())
            .into_iter()
            .flat_map(|children| children.iter().copied())
    }

    /// 返回只属于该 loop、而不属于任何已证明子 loop 的 block。
    pub fn direct_blocks(&self, loop_id: NaturalLoopId) -> &[BlockRef] {
        self.direct_blocks
            .get(loop_id.index())
            .map_or(&[], Vec::as_slice)
    }

    /// 查询某个 block 的唯一 innermost loop；交叠/不可规约 domain 返回 `None`。
    pub fn innermost_loop(&self, block: BlockRef) -> Option<NaturalLoopId> {
        if self
            .ambiguous_blocks
            .get(block.index())
            .copied()
            .unwrap_or(true)
        {
            return None;
        }
        self.innermost_by_block
            .get(block.index())
            .copied()
            .flatten()
    }

    /// 判断 loop 是否包含 block。查询只依赖 forest owner，不重新扫描 CFG。
    pub fn contains(&self, loop_id: NaturalLoopId, block: BlockRef) -> bool {
        let Some(inner) = self.innermost_loop(block) else {
            return false;
        };
        self.is_ancestor_or_self(loop_id, inner)
    }

    /// 判断两个 loop 是否存在 forest ancestor 关系（允许相等）。
    pub fn is_ancestor_or_self(&self, ancestor: NaturalLoopId, descendant: NaturalLoopId) -> bool {
        let (Some(start), Some(end), Some(descendant_start)) = (
            self.preorder_index.get(ancestor.index()).copied().flatten(),
            self.subtree_end.get(ancestor.index()).copied().flatten(),
            self.preorder_index
                .get(descendant.index())
                .copied()
                .flatten(),
        ) else {
            return false;
        };
        start <= descendant_start && descendant_start < end
    }

    /// 返回以 block 的 innermost loop 开始、向外到 root 的祖先迭代器。
    pub fn ancestors_of(&self, block: BlockRef) -> NaturalLoopAncestors<'_> {
        NaturalLoopAncestors {
            forest: self,
            next: self.innermost_loop(block),
        }
    }
}

fn strict_loop_ancestor(
    preorder_index: &[Option<usize>],
    subtree_end: &[Option<usize>],
    ancestor: NaturalLoopId,
    descendant: NaturalLoopId,
) -> bool {
    ancestor != descendant
        && preorder_index
            .get(ancestor.index())
            .copied()
            .flatten()
            .zip(subtree_end.get(ancestor.index()).copied().flatten())
            .zip(preorder_index.get(descendant.index()).copied().flatten())
            .is_some_and(|((start, end), descendant_start)| {
                start <= descendant_start && descendant_start < end
            })
}

/// 从 block 的 innermost loop 向外迭代，避免 lowering 为每个 block 重新展开一份祖先 Vec。
pub struct NaturalLoopAncestors<'a> {
    forest: &'a NaturalLoopForest,
    next: Option<NaturalLoopId>,
}

impl Iterator for NaturalLoopAncestors<'_> {
    type Item = NaturalLoopId;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.next?;
        self.next = self.forest.parent_of(current);
        Some(current)
    }
}

fn tree_dominates(
    preorder_index: &[Option<usize>],
    subtree_end: &[Option<usize>],
    dom: BlockRef,
    block: BlockRef,
) -> bool {
    if dom == block {
        return true;
    }

    let (Some(dom_start), Some(dom_end), Some(block_start)) = (
        preorder_index.get(dom.index()).copied().flatten(),
        subtree_end.get(dom.index()).copied().flatten(),
        preorder_index.get(block.index()).copied().flatten(),
    ) else {
        return false;
    };
    dom_start <= block_start && block_start < dom_end
}

fn nearest_common_tree_ancestor(
    parent: &[Option<BlockRef>],
    depth: &[Option<usize>],
    ancestors: &[Vec<Option<BlockRef>>],
    mut left: BlockRef,
    mut right: BlockRef,
) -> Option<BlockRef> {
    let mut left_depth = depth.get(left.index()).copied().flatten()?;
    let mut right_depth = depth.get(right.index()).copied().flatten()?;

    if left_depth < right_depth {
        std::mem::swap(&mut left, &mut right);
        std::mem::swap(&mut left_depth, &mut right_depth);
    }
    left = lift_tree_node(ancestors, left, left_depth - right_depth)?;

    if left == right {
        return Some(left);
    }
    for level in (0..ancestors.len()).rev() {
        let left_ancestor = ancestors[level][left.index()];
        let right_ancestor = ancestors[level][right.index()];
        if left_ancestor != right_ancestor
            && let (Some(next_left), Some(next_right)) = (left_ancestor, right_ancestor)
        {
            left = next_left;
            right = next_right;
        }
    }

    parent[left.index()]
}

fn lift_tree_node(
    ancestors: &[Vec<Option<BlockRef>>],
    mut block: BlockRef,
    mut distance: usize,
) -> Option<BlockRef> {
    let mut level = 0;
    while distance != 0 {
        if distance & 1 != 0 {
            block = ancestors
                .get(level)?
                .get(block.index())
                .copied()
                .flatten()?;
        }
        distance >>= 1;
        level += 1;
    }
    Some(block)
}
