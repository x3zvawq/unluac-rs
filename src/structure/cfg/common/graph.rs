//! GraphFacts 层的稳定事实与树查询。
//!
//! 这里负责支配树、后支配树、SCC、backedge、natural loop 这些“已经脱离原始 CFG 结构、
//! 但仍属于通用图分析”的事实。StructureFacts/HIR 只应该调这些查询接口，不应再回头
//! 自己揉 parent 数组、重新实现最近公共祖先或重复扫描图判断环。NaturalLoopForest
//! 额外冻结 loop parent、innermost owner 和 direct block，供后层按 ancestor iterator 查询。
//! SCC 同时保留拓扑身份与 condensation 前驱；例如 `entry -> a -> b -> a` 中 a/b
//! 共用一个成环身份，捕获写后分析直接查询该身份，不再另建 block-to-SCC 映射。
//! 迭代支配边界统一扩展已有定义与合流种子；值活性、Close 出口及虚拟入口仍由消费者决定。

use std::collections::{BTreeSet, VecDeque};

use super::cfg::{BlockRef, EdgeRef};

/// 一个 proto 的图分析事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphFacts {
    pub rpo: Vec<BlockRef>,
    pub dominator_tree: DominatorTree,
    pub post_dominator_tree: PostDominatorTree,
    pub dominance_frontier: Vec<BTreeSet<BlockRef>>,
    pub(crate) scc: SccFacts,
    pub backedges: Vec<EdgeRef>,
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
        self.scc.components.iter().map(Vec::as_slice)
    }

    pub(crate) fn scc_id(&self, block: BlockRef) -> Option<SccId> {
        self.scc.block_scc.get(block.index()).copied().flatten()
    }

    pub(crate) fn scc_count(&self) -> usize {
        self.scc.components.len()
    }

    pub(crate) fn scc_predecessors(&self, scc: SccId) -> &[SccId] {
        &self.scc.predecessors[scc.index()]
    }

    pub fn block_is_cyclic(&self, block: BlockRef) -> bool {
        self.scc_id(block)
            .is_some_and(|scc| self.scc.cyclic[scc.index()])
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

    /// 扩展定义与已有合流点的迭代支配边界，活性条件只裁剪新发现的合流点。
    ///
    /// 已有合流点也作为传播种子，例如 Close 的真实循环出口还可能在下游再次汇合。
    /// 虚拟函数入口没有真实 CFG 边，不能在这里猜测其定义或把它提前加入传播。
    pub(crate) fn extend_dominance_frontier(
        &self,
        definitions: &BTreeSet<BlockRef>,
        merges: &mut BTreeSet<BlockRef>,
        is_live: impl Fn(BlockRef) -> bool,
    ) {
        let mut pending = definitions
            .iter()
            .chain(merges.iter())
            .copied()
            .collect::<VecDeque<_>>();
        while let Some(block) = pending.pop_front() {
            for frontier in self.dominance_frontier_blocks(block) {
                if is_live(frontier) && merges.insert(frontier) && !definitions.contains(&frontier)
                {
                    pending.push_back(frontier);
                }
            }
        }
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

/// 可达 CFG 的 SCC 身份，严格按 condensation 拓扑序编号。
///
/// 跨 SCC 边只能从较小编号到较大编号；消费者可据此裁剪查询范围，不能重建编号。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct SccId(pub(crate) usize);

impl SccId {
    pub(crate) const fn index(self) -> usize {
        self.0
    }
}

/// Graph 分析一次冻结成员、身份、成环与 condensation 前驱；不缓存平方规模传递闭包。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SccFacts {
    pub(crate) components: Vec<Vec<BlockRef>>,
    pub(crate) block_scc: Vec<Option<SccId>>,
    pub(crate) cyclic: Vec<bool>,
    pub(crate) predecessors: Vec<Vec<SccId>>,
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
    /// 第 k 行是 2^(k+1) 步祖先；单步祖先直接使用 parent。
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
    /// 第 k 行是 2^(k+1) 步祖先；单步祖先直接使用 parent。
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
/// 歧义标记只在构建期阻止 owner 恢复；发布时 `None` 已承载该结果。无 loop 时不保存 CFG 容量。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NaturalLoopForest {
    loop_by_header: Vec<Option<NaturalLoopId>>,
    parent: Vec<Option<NaturalLoopId>>,
    children: Vec<Vec<NaturalLoopId>>,
    direct_blocks: Vec<Vec<BlockRef>>,
    innermost_by_block: Vec<Option<NaturalLoopId>>,
    preorder_index: Vec<Option<usize>>,
    subtree_end: Vec<Option<usize>>,
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
        if loops.is_empty() {
            return Self::default();
        }
        let loop_count = loops.len();
        let mut loop_by_header = vec![None; block_count];
        for (index, natural_loop) in loops.iter().enumerate() {
            // 唯一生产者已校验 CFG，并按 header 合并全部回边，身份无需再次去重。
            loop_by_header[natural_loop.header.index()] = Some(NaturalLoopId(index));
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
                        && natural_loop.blocks.is_subset(&candidate_loop.blocks)
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

        // 每条 parent 边已证明严格集合包含，且该关系可传递；owner 选择直接消费
        // 冻结的祖先区间，不按 block 重复比较整个 domain。仅有集合包含而没有
        // 已证明的 forest 祖先关系时，仍按交叠处理，不签发 innermost owner。
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
                if strict_loop_ancestor(&preorder_index, &subtree_end, previous_id, current_id) {
                    *current_slot = Some(current_id);
                } else if !strict_loop_ancestor(
                    &preorder_index,
                    &subtree_end,
                    current_id,
                    previous_id,
                ) {
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
    left = lift_tree_node(parent, ancestors, left, left_depth - right_depth)?;

    if left == right {
        return Some(left);
    }
    for level in ancestors
        .iter()
        .rev()
        .map(Vec::as_slice)
        .chain(std::iter::once(parent))
    {
        let left_ancestor = level[left.index()];
        let right_ancestor = level[right.index()];
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
    parent: &[Option<BlockRef>],
    ancestors: &[Vec<Option<BlockRef>>],
    mut block: BlockRef,
    mut distance: usize,
) -> Option<BlockRef> {
    let mut levels = std::iter::once(parent).chain(ancestors.iter().map(Vec::as_slice));
    while distance != 0 {
        let level = levels.next()?;
        if distance & 1 != 0 {
            block = level.get(block.index()).copied().flatten()?;
        }
        distance >>= 1;
    }
    Some(block)
}
