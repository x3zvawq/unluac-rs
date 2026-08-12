//! GraphFacts 层的稳定事实与树查询。
//!
//! 这里负责支配树、后支配树、SCC、backedge、natural loop 这些“已经脱离原始 CFG 结构、
//! 但仍属于通用图分析”的事实。StructureFacts/HIR 只应该调这些查询接口，不应再回头
//! 自己揉 parent 数组、重新实现最近公共祖先或重复扫描图判断环。

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
