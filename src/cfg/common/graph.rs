//! GraphFacts 层的稳定事实与树查询。
//!
//! 这里负责支配树、后支配树、backedge、natural loop 这些“已经脱离原始 CFG 结构、
//! 但仍属于通用图分析”的事实。StructureFacts/HIR 只应该调这些查询接口，不应再回头
//! 自己揉 parent 数组或重新实现最近公共祖先逻辑。

use std::collections::BTreeSet;

use super::cfg::{BlockRef, EdgeRef};

/// 一个 proto 的图分析事实，以及它的子 proto 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphFacts {
    pub rpo: Vec<BlockRef>,
    pub dominator_tree: DominatorTree,
    pub post_dominator_tree: PostDominatorTree,
    pub dominance_frontier: Vec<BTreeSet<BlockRef>>,
    pub backedges: Vec<EdgeRef>,
    pub loop_headers: BTreeSet<BlockRef>,
    pub natural_loops: Vec<NaturalLoop>,
    pub children: Vec<GraphFacts>,
}

impl GraphFacts {
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
}

impl DominatorTree {
    pub fn dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        tree_dominates(&self.parent, dom, block)
    }

    pub fn nearest_common_ancestor(&self, left: BlockRef, right: BlockRef) -> Option<BlockRef> {
        nearest_common_tree_ancestor(&self.parent, left, right)
    }
}

/// 后支配树。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PostDominatorTree {
    pub parent: Vec<Option<BlockRef>>,
    pub children: Vec<Vec<BlockRef>>,
    pub order: Vec<BlockRef>,
}

impl PostDominatorTree {
    pub fn dominates(&self, dom: BlockRef, block: BlockRef) -> bool {
        tree_dominates(&self.parent, dom, block)
    }

    pub fn nearest_common_ancestor(&self, left: BlockRef, right: BlockRef) -> Option<BlockRef> {
        nearest_common_tree_ancestor(&self.parent, left, right)
    }
}

/// 一条 natural loop 事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaturalLoop {
    pub header: BlockRef,
    pub backedge: EdgeRef,
    pub blocks: BTreeSet<BlockRef>,
}

fn tree_dominates(parent: &[Option<BlockRef>], dom: BlockRef, mut block: BlockRef) -> bool {
    if dom == block {
        return true;
    }

    while let Some(next) = parent[block.index()] {
        if next == dom {
            return true;
        }
        block = next;
    }

    false
}

fn nearest_common_tree_ancestor(
    parent: &[Option<BlockRef>],
    left: BlockRef,
    right: BlockRef,
) -> Option<BlockRef> {
    let mut ancestors = BTreeSet::new();
    let mut cursor = Some(left);
    while let Some(block) = cursor {
        ancestors.insert(block);
        cursor = parent[block.index()];
    }

    let mut cursor = Some(right);
    while let Some(block) = cursor {
        if ancestors.contains(&block) {
            return Some(block);
        }
        cursor = parent[block.index()];
    }

    None
}
