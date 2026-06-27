//! CFG 构图层的稳定类型与基础查询。
//!
//! 这一层只表达 basic block、edge 和可达性等稳定图结构，不夹带 GraphFacts /
//! Dataflow 的派生语义。后续如果 StructureFacts/HIR 需要稳定 block/edge 查询，
//! 也应优先补在这里，而不是再在后层各自包一层小型 CFG API。

use std::collections::{BTreeSet, VecDeque};
use std::fmt;

use crate::transformer::{InstrRef, LowInstr};

/// 一个 proto 的控制流图，以及它的子 proto 图。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgGraph {
    pub cfg: Cfg,
    pub children: Vec<CfgGraph>,
}

/// 单个 proto 的基础控制流图。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Cfg {
    pub blocks: Vec<BasicBlock>,
    pub edges: Vec<CfgEdge>,
    pub entry_block: BlockRef,
    pub exit_block: BlockRef,
    pub block_order: Vec<BlockRef>,
    pub instr_to_block: Vec<BlockRef>,
    pub preds: Vec<Vec<EdgeRef>>,
    pub succs: Vec<Vec<EdgeRef>>,
    pub reachable_blocks: BTreeSet<BlockRef>,
}

/// 边的稳定引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct EdgeRef(pub usize);

impl EdgeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for EdgeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// block 的稳定引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct BlockRef(pub usize);

impl BlockRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for BlockRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// 一个 basic block。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Default)]
pub struct BasicBlock {
    pub kind: BlockKind,
    pub instrs: InstrRange,
}

/// block 的类别。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Default)]
pub enum BlockKind {
    #[default]
    Normal,
    SyntheticExit,
}

/// 指令线性区间。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct InstrRange {
    pub start: InstrRef,
    pub len: usize,
}

impl InstrRange {
    pub const fn new(start: InstrRef, len: usize) -> Self {
        Self { start, len }
    }

    pub const fn end(self) -> usize {
        self.start.index() + self.len
    }

    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    pub const fn last(self) -> Option<InstrRef> {
        if self.len == 0 {
            None
        } else {
            Some(InstrRef(self.start.index() + self.len - 1))
        }
    }
}

impl Default for InstrRange {
    fn default() -> Self {
        Self::new(InstrRef(0), 0)
    }
}

/// CFG 边。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CfgEdge {
    pub from: BlockRef,
    pub to: BlockRef,
    pub kind: EdgeKind,
}

/// CFG 原生边类别。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum EdgeKind {
    Fallthrough,
    Jump,
    BranchTrue,
    BranchFalse,
    LoopBody,
    LoopExit,
    Return,
    TailCall,
}

impl Cfg {
    /// block 末尾指令通常决定了边形态，所以这里提供统一入口避免各层重复取尾。
    pub fn terminator<'a>(&self, instrs: &'a [LowInstr], block: BlockRef) -> Option<&'a LowInstr> {
        self.blocks
            .get(block.index())
            .and_then(|basic_block| basic_block.instrs.last())
            .and_then(|instr| instrs.get(instr.index()))
    }

    /// 读取 branch block 的真假边。
    ///
    /// 这个查询只依赖 CFG 边的 kind，不应散在 Structure/HIR 各自维护一份 helper。
    pub fn branch_edges(&self, block: BlockRef) -> Option<(EdgeRef, EdgeRef)> {
        let succs = &self.succs[block.index()];
        if succs.len() != 2 {
            return None;
        }

        let then_edge = succs
            .iter()
            .find(|edge_ref| matches!(self.edges[edge_ref.index()].kind, EdgeKind::BranchTrue))?;
        let else_edge = succs
            .iter()
            .find(|edge_ref| matches!(self.edges[edge_ref.index()].kind, EdgeKind::BranchFalse))?;

        Some((*then_edge, *else_edge))
    }

    /// 返回去重后的 reachable successors。
    pub fn reachable_successors(&self, block: BlockRef) -> Vec<BlockRef> {
        let mut succs = self.succs[block.index()]
            .iter()
            .map(|edge_ref| self.edges[edge_ref.index()].to)
            .filter(|succ| self.reachable_blocks.contains(succ))
            .collect::<Vec<_>>();
        succs.sort();
        succs.dedup();
        succs
    }

    /// 返回去重后的 reachable predecessors。
    pub fn reachable_predecessors(&self, block: BlockRef) -> Vec<BlockRef> {
        let mut preds = self.preds[block.index()]
            .iter()
            .map(|edge_ref| self.edges[edge_ref.index()].from)
            .filter(|pred| self.reachable_blocks.contains(pred))
            .collect::<Vec<_>>();
        preds.sort();
        preds.dedup();
        preds
    }

    /// 如果 block 只有一个 reachable successor，返回它。
    pub fn unique_reachable_successor(&self, block: BlockRef) -> Option<BlockRef> {
        let mut successors = self.succs[block.index()]
            .iter()
            .map(|edge_ref| self.edges[edge_ref.index()].to)
            .filter(|succ| self.reachable_blocks.contains(succ));
        let succ = successors.next()?;
        if successors.next().is_none() {
            Some(succ)
        } else {
            None
        }
    }

    pub fn can_reach(&self, from: BlockRef, to: BlockRef) -> bool {
        self.can_reach_within(from, to, &self.reachable_blocks)
    }

    pub fn can_reach_within(
        &self,
        from: BlockRef,
        to: BlockRef,
        allowed_blocks: &BTreeSet<BlockRef>,
    ) -> bool {
        if from == to {
            return true;
        }

        let mut visited = BTreeSet::new();
        let mut worklist = VecDeque::from([from]);

        while let Some(block) = worklist.pop_front() {
            if !self.reachable_blocks.contains(&block)
                || !allowed_blocks.contains(&block)
                || !visited.insert(block)
            {
                continue;
            }

            for edge_ref in &self.succs[block.index()] {
                let succ = self.edges[edge_ref.index()].to;
                if succ == to {
                    return true;
                }
                if allowed_blocks.contains(&succ) {
                    worklist.push_back(succ);
                }
            }
        }

        false
    }
}
