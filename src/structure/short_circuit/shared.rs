//! 这个文件承载 short-circuit 提取时共用的 CFG 辅助规则。
//!
//! 比如线性跟随、真值边翻译、无环检查都同时服务 branch-exit 和 value-merge 两类
//! 候选；把它们集中起来可以避免两个 pass 各自养一套近似状态机。
//!
//! 它依赖 CFG / GraphFacts / Dataflow 已提供的图查询和写寄存器事实，只表达短路提取
//! 两边都共享的“小规则”，不会越权判断最终源码语法。
//!
//! 例子：
//! - `LinearFollowCtx` 会沿着只剩 jump/fallthrough 的垫片 block 继续跟到下一个判断头
//! - `truthy_falsy_targets` 会把 branch 的真假边统一翻成短路里的 truthy/falsy 目标
//! - `short_circuit_nodes_are_acyclic` 会挡住有环图，避免后层再替结构层兜底

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, DataflowFacts, DominatorTree};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg, ResultPack};

use super::super::common::{
    BranchCandidate, ShortCircuitCandidate, ShortCircuitNode, ShortCircuitNodeRef,
    ShortCircuitTarget,
};
use super::super::helpers::is_reducible_region;

pub(super) fn prefer_short_circuit_candidate(
    candidate: &ShortCircuitCandidate,
    existing: &ShortCircuitCandidate,
) -> bool {
    short_circuit_candidate_score(candidate) > short_circuit_candidate_score(existing)
}

fn short_circuit_candidate_score(candidate: &ShortCircuitCandidate) -> (usize, usize, usize) {
    (
        candidate.blocks.len(),
        candidate.nodes.len(),
        usize::MAX - candidate.header.index(),
    )
}

pub(super) struct LinearFollowCtx<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) branch_by_header: &'a BTreeMap<BlockRef, &'a BranchCandidate>,
    pub(super) dom_tree: &'a DominatorTree,
    pub(super) root: BlockRef,
}

impl<'a> LinearFollowCtx<'a> {
    pub(super) fn follow(
        &self,
        start: BlockRef,
        mut extra_valid: impl FnMut(BlockRef) -> bool,
        mut is_terminal: impl FnMut(BlockRef, &[BlockRef]) -> bool,
    ) -> Option<LinearFollowTarget> {
        let mut current = start;
        let mut visited = BTreeSet::new();

        loop {
            if current == self.cfg.exit_block
                || !self.cfg.reachable_blocks.contains(&current)
                || !self.dom_tree.dominates(self.root, current)
                || !extra_valid(current)
                || !visited.insert(current)
            {
                return None;
            }

            if self.branch_by_header.contains_key(&current) {
                return Some(LinearFollowTarget::Header(current));
            }

            let succs = self.cfg.reachable_successors(current);
            if is_terminal(current, succs.as_slice()) {
                return Some(LinearFollowTarget::Terminal(current));
            }

            match succs.as_slice() {
                [succ] if block_is_passthrough(self.proto, self.cfg, current) => current = *succ,
                _ => return None,
            }
        }
    }
}

pub(super) enum LinearFollowTarget {
    Header(BlockRef),
    Terminal(BlockRef),
}

pub(super) fn truthy_falsy_targets(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    let (then_edge_ref, else_edge_ref) = cfg.branch_edges(header)?;
    let then_target = cfg.edges[then_edge_ref.index()].to;
    let else_target = cfg.edges[else_edge_ref.index()].to;

    match cfg.terminator(&proto.instrs, header) {
        Some(LowInstr::Branch(instr)) if instr.cond.negated => Some((else_target, then_target)),
        Some(LowInstr::Branch(_)) => Some((then_target, else_target)),
        _ => None,
    }
}

pub(super) fn block_writes_reg(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range
        .last()
        .and_then(|last| {
            matches!(proto.instrs.get(last.index()), Some(LowInstr::Jump(_)))
                .then_some(range.end().saturating_sub(1))
        })
        .unwrap_or_else(|| range.end());

    (range.start.index()..end).any(|instr_index| {
        dataflow
            .instr_def_for_reg(InstrRef(instr_index), reg)
            .is_some()
    })
}

pub(super) fn short_circuit_nodes_are_acyclic(
    nodes: &[ShortCircuitNode],
    entry: ShortCircuitNodeRef,
) -> bool {
    if nodes.is_empty() || entry.index() >= nodes.len() {
        return false;
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum VisitState {
        Unvisited,
        Visiting,
        Done,
    }

    let mut states = vec![VisitState::Unvisited; nodes.len()];
    let mut stack = vec![(entry, false)];

    while let Some((node_ref, expanded)) = stack.pop() {
        let Some(node) = nodes.get(node_ref.index()) else {
            return false;
        };

        if expanded {
            states[node_ref.index()] = VisitState::Done;
            continue;
        }

        match states[node_ref.index()] {
            VisitState::Done => continue,
            VisitState::Visiting => return false,
            VisitState::Unvisited => {
                states[node_ref.index()] = VisitState::Visiting;
                stack.push((node_ref, true));
            }
        }

        for target in [&node.truthy, &node.falsy] {
            let ShortCircuitTarget::Node(next_ref) = target else {
                continue;
            };
            match states[next_ref.index()] {
                VisitState::Done => {}
                VisitState::Visiting => return false,
                VisitState::Unvisited => stack.push((*next_ref, false)),
            }
        }
    }

    true
}

fn block_is_passthrough(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    match range.len {
        0 => true,
        1 => matches!(
            proto.instrs.get(range.start.index()),
            Some(LowInstr::Jump(_))
        ),
        _ => false,
    }
}

/// 如果 block 内含有 结果数为 0（`ResultPack::Ignore`）的 `Call` 指令，则返回 true。
/// 这类调用只有副作用、不产生返回值，block 不能被当作纯值叶子节点，
/// 否则调用副作用会在 `x and expr` 表达式中静默丢失。
pub(super) fn block_has_ignore_call(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    (range.start.index()..range.end()).any(|i| match proto.instrs.get(i) {
        Some(LowInstr::Call(c)) => matches!(c.results, ResultPack::Ignore),
        _ => false,
    })
}

pub(super) fn is_reducible_candidate(
    cfg: &Cfg,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    is_reducible_region(cfg, header, blocks)
}
