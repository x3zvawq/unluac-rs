//! 这个文件承载 short-circuit 提取时共用的 CFG 辅助规则。
//!
//! 比如线性跟随、真值边翻译、无环检查都同时服务 branch-exit 和 value-merge 两类
//! 候选；把它们集中起来可以避免两个 pass 各自养一套近似状态机。
//!
//! 它依赖 CFG / GraphFacts 已提供的图查询与 low 指令分类，只表达短路提取
//! 两边都共享的“小规则”，不会越权判断最终源码语法。
//!
//! 例子：
//! - `LinearFollowCtx` 会沿着只剩 jump/fallthrough 的垫片 block 继续跟到下一个判断头
//! - `truthy_falsy_targets` 会把 branch 的真假边统一翻成短路里的 truthy/falsy 目标
//! - `short_circuit_nodes_are_acyclic` 会挡住有环图，避免后层再替结构层兜底

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DominatorTree};
use crate::transformer::{LowInstr, LoweredProto, ResultPack};

use super::super::common::{
    BranchCandidate, ShortCircuitCandidate, ShortCircuitNode, ShortCircuitNodeRef,
    ShortCircuitTarget,
};
use super::super::helpers::is_reducible_region;

pub(super) fn prefer_short_circuit_candidate(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &ShortCircuitCandidate,
    existing: &ShortCircuitCandidate,
) -> bool {
    short_circuit_candidate_score(proto, cfg, candidate)
        > short_circuit_candidate_score(proto, cfg, existing)
}

fn short_circuit_candidate_score(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &ShortCircuitCandidate,
) -> (usize, usize, usize, usize) {
    (
        candidate.blocks.len(),
        candidate.nodes.len(),
        debug_line_coherence(proto, cfg, candidate),
        usize::MAX - candidate.header.index(),
    )
}

/// 行号只在两个候选已经通过相同语义校验且覆盖规模相同时参与排序。
///
/// 同一源码短路表达式的相邻判断通常共享行号；缺失的行号不产生奖励也不产生惩罚，
/// 因而不会改变 CFG membership、phi 或 transfer，只替代最后的任意 block-id 裁决。
fn debug_line_coherence(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &ShortCircuitCandidate,
) -> usize {
    candidate
        .nodes
        .windows(2)
        .filter(|nodes| {
            let lhs = block_line_hint(proto, cfg, nodes[0].header);
            let rhs = block_line_hint(proto, cfg, nodes[1].header);
            lhs.is_some() && lhs == rhs
        })
        .count()
}

fn block_line_hint(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> Option<u32> {
    let instrs = cfg.blocks.get(block.index())?.instrs;
    (instrs.start.index()..instrs.end())
        .rev()
        .find_map(|index| proto.lowering_map.line_hints.get(index).copied().flatten())
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
        mut is_terminal: impl FnMut(BlockRef) -> bool,
    ) -> Option<LinearFollowResult> {
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
                return Some(LinearFollowResult {
                    target: LinearFollowTarget::Header(current),
                    traversed: visited,
                });
            }

            let successor = self.cfg.unique_reachable_successor(current);
            if is_terminal(current) {
                return Some(LinearFollowResult {
                    target: LinearFollowTarget::Terminal(current),
                    traversed: visited,
                });
            }

            match successor {
                Some(succ) if block_is_passthrough(self.proto, self.cfg, current) => current = succ,
                _ => return None,
            }
        }
    }
}

pub(super) struct LinearFollowResult {
    pub(super) target: LinearFollowTarget,
    pub(super) traversed: BTreeSet<BlockRef>,
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
    let (truthy, falsy) = cfg.predicate_edges(&proto.instrs, header)?;
    Some((cfg.edges[truthy.index()].to, cfg.edges[falsy.index()].to))
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

pub(super) fn block_is_passthrough(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
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
