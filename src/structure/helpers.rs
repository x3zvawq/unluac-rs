//! 这个文件放 StructureFacts 共享图辅助函数。
//!
//! 它们都只读 CFG / graph facts，不掺杂具体候选语义，目的是让 branch/loop/
//! short-circuit/scope 等模块共享一套稳定的小工具。
//!
//! 它依赖 CFG / GraphFacts 已经提供好的 block、edge、支配关系和可达性，只表达
//! “共享图查询”本身，不越权决定某个候选最终是不是 `if/while/and-or`。
//!
//! 例子：
//! - `collect_region_entry_edges` 会把“区域外进入区域内”的所有边统一收出来，供
//!   goto/irreducible 共用
//! - `collect_region_exit_edges` 会把“区域内流向区域外”的边统一收出来，供
//!   goto/region exit 共用
//! - `is_reducible_region` 会回答“除 header 外，区域内 block 是否只被区域内前驱进入”

use std::collections::{BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, DominatorTree, EdgeKind, EdgeRef};
use crate::transformer::{LowInstr, LoweredProto};

use super::common::IrreducibleRegion;

/// 返回共享的纯 terminal block 所代表的控制语义。
///
/// 这种 block 只有一条 Return/TailCall 指令；非自然边可以在源处执行 phi copy 后
/// 直接物化同一 terminal，而自然路径仍由该 block 的唯一 containment owner 发射。
pub(super) fn shared_pure_terminal_kind(cfg: &Cfg, block: BlockRef) -> Option<EdgeKind> {
    if cfg.preds.get(block.index())?.len() < 2 || cfg.blocks.get(block.index())?.instrs.len != 1 {
        return None;
    }
    let [edge] = cfg.succs.get(block.index())?.as_slice() else {
        return None;
    };
    let edge = cfg.edges.get(edge.index())?;
    (edge.to == cfg.exit_block && matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall))
        .then_some(edge.kind)
}

pub(super) fn block_has_non_control_prefix(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let Some(last_instr) = range
        .last()
        .and_then(|instr_ref| proto.instrs.get(instr_ref.index()))
    else {
        return false;
    };
    let body_end = if matches!(
        last_instr,
        LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::Return(_)
            | LowInstr::TailCall(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_)
    ) {
        range.end().saturating_sub(1)
    } else {
        range.end()
    };
    range.start.index() < body_end
}

pub(super) fn control_prefix_is_movable(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let body_end = range.last().map_or(range.end(), |last| {
        if proto.instrs[last.index()].is_control_terminator() {
            range.end() - 1
        } else {
            range.end()
        }
    });
    (range.start.index()..body_end).all(|index| {
        matches!(
            proto.instrs[index],
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadConst(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
        )
    })
}

/// `actual` 可以是直达 `expected` 所在 block 的单跳 pad；只穿透实际目标这一侧。
pub(super) fn same_or_transparent_jump_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    if actual == expected {
        return true;
    }
    let block = cfg.instr_to_block[actual.index()];
    let range = cfg.blocks[block.index()].instrs;
    range.len == 1
        && matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()]
                    == cfg.instr_to_block[expected.index()]
        )
}

pub(super) fn equivalent_single_return_targets(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    let block = cfg.instr_to_block[actual.index()];
    let expected_block = cfg.instr_to_block[expected.index()];
    cfg.blocks[block.index()].instrs.len == 1
        && cfg.blocks[expected_block.index()].instrs.len == 1
        && matches!(
            (
                cfg.terminator(&proto.instrs, block),
                cfg.terminator(&proto.instrs, expected_block),
            ),
            (Some(LowInstr::Return(actual)), Some(LowInstr::Return(expected)))
                if actual == expected
        )
}

pub(super) fn collect_region_exits(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> BTreeSet<BlockRef> {
    collect_region_exit_edges(cfg, blocks)
        .into_iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .collect()
}

pub(super) fn collect_region_entry_edges(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> Vec<EdgeRef> {
    let mut entry_edges: Vec<_> = blocks
        .iter()
        .flat_map(|block| cfg.preds[block.index()].iter())
        .filter(|edge_ref| {
            let edge = cfg.edges[edge_ref.index()];
            cfg.reachable_blocks.contains(&edge.from) && !blocks.contains(&edge.from)
        })
        .copied()
        .collect();
    entry_edges.sort();
    entry_edges.dedup();
    entry_edges
}

pub(super) fn collect_region_exit_edges(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> Vec<EdgeRef> {
    let mut exit_edges: Vec<_> = blocks
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .filter(|edge_ref| {
            let edge = cfg.edges[edge_ref.index()];
            cfg.reachable_blocks.contains(&edge.to) && !blocks.contains(&edge.to)
        })
        .copied()
        .collect();
    exit_edges.sort();
    exit_edges.dedup();
    exit_edges
}

pub(super) fn collect_forward_region_blocks(
    cfg: &Cfg,
    entries: impl IntoIterator<Item = BlockRef>,
    stop: Option<BlockRef>,
    dom_limit: Option<(BlockRef, &DominatorTree)>,
) -> BTreeSet<BlockRef> {
    let mut blocks = BTreeSet::new();
    let mut worklist = VecDeque::from_iter(entries);

    while let Some(block) = worklist.pop_front() {
        if Some(block) == stop
            || !cfg.reachable_blocks.contains(&block)
            || dom_limit.is_some_and(|(root, tree)| !tree.dominates(root, block))
            || !blocks.insert(block)
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if Some(succ) != stop {
                worklist.push_back(succ);
            }
        }
    }

    blocks
}

pub(super) fn collect_region_predecessors_to_target(
    cfg: &Cfg,
    blocks: &BTreeSet<BlockRef>,
    target: BlockRef,
) -> BTreeSet<BlockRef> {
    blocks
        .iter()
        .copied()
        .filter(|block| {
            cfg.succs[block.index()]
                .iter()
                .any(|edge_ref| cfg.edges[edge_ref.index()].to == target)
        })
        .collect()
}

/// 收集从 `entry` 出发到 `merge` 之间所有直接到达 `merge` 的前驱 block。
///
/// 不使用 entry 作为支配约束根——当条件表达式存在短路求值时，外层块可能有
/// 直接跳入 entry 后续区域的边，导致 entry 并不支配所有 then-arm 内的 block。
/// stop-at-merge 已经足够限制搜索范围，不会越界到 merge 之后。
pub(super) fn collect_merge_arm_preds(
    cfg: &Cfg,
    entry: BlockRef,
    merge: BlockRef,
) -> BTreeSet<BlockRef> {
    let blocks = collect_forward_region_blocks(cfg, [entry], Some(merge), None);
    collect_region_predecessors_to_target(cfg, &blocks, merge)
}

pub(super) fn is_reducible_region(
    cfg: &Cfg,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    blocks.iter().all(|block| {
        if *block == header {
            true
        } else {
            cfg.preds[block.index()].iter().all(|edge_ref| {
                let pred = cfg.edges[edge_ref.index()].from;
                !cfg.reachable_blocks.contains(&pred) || blocks.contains(&pred)
            })
        }
    })
}

pub(super) fn compute_irreducible_regions(
    cfg: &Cfg,
    graph_facts: &crate::structure::GraphFacts,
) -> Vec<IrreducibleRegion> {
    let mut irreducible_regions = Vec::new();
    for blocks in graph_facts.strongly_connected_components() {
        let Some(first) = blocks.first().copied() else {
            continue;
        };
        if !graph_facts.block_is_cyclic(first) {
            continue;
        }
        let component = blocks.iter().copied().collect::<BTreeSet<_>>();

        let entry_edges = collect_region_entry_edges(cfg, &component);
        let entry_targets = entry_edges
            .iter()
            .map(|edge_ref| cfg.edges[edge_ref.index()].to)
            .collect::<BTreeSet<_>>();
        if entry_targets.len() <= 1 {
            continue;
        }

        let Some(entry) = component.iter().copied().min() else {
            continue;
        };
        irreducible_regions.push(IrreducibleRegion {
            entry,
            blocks: component,
            entry_edges,
        });
    }

    irreducible_regions.sort_by_key(|region| region.entry);
    irreducible_regions
}
