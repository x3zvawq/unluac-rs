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

use crate::cfg::{BlockRef, Cfg, DominatorTree, EdgeRef};

use super::common::IrreducibleRegion;

pub(super) fn collect_region_exits(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> BTreeSet<BlockRef> {
    collect_region_exit_edges(cfg, blocks)
        .into_iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .collect()
}

pub(super) fn collect_region_entry_edges(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> Vec<EdgeRef> {
    let mut entry_edges = Vec::new();

    for block in blocks {
        for edge_ref in &cfg.preds[block.index()] {
            let edge = cfg.edges[edge_ref.index()];
            if cfg.reachable_blocks.contains(&edge.from) && !blocks.contains(&edge.from) {
                entry_edges.push(*edge_ref);
            }
        }
    }

    entry_edges.sort();
    entry_edges.dedup();
    entry_edges
}

pub(super) fn collect_region_exit_edges(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> Vec<EdgeRef> {
    let mut exit_edges = Vec::new();

    for block in blocks {
        for edge_ref in &cfg.succs[block.index()] {
            let edge = cfg.edges[edge_ref.index()];
            if cfg.reachable_blocks.contains(&edge.to) && !blocks.contains(&edge.to) {
                exit_edges.push(*edge_ref);
            }
        }
    }

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
            || !blocks.insert(block)
            || dom_limit.is_some_and(|(root, tree)| !tree.dominates(root, block))
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

pub(super) fn collect_merge_arm_preds(
    cfg: &Cfg,
    dom_tree: &DominatorTree,
    entry: BlockRef,
    merge: BlockRef,
) -> BTreeSet<BlockRef> {
    let blocks = collect_forward_region_blocks(cfg, [entry], Some(merge), Some((entry, dom_tree)));
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

pub(super) fn compute_irreducible_regions(cfg: &Cfg) -> Vec<IrreducibleRegion> {
    let real_blocks = cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| cfg.reachable_blocks.contains(block))
        .collect::<Vec<_>>();

    let order = kosaraju_postorder(cfg, &real_blocks);
    let mut visited = BTreeSet::new();
    let mut components = Vec::new();

    for block in order.into_iter().rev() {
        if visited.contains(&block) {
            continue;
        }

        let mut component = BTreeSet::new();
        let mut worklist = VecDeque::from([block]);
        while let Some(cursor) = worklist.pop_front() {
            if !visited.insert(cursor) {
                continue;
            }
            component.insert(cursor);

            for pred in cfg.reachable_predecessors(cursor) {
                if pred != cfg.exit_block {
                    worklist.push_back(pred);
                }
            }
        }

        components.push(component);
    }

    let mut irreducible_regions = Vec::new();
    for component in components {
        if component.len() == 1
            && !has_self_loop(cfg, *component.iter().next().unwrap_or(&cfg.entry_block))
        {
            continue;
        }

        let entry_edges = collect_region_entry_edges(cfg, &component);
        if entry_edges.len() <= 1 {
            continue;
        }

        let entry = component
            .iter()
            .copied()
            .min()
            .expect("irreducible component should not be empty");
        irreducible_regions.push(IrreducibleRegion {
            entry,
            blocks: component,
            entry_edges,
        });
    }

    irreducible_regions.sort_by_key(|region| region.entry);
    irreducible_regions
}

fn kosaraju_postorder(cfg: &Cfg, blocks: &[BlockRef]) -> Vec<BlockRef> {
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();

    for block in blocks {
        dfs_postorder(cfg, *block, &mut visited, &mut order);
    }

    order
}

fn dfs_postorder(
    cfg: &Cfg,
    block: BlockRef,
    visited: &mut BTreeSet<BlockRef>,
    order: &mut Vec<BlockRef>,
) {
    if !cfg.reachable_blocks.contains(&block) || !visited.insert(block) {
        return;
    }

    for edge_ref in &cfg.succs[block.index()] {
        let succ = cfg.edges[edge_ref.index()].to;
        if succ != cfg.exit_block {
            dfs_postorder(cfg, succ, visited, order);
        }
    }

    order.push(block);
}

fn has_self_loop(cfg: &Cfg, block: BlockRef) -> bool {
    cfg.succs[block.index()]
        .iter()
        .any(|edge_ref| cfg.edges[edge_ref.index()].to == block)
}
