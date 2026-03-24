//! 这个文件放 StructureFacts 共享图辅助函数。
//!
//! 它们都只读 CFG / graph facts，不掺杂具体候选语义，目的是让 branch/loop/
//! short-circuit/scope 等模块共享一套稳定的小工具。

use std::collections::{BTreeSet, VecDeque};

use crate::cfg::{BlockRef, Cfg, EdgeKind, EdgeRef};

/// 不可规约区域的共享描述。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct IrreducibleRegion {
    pub entry: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry_edges: Vec<EdgeRef>,
}

pub(super) fn collect_region_exits(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> BTreeSet<BlockRef> {
    let mut exits = BTreeSet::new();

    for block in blocks {
        for edge_ref in &cfg.succs[block.index()] {
            let edge = cfg.edges[edge_ref.index()];
            if cfg.reachable_blocks.contains(&edge.to) && !blocks.contains(&edge.to) {
                exits.insert(edge.to);
            }
        }
    }

    exits
}

pub(super) fn branch_edges(cfg: &Cfg, block: BlockRef) -> Option<(&EdgeRef, &EdgeRef)> {
    let succs = &cfg.succs[block.index()];
    if succs.len() != 2 {
        return None;
    }

    let then_edge = succs
        .iter()
        .find(|edge_ref| matches!(cfg.edges[edge_ref.index()].kind, EdgeKind::BranchTrue))?;
    let else_edge = succs
        .iter()
        .find(|edge_ref| matches!(cfg.edges[edge_ref.index()].kind, EdgeKind::BranchFalse))?;

    Some((then_edge, else_edge))
}

pub(super) fn nearest_common_postdom(
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

pub(super) fn dominates(parent: &[Option<BlockRef>], dom: BlockRef, mut block: BlockRef) -> bool {
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

pub(super) fn can_reach(cfg: &Cfg, from: BlockRef, to: BlockRef) -> bool {
    if from == to {
        return true;
    }

    let mut visited = BTreeSet::new();
    let mut worklist = VecDeque::from([from]);

    while let Some(block) = worklist.pop_front() {
        if !cfg.reachable_blocks.contains(&block) || !visited.insert(block) {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let succ = cfg.edges[edge_ref.index()].to;
            if succ == to {
                return true;
            }
            worklist.push_back(succ);
        }
    }

    false
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

            for edge_ref in &cfg.preds[cursor.index()] {
                let pred = cfg.edges[edge_ref.index()].from;
                if cfg.reachable_blocks.contains(&pred) && pred != cfg.exit_block {
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

        let entry_edges = component_entry_edges(cfg, &component);
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

fn component_entry_edges(cfg: &Cfg, blocks: &BTreeSet<BlockRef>) -> Vec<EdgeRef> {
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

fn has_self_loop(cfg: &Cfg, block: BlockRef) -> bool {
    cfg.succs[block.index()]
        .iter()
        .any(|edge_ref| cfg.edges[edge_ref.index()].to == block)
}
