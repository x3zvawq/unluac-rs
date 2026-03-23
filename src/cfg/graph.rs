//! 这个文件实现 CFG 之上的第一层图事实分析。
//!
//! 这里故意只回答“图上发生了什么”，例如支配、回边和 natural loop；
//! 结构化 if/loop 的源码级判断仍然留给后续 StructureFacts。

use std::collections::{BTreeSet, VecDeque};

use super::common::{
    BlockRef, Cfg, CfgGraph, DominatorTree, EdgeRef, GraphFacts, NaturalLoop, PostDominatorTree,
};

/// 对整个 CFG 树递归计算图事实。
pub fn analyze_graph_facts(cfg: &CfgGraph) -> GraphFacts {
    GraphFacts {
        rpo: compute_rpo(&cfg.cfg),
        dominator_tree: compute_dominator_tree(&cfg.cfg),
        post_dominator_tree: compute_post_dominator_tree(&cfg.cfg),
        dominance_frontier: compute_dominance_frontier(&cfg.cfg),
        backedges: compute_backedges(&cfg.cfg),
        loop_headers: compute_loop_headers(&cfg.cfg),
        natural_loops: compute_natural_loops(&cfg.cfg),
        children: cfg.children.iter().map(analyze_graph_facts).collect(),
    }
}

fn compute_rpo(cfg: &Cfg) -> Vec<BlockRef> {
    if !cfg.reachable_blocks.contains(&cfg.entry_block) {
        return Vec::new();
    }

    let mut visited = BTreeSet::new();
    let mut postorder = Vec::new();
    dfs_postorder(
        cfg,
        cfg.entry_block,
        &cfg.reachable_blocks,
        &mut visited,
        &mut postorder,
    );
    postorder.reverse();
    postorder
}

fn compute_dominator_tree(cfg: &Cfg) -> DominatorTree {
    let rpo = compute_rpo(cfg);
    compute_tree(cfg, &rpo, cfg.entry_block, false)
}

fn compute_post_dominator_tree(cfg: &Cfg) -> PostDominatorTree {
    let reverse_reachable = compute_reverse_reachable(cfg);
    let rpo = compute_reverse_rpo(cfg, &reverse_reachable);
    let tree = compute_tree(cfg, &rpo, cfg.exit_block, true);

    PostDominatorTree {
        parent: tree.parent,
        children: tree.children,
        order: tree.order,
    }
}

fn compute_dominance_frontier(cfg: &Cfg) -> Vec<BTreeSet<BlockRef>> {
    let dom_tree = compute_dominator_tree(cfg);
    let mut frontier = vec![BTreeSet::new(); cfg.blocks.len()];

    for block in cfg
        .reachable_blocks
        .iter()
        .copied()
        .filter(|block| cfg.preds[block.index()].len() >= 2)
    {
        let Some(block_parent) = dom_tree.parent[block.index()] else {
            continue;
        };

        for edge_ref in &cfg.preds[block.index()] {
            let mut runner = cfg.edges[edge_ref.index()].from;

            while runner != block_parent {
                frontier[runner.index()].insert(block);
                let Some(next_runner) = dom_tree.parent[runner.index()] else {
                    break;
                };
                runner = next_runner;
            }
        }
    }

    frontier
}

fn compute_backedges(cfg: &Cfg) -> Vec<EdgeRef> {
    let dom_tree = compute_dominator_tree(cfg);

    cfg.edges
        .iter()
        .enumerate()
        .filter_map(|(index, edge)| {
            let edge_ref = EdgeRef(index);
            if cfg.reachable_blocks.contains(&edge.from)
                && cfg.reachable_blocks.contains(&edge.to)
                && dominates(&dom_tree.parent, edge.to, edge.from)
            {
                Some(edge_ref)
            } else {
                None
            }
        })
        .collect()
}

fn compute_loop_headers(cfg: &Cfg) -> BTreeSet<BlockRef> {
    compute_backedges(cfg)
        .into_iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .collect()
}

fn compute_natural_loops(cfg: &Cfg) -> Vec<NaturalLoop> {
    let backedges = compute_backedges(cfg);

    backedges
        .into_iter()
        .map(|backedge| {
            let edge = cfg.edges[backedge.index()];
            let mut blocks = BTreeSet::from([edge.to]);
            let mut worklist = VecDeque::new();

            if edge.from != edge.to {
                blocks.insert(edge.from);
                worklist.push_back(edge.from);
            }

            while let Some(block) = worklist.pop_front() {
                for pred_edge in &cfg.preds[block.index()] {
                    let pred = cfg.edges[pred_edge.index()].from;
                    if cfg.reachable_blocks.contains(&pred) && blocks.insert(pred) {
                        worklist.push_back(pred);
                    }
                }
            }

            NaturalLoop {
                header: edge.to,
                backedge,
                blocks,
            }
        })
        .collect()
}

fn compute_reverse_reachable(cfg: &Cfg) -> BTreeSet<BlockRef> {
    let mut reverse_reachable = BTreeSet::new();
    let mut worklist = VecDeque::from([cfg.exit_block]);

    while let Some(block) = worklist.pop_front() {
        if !reverse_reachable.insert(block) {
            continue;
        }

        for edge_ref in &cfg.preds[block.index()] {
            let pred = cfg.edges[edge_ref.index()].from;
            if cfg.reachable_blocks.contains(&pred) && !reverse_reachable.contains(&pred) {
                worklist.push_back(pred);
            }
        }
    }

    reverse_reachable
}

fn compute_reverse_rpo(cfg: &Cfg, reverse_reachable: &BTreeSet<BlockRef>) -> Vec<BlockRef> {
    if !reverse_reachable.contains(&cfg.exit_block) {
        return Vec::new();
    }

    let mut visited = BTreeSet::new();
    let mut postorder = Vec::new();
    dfs_reverse_postorder(
        cfg,
        cfg.exit_block,
        reverse_reachable,
        &mut visited,
        &mut postorder,
    );
    postorder.reverse();
    postorder
}

fn compute_tree(cfg: &Cfg, rpo: &[BlockRef], root: BlockRef, reverse: bool) -> DominatorTree {
    let mut position = vec![None; cfg.blocks.len()];
    for (index, block) in rpo.iter().copied().enumerate() {
        position[block.index()] = Some(index);
    }

    let mut idom = vec![None; cfg.blocks.len()];
    if position[root.index()].is_some() {
        idom[root.index()] = Some(root);
    }

    let mut changed = true;
    while changed {
        changed = false;

        for block in rpo.iter().copied().filter(|block| *block != root) {
            let mut incoming = incoming_blocks(cfg, block, reverse)
                .into_iter()
                .filter(|pred| idom[pred.index()].is_some());

            let Some(first) = incoming.next() else {
                continue;
            };
            let mut new_idom = first;

            for pred in incoming {
                new_idom = intersect(&idom, &position, pred, new_idom);
            }

            if idom[block.index()] != Some(new_idom) {
                idom[block.index()] = Some(new_idom);
                changed = true;
            }
        }
    }

    let mut parent = vec![None; cfg.blocks.len()];
    let mut children = vec![Vec::new(); cfg.blocks.len()];

    for (index, maybe_idom) in idom.into_iter().enumerate() {
        let block = BlockRef(index);
        let Some(idom_block) = maybe_idom else {
            continue;
        };
        if block == root {
            continue;
        }

        parent[index] = Some(idom_block);
        children[idom_block.index()].push(block);
    }

    let mut order = Vec::new();
    if position[root.index()].is_some() {
        collect_tree_order(root, &children, &mut order);
    }

    DominatorTree {
        parent,
        children,
        order,
    }
}

fn incoming_blocks(cfg: &Cfg, block: BlockRef, reverse: bool) -> Vec<BlockRef> {
    let edge_refs = if reverse {
        &cfg.succs[block.index()]
    } else {
        &cfg.preds[block.index()]
    };

    edge_refs
        .iter()
        .map(|edge_ref| {
            let edge = cfg.edges[edge_ref.index()];
            if reverse { edge.to } else { edge.from }
        })
        .collect()
}

fn intersect(
    idom: &[Option<BlockRef>],
    position: &[Option<usize>],
    mut finger_a: BlockRef,
    mut finger_b: BlockRef,
) -> BlockRef {
    while finger_a != finger_b {
        while position[finger_a.index()] > position[finger_b.index()] {
            finger_a =
                idom[finger_a.index()].expect("dominator walk should stay inside computed tree");
        }

        while position[finger_b.index()] > position[finger_a.index()] {
            finger_b =
                idom[finger_b.index()].expect("dominator walk should stay inside computed tree");
        }
    }

    finger_a
}

fn collect_tree_order(block: BlockRef, children: &[Vec<BlockRef>], order: &mut Vec<BlockRef>) {
    order.push(block);
    for child in &children[block.index()] {
        collect_tree_order(*child, children, order);
    }
}

fn dominates(parent: &[Option<BlockRef>], dom: BlockRef, mut block: BlockRef) -> bool {
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

fn dfs_postorder(
    cfg: &Cfg,
    block: BlockRef,
    visible: &BTreeSet<BlockRef>,
    visited: &mut BTreeSet<BlockRef>,
    postorder: &mut Vec<BlockRef>,
) {
    if !visible.contains(&block) || !visited.insert(block) {
        return;
    }

    for edge_ref in &cfg.succs[block.index()] {
        let edge = cfg.edges[edge_ref.index()];
        dfs_postorder(cfg, edge.to, visible, visited, postorder);
    }

    postorder.push(block);
}

fn dfs_reverse_postorder(
    cfg: &Cfg,
    block: BlockRef,
    visible: &BTreeSet<BlockRef>,
    visited: &mut BTreeSet<BlockRef>,
    postorder: &mut Vec<BlockRef>,
) {
    if !visible.contains(&block) || !visited.insert(block) {
        return;
    }

    for edge_ref in &cfg.preds[block.index()] {
        let edge = cfg.edges[edge_ref.index()];
        dfs_reverse_postorder(cfg, edge.from, visible, visited, postorder);
    }

    postorder.push(block);
}
