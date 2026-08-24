//! 这个文件实现 CFG 之上的第一层图事实分析。
//!
//! 它只消费 CFG 的 block、edge 与可达性，使用正反向共享的非递归 DFS 和
//! Lengauer-Tarjan 算法建立支配树/后支配树，再推导 dominance frontier、backedge
//! 与按 header 合并的 natural loop；结构化 if/loop 的源码级判断仍然留给后续
//! StructureFacts。同一 header 的所有回边共用一次多源反向 worklist，不会按回边重复
//! 扫描前驱图。
//!
//! 例子：菱形 `entry -> then/else -> merge` 会产出 `idom(merge) = entry`，反向分析
//! 同一张图则产出两臂的共同后支配点 `merge`。这里不会因为该形状“像 if”就创建
//! branch 候选，也不会把不可达 block 接入任一支配树。

use std::collections::{BTreeSet, VecDeque};

use crate::structure::StructureError;

use super::common::{
    BlockRef, Cfg, CfgGraph, DominatorTree, EdgeRef, GraphFacts, NaturalLoop, NaturalLoopForest,
    PostDominatorTree,
};

struct DenseBlockSet {
    present: Vec<bool>,
}

#[derive(Clone, Copy)]
enum FlowDirection {
    Forward,
    Reverse,
}

impl FlowDirection {
    fn outgoing_edges(self, cfg: &Cfg, block: BlockRef) -> &[EdgeRef] {
        match self {
            Self::Forward => &cfg.succs[block.index()],
            Self::Reverse => &cfg.preds[block.index()],
        }
    }

    fn incoming_edges(self, cfg: &Cfg, block: BlockRef) -> &[EdgeRef] {
        match self {
            Self::Forward => &cfg.preds[block.index()],
            Self::Reverse => &cfg.succs[block.index()],
        }
    }

    fn edge_target(self, cfg: &Cfg, edge_ref: EdgeRef) -> BlockRef {
        let edge = cfg.edges[edge_ref.index()];
        match self {
            Self::Forward => edge.to,
            Self::Reverse => edge.from,
        }
    }

    fn incoming_source(self, cfg: &Cfg, edge_ref: EdgeRef) -> BlockRef {
        let edge = cfg.edges[edge_ref.index()];
        match self {
            Self::Forward => edge.from,
            Self::Reverse => edge.to,
        }
    }
}

struct DfsTraversal {
    preorder: Vec<BlockRef>,
    parent: Vec<Option<BlockRef>>,
    postorder: Vec<BlockRef>,
}

impl DenseBlockSet {
    fn new(block_count: usize) -> Self {
        Self {
            present: vec![false; block_count],
        }
    }

    fn from_blocks<I>(block_count: usize, blocks: I) -> Self
    where
        I: IntoIterator<Item = BlockRef>,
    {
        let mut set = Self::new(block_count);
        for block in blocks {
            set.present[block.index()] = true;
        }
        set
    }

    fn contains(&self, block: BlockRef) -> bool {
        self.present[block.index()]
    }

    fn insert(&mut self, block: BlockRef) -> bool {
        let slot = &mut self.present[block.index()];
        let inserted = !*slot;
        *slot = true;
        inserted
    }
}

struct GraphAnalysis {
    rpo: Vec<BlockRef>,
    dominator_tree: DominatorTree,
    post_dominator_tree: PostDominatorTree,
    dominance_frontier: Vec<BTreeSet<BlockRef>>,
    strongly_connected_components: Vec<Vec<BlockRef>>,
    cyclic_blocks: Vec<bool>,
    backedges: Vec<EdgeRef>,
    loop_headers: BTreeSet<BlockRef>,
    natural_loops: Vec<NaturalLoop>,
    natural_loop_forest: NaturalLoopForest,
}

impl GraphAnalysis {
    fn analyze(cfg: &Cfg) -> Result<Self, StructureError> {
        super::validate_cfg(cfg)?;
        let reachable =
            DenseBlockSet::from_blocks(cfg.blocks.len(), cfg.reachable_blocks.iter().copied());
        let forward =
            compute_dfs_traversal(cfg, cfg.entry_block, &reachable, FlowDirection::Forward);
        let dominator_tree = compute_dominator_tree(cfg, &forward)?;
        let strongly_connected_components =
            compute_strongly_connected_components(cfg, &forward.postorder, &reachable);
        let cyclic_blocks = compute_cyclic_blocks(cfg, &strongly_connected_components);
        let mut rpo = forward.postorder;
        rpo.reverse();
        let reverse_reachable = compute_reverse_reachable(cfg, &reachable);
        let reverse = compute_dfs_traversal(
            cfg,
            cfg.exit_block,
            &reverse_reachable,
            FlowDirection::Reverse,
        );
        let post_dominator_tree = compute_post_dominator_tree(cfg, &reverse)?;
        let dominance_frontier = compute_dominance_frontier(cfg, &dominator_tree, &reachable);
        let backedges = compute_backedges(cfg, &dominator_tree, &reachable);
        let loop_headers = compute_loop_headers(cfg, &backedges);
        let natural_loops = compute_natural_loops(cfg, &backedges, &reachable);
        let natural_loop_forest =
            NaturalLoopForest::build(&natural_loops, &dominator_tree, cfg.blocks.len());

        Ok(Self {
            rpo,
            dominator_tree,
            post_dominator_tree,
            dominance_frontier,
            strongly_connected_components,
            cyclic_blocks,
            backedges,
            loop_headers,
            natural_loops,
            natural_loop_forest,
        })
    }

    fn into_graph_facts(self, children: Vec<GraphFacts>) -> GraphFacts {
        GraphFacts {
            rpo: self.rpo,
            dominator_tree: self.dominator_tree,
            post_dominator_tree: self.post_dominator_tree,
            dominance_frontier: self.dominance_frontier,
            strongly_connected_components: self.strongly_connected_components,
            cyclic_blocks: self.cyclic_blocks,
            backedges: self.backedges,
            loop_headers: self.loop_headers,
            natural_loops: self.natural_loops,
            natural_loop_forest: self.natural_loop_forest,
            children,
        }
    }
}

fn compute_strongly_connected_components(
    cfg: &Cfg,
    postorder: &[BlockRef],
    reachable: &DenseBlockSet,
) -> Vec<Vec<BlockRef>> {
    let mut visited = DenseBlockSet::new(cfg.blocks.len());
    let mut components = Vec::new();
    let mut pending = Vec::new();

    for root in postorder.iter().rev().copied() {
        if !visited.insert(root) {
            continue;
        }
        let mut component = Vec::new();
        pending.push(root);
        while let Some(block) = pending.pop() {
            component.push(block);
            for edge_ref in &cfg.preds[block.index()] {
                let pred = cfg.edges[edge_ref.index()].from;
                if reachable.contains(pred) && visited.insert(pred) {
                    pending.push(pred);
                }
            }
        }
        component.sort_unstable();
        components.push(component);
    }

    components
}

fn compute_cyclic_blocks(cfg: &Cfg, components: &[Vec<BlockRef>]) -> Vec<bool> {
    let mut cyclic_blocks = vec![false; cfg.blocks.len()];
    for component in components {
        let cyclic = component.len() > 1
            || component.first().is_some_and(|block| {
                cfg.succs[block.index()]
                    .iter()
                    .any(|edge_ref| cfg.edges[edge_ref.index()].to == *block)
            });
        if cyclic {
            for block in component {
                cyclic_blocks[block.index()] = true;
            }
        }
    }
    cyclic_blocks
}

use crate::decompile::{DecompileContext, DecompileError, DecompileState};

/// GraphFacts 阶段入口：从 CFG 槽位读取图，写回稳定图事实。
pub(crate) fn analyze_graph_facts(
    state: &mut DecompileState,
    _context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let cfg = state.require_cfg()?;
    struct Frame<'a> {
        cfg: &'a CfgGraph,
        next_child: usize,
        children: Vec<GraphFacts>,
    }

    // The graph algorithms themselves are iterative over blocks.  Keep the proto
    // traversal iterative as well: a legal Luau flat table may contain 999 nested
    // child protos and must not consume the Rust call stack between those analyses.
    let mut stack = vec![Frame {
        cfg,
        next_child: 0,
        children: Vec::new(),
    }];
    let result = loop {
        let child = {
            let frame = stack.last_mut().expect("graph proto frame is non-empty");
            let child = frame.cfg.children.get(frame.next_child);
            if child.is_some() {
                frame.next_child += 1;
            }
            child
        };
        if let Some(child) = child {
            stack.push(Frame {
                cfg: child,
                next_child: 0,
                children: Vec::new(),
            });
            continue;
        }

        let frame = stack.pop().expect("graph proto frame is non-empty");
        let facts = GraphAnalysis::analyze(&frame.cfg.cfg)?.into_graph_facts(frame.children);
        if let Some(parent) = stack.last_mut() {
            parent.children.push(facts);
        } else {
            break facts;
        }
    };
    state.graph_facts = Some(result);
    Ok(())
}

fn compute_dominator_tree(
    cfg: &Cfg,
    traversal: &DfsTraversal,
) -> Result<DominatorTree, StructureError> {
    compute_tree(cfg, traversal, FlowDirection::Forward)
}

fn compute_post_dominator_tree(
    cfg: &Cfg,
    traversal: &DfsTraversal,
) -> Result<PostDominatorTree, StructureError> {
    let tree = compute_tree(cfg, traversal, FlowDirection::Reverse)?;

    Ok(PostDominatorTree {
        parent: tree.parent,
        children: tree.children,
        order: tree.order,
        preorder_index: tree.preorder_index,
        subtree_end: tree.subtree_end,
        depth: tree.depth,
        ancestors: tree.ancestors,
    })
}

fn compute_dominance_frontier(
    cfg: &Cfg,
    dom_tree: &DominatorTree,
    reachable: &DenseBlockSet,
) -> Vec<BTreeSet<BlockRef>> {
    let mut frontier = vec![BTreeSet::new(); cfg.blocks.len()];

    for block in dom_tree.order.iter().copied().rev() {
        for edge_ref in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge_ref.index()].to;
            if reachable.contains(successor) && dom_tree.parent[successor.index()] != Some(block) {
                frontier[block.index()].insert(successor);
            }
        }

        for child in &dom_tree.children[block.index()] {
            let inherited = frontier[child.index()]
                .iter()
                .copied()
                .filter(|member| dom_tree.parent[member.index()] != Some(block))
                .collect::<Vec<_>>();
            frontier[block.index()].extend(inherited);
        }
    }

    frontier
}

fn compute_backedges(
    cfg: &Cfg,
    dom_tree: &DominatorTree,
    reachable: &DenseBlockSet,
) -> Vec<EdgeRef> {
    cfg.edges
        .iter()
        .enumerate()
        .filter_map(|(index, edge)| {
            let edge_ref = EdgeRef(index);
            if reachable.contains(edge.from)
                && reachable.contains(edge.to)
                && dom_tree.dominates(edge.to, edge.from)
            {
                Some(edge_ref)
            } else {
                None
            }
        })
        .collect()
}

fn compute_loop_headers(cfg: &Cfg, backedges: &[EdgeRef]) -> BTreeSet<BlockRef> {
    backedges
        .iter()
        .copied()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .collect()
}

fn compute_natural_loops(
    cfg: &Cfg,
    backedges: &[EdgeRef],
    reachable: &DenseBlockSet,
) -> Vec<NaturalLoop> {
    let mut backedges_by_header = vec![Vec::new(); cfg.blocks.len()];
    for backedge in backedges.iter().copied() {
        let header = cfg.edges[backedge.index()].to;
        backedges_by_header[header.index()].push(backedge);
    }

    let mut visit_epoch = vec![0usize; cfg.blocks.len()];
    let mut epoch = 0usize;
    let mut worklist = VecDeque::new();
    let mut natural_loops = Vec::with_capacity(
        backedges_by_header
            .iter()
            .filter(|backedges| !backedges.is_empty())
            .count(),
    );

    for (header_index, grouped_backedges) in backedges_by_header.into_iter().enumerate() {
        if grouped_backedges.is_empty() {
            continue;
        }
        epoch = epoch.wrapping_add(1);
        if epoch == 0 {
            visit_epoch.fill(0);
            epoch = 1;
        }

        let header = BlockRef(header_index);
        let mut blocks = BTreeSet::from([header]);
        visit_epoch[header_index] = epoch;
        worklist.clear();
        for backedge in grouped_backedges.iter().copied() {
            let source = cfg.edges[backedge.index()].from;
            if visit_epoch[source.index()] == epoch {
                continue;
            }
            visit_epoch[source.index()] = epoch;
            blocks.insert(source);
            worklist.push_back(source);
        }

        while let Some(block) = worklist.pop_front() {
            for pred_edge in &cfg.preds[block.index()] {
                let pred = cfg.edges[pred_edge.index()].from;
                if !reachable.contains(pred) || visit_epoch[pred.index()] == epoch {
                    continue;
                }
                visit_epoch[pred.index()] = epoch;
                blocks.insert(pred);
                worklist.push_back(pred);
            }
        }

        natural_loops.push(NaturalLoop {
            header,
            backedges: grouped_backedges,
            blocks,
        });
    }
    natural_loops
}

fn compute_reverse_reachable(cfg: &Cfg, reachable: &DenseBlockSet) -> DenseBlockSet {
    let mut reverse_reachable = DenseBlockSet::new(cfg.blocks.len());
    let mut worklist = VecDeque::from([cfg.exit_block]);

    while let Some(block) = worklist.pop_front() {
        if !reverse_reachable.insert(block) {
            continue;
        }

        for edge_ref in &cfg.preds[block.index()] {
            let pred = cfg.edges[edge_ref.index()].from;
            if reachable.contains(pred) && !reverse_reachable.contains(pred) {
                worklist.push_back(pred);
            }
        }
    }

    reverse_reachable
}

fn compute_tree(
    cfg: &Cfg,
    traversal: &DfsTraversal,
    direction: FlowDirection,
) -> Result<DominatorTree, StructureError> {
    let block_count = cfg.blocks.len();
    let Some(root) = traversal.preorder.first().copied() else {
        return empty_dominator_tree(block_count);
    };

    let mut semi = vec![usize::MAX; block_count];
    let mut label = (0..block_count).map(BlockRef).collect::<Vec<_>>();
    for (number, block) in traversal.preorder.iter().copied().enumerate() {
        semi[block.index()] = number;
    }

    let mut ancestor = vec![None; block_count];
    let mut idom = vec![None; block_count];
    idom[root.index()] = Some(root);
    let mut buckets = vec![Vec::new(); block_count];
    let mut eval_path = Vec::with_capacity(block_count);

    for block in traversal.preorder.iter().copied().skip(1).rev() {
        for edge_ref in direction.incoming_edges(cfg, block) {
            let predecessor = direction.incoming_source(cfg, *edge_ref);
            if semi[predecessor.index()] == usize::MAX {
                continue;
            }

            let representative = eval(
                predecessor,
                &mut ancestor,
                &mut label,
                &semi,
                &mut eval_path,
            )?;
            semi[block.index()] = semi[block.index()].min(semi[representative.index()]);
        }

        let semi_dominator = traversal.preorder[semi[block.index()]];
        buckets[semi_dominator.index()].push(block);

        let Some(parent) = traversal.parent[block.index()] else {
            return Err(StructureError::invalid(format!(
                "non-root DFS block {block} has no traversal parent"
            )));
        };
        ancestor[block.index()] = Some(parent);

        while let Some(bucket_block) = buckets[parent.index()].pop() {
            let representative = eval(
                bucket_block,
                &mut ancestor,
                &mut label,
                &semi,
                &mut eval_path,
            )?;
            idom[bucket_block.index()] = Some(
                if semi[representative.index()] < semi[bucket_block.index()] {
                    representative
                } else {
                    parent
                },
            );
        }
    }

    for block in traversal.preorder.iter().copied().skip(1) {
        let semi_dominator = traversal.preorder[semi[block.index()]];
        if idom[block.index()] != Some(semi_dominator) {
            let Some(provisional) = idom[block.index()] else {
                return Err(StructureError::invalid(format!(
                    "reachable non-root block {block} has no provisional dominator"
                )));
            };
            let Some(final_parent) = idom[provisional.index()] else {
                return Err(StructureError::invalid(format!(
                    "provisional dominator {provisional} for {block} is unresolved"
                )));
            };
            idom[block.index()] = Some(final_parent);
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

    let order = collect_tree_order(root, &children);
    let (preorder_index, subtree_end) = tree_intervals(&parent, &order);
    let (depth, ancestors) = tree_lca_index(&parent, &order)?;

    Ok(DominatorTree {
        parent,
        children,
        order,
        preorder_index,
        subtree_end,
        depth,
        ancestors,
    })
}

fn empty_dominator_tree(block_count: usize) -> Result<DominatorTree, StructureError> {
    let parent = vec![None; block_count];
    let order = Vec::new();
    let (preorder_index, subtree_end) = tree_intervals(&parent, &order);
    let (depth, ancestors) = tree_lca_index(&parent, &order)?;
    Ok(DominatorTree {
        parent,
        children: vec![Vec::new(); block_count],
        order,
        preorder_index,
        subtree_end,
        depth,
        ancestors,
    })
}

fn eval(
    block: BlockRef,
    ancestor: &mut [Option<BlockRef>],
    label: &mut [BlockRef],
    semi: &[usize],
    path: &mut Vec<BlockRef>,
) -> Result<BlockRef, StructureError> {
    // 经典算法用递归 compress 更新祖先链。显式记录路径再逆序更新，既保持
    // “先压缩父节点、再比较父 label”的顺序，也不把 CFG 深度转成线程栈深度。
    path.clear();
    let mut current = block;
    while let Some(parent) = ancestor[current.index()] {
        if ancestor[parent.index()].is_none() {
            break;
        }
        path.push(current);
        current = parent;
    }

    for current in path.iter().copied().rev() {
        let Some(parent) = ancestor[current.index()] else {
            return Err(StructureError::invalid(format!(
                "compressed dominator path for {current} lost its parent"
            )));
        };
        let parent_label = label[parent.index()];
        if semi[parent_label.index()] < semi[label[current.index()].index()] {
            label[current.index()] = parent_label;
        }
        ancestor[current.index()] = ancestor[parent.index()];
    }

    Ok(label[block.index()])
}

fn tree_intervals(
    parent: &[Option<BlockRef>],
    order: &[BlockRef],
) -> (Vec<Option<usize>>, Vec<Option<usize>>) {
    let mut preorder_index = vec![None; parent.len()];
    let mut subtree_end = vec![None; parent.len()];
    for (index, block) in order.iter().copied().enumerate() {
        preorder_index[block.index()] = Some(index);
        subtree_end[block.index()] = Some(index + 1);
    }
    for block in order.iter().copied().rev() {
        let Some(parent) = parent[block.index()] else {
            continue;
        };
        subtree_end[parent.index()] = subtree_end[parent.index()].max(subtree_end[block.index()]);
    }
    (preorder_index, subtree_end)
}

type TreeLcaIndex = (Vec<Option<usize>>, Vec<Vec<Option<BlockRef>>>);

fn tree_lca_index(
    parent: &[Option<BlockRef>],
    order: &[BlockRef],
) -> Result<TreeLcaIndex, StructureError> {
    let mut depth = vec![None; parent.len()];
    for block in order.iter().copied() {
        depth[block.index()] = Some(
            parent[block.index()]
                .and_then(|parent| depth[parent.index()])
                .map_or(0, |parent_depth| parent_depth + 1),
        );
    }

    let mut ancestors = Vec::new();
    if !parent.is_empty() {
        ancestors.push(parent.to_vec());
    }
    while (1usize << ancestors.len()) < parent.len() {
        let Some(previous) = ancestors.last() else {
            return Err(StructureError::invalid(
                "non-empty dominator tree has no first ancestor level",
            ));
        };
        ancestors.push(
            previous
                .iter()
                .map(|ancestor| ancestor.and_then(|block| previous[block.index()]))
                .collect(),
        );
    }
    Ok((depth, ancestors))
}

fn collect_tree_order(root: BlockRef, children: &[Vec<BlockRef>]) -> Vec<BlockRef> {
    let mut order = Vec::with_capacity(children.len());
    let mut stack = Vec::with_capacity(children.len());
    stack.push(root);
    while let Some(block) = stack.pop() {
        order.push(block);
        stack.extend(children[block.index()].iter().rev().copied());
    }
    order
}

fn compute_dfs_traversal(
    cfg: &Cfg,
    root: BlockRef,
    visible: &DenseBlockSet,
    direction: FlowDirection,
) -> DfsTraversal {
    let block_count = cfg.blocks.len();
    let mut traversal = DfsTraversal {
        preorder: Vec::with_capacity(block_count),
        parent: vec![None; block_count],
        postorder: Vec::with_capacity(block_count),
    };
    if !visible.contains(root) {
        return traversal;
    }

    let mut visited = DenseBlockSet::new(block_count);
    let mut stack = Vec::with_capacity(block_count);
    visited.insert(root);
    traversal.preorder.push(root);
    stack.push((root, 0));

    while !stack.is_empty() {
        let top = stack.len() - 1;
        let (block, edge_index) = stack[top];
        let outgoing = direction.outgoing_edges(cfg, block);
        if edge_index == outgoing.len() {
            traversal.postorder.push(block);
            stack.pop();
            continue;
        }

        stack[top].1 += 1;
        let successor = direction.edge_target(cfg, outgoing[edge_index]);
        if visible.contains(successor) && visited.insert(successor) {
            traversal.parent[successor.index()] = Some(block);
            traversal.preorder.push(successor);
            stack.push((successor, 0));
        }
    }

    traversal
}
