//! 从 CFG 构建共享 GraphFacts。
//!
//! 发布支配、后支配、SCC、回边和自然循环关系，源码结构候选由后续分析持有。

use std::collections::{BTreeSet, VecDeque};

use crate::graph::{self, DfsTraversal};
use crate::structure::StructureError;

use super::common::{
    BlockRef, Cfg, CfgGraph, DominatorTree, EdgeRef, GraphFacts, NaturalLoop, NaturalLoopForest,
    PostDominatorTree, SccFacts, SccId,
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
}

struct GraphAnalysis {
    rpo: Vec<BlockRef>,
    dominator_tree: DominatorTree,
    post_dominator_tree: PostDominatorTree,
    dominance_frontier: Vec<BTreeSet<BlockRef>>,
    scc: SccFacts,
    backedges: Vec<EdgeRef>,
    natural_loops: Vec<NaturalLoop>,
    natural_loop_forest: NaturalLoopForest,
}

impl GraphAnalysis {
    fn analyze(cfg: &Cfg) -> Result<Self, StructureError> {
        super::validate_cfg(cfg)?;
        let reachable =
            DenseBlockSet::from_blocks(cfg.blocks.len(), cfg.reachable_blocks.iter().copied());
        let forward = compute_dfs_traversal(
            cfg,
            cfg.entry_block,
            |block| reachable.contains(block),
            FlowDirection::Forward,
        );
        let dominator_tree = compute_dominator_tree(cfg, &forward)?;
        let scc = compute_strongly_connected_components(cfg, &forward.postorder)?;
        let mut rpo = forward.postorder;
        rpo.reverse();
        let reverse = compute_dfs_traversal(
            cfg,
            cfg.exit_block,
            // 无正常退出路径时仍保留 exit 根；其余节点必须属于入口可达域。
            |block| block == cfg.exit_block || reachable.contains(block),
            FlowDirection::Reverse,
        );
        let post_dominator_tree = compute_post_dominator_tree(cfg, &reverse)?;
        let dominance_frontier = compute_dominance_frontier(cfg, &dominator_tree, &reachable);
        let backedges = compute_backedges(cfg, &dominator_tree, &reachable);
        let natural_loops = compute_natural_loops(cfg, &backedges, &reachable);
        let natural_loop_forest =
            NaturalLoopForest::build(&natural_loops, &dominator_tree, cfg.blocks.len());

        Ok(Self {
            rpo,
            dominator_tree,
            post_dominator_tree,
            dominance_frontier,
            scc,
            backedges,
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
            scc: self.scc,
            backedges: self.backedges,
            natural_loops: self.natural_loops,
            natural_loop_forest: self.natural_loop_forest,
            children,
        }
    }
}

fn compute_strongly_connected_components(
    cfg: &Cfg,
    postorder: &[BlockRef],
) -> Result<SccFacts, StructureError> {
    let mut components = graph::strongly_connected_components(
        cfg.blocks.len(),
        postorder,
        BlockRef::index,
        |block| {
            cfg.preds[block.index()]
                .iter()
                .map(|edge| cfg.edges[edge.index()].from)
        },
    );
    for component in &mut components {
        component.sort_unstable();
    }
    let mut block_scc = vec![None; cfg.blocks.len()];
    let mut cyclic = Vec::with_capacity(components.len());
    for (index, component) in components.iter().enumerate() {
        cyclic.push(
            component.len() > 1
                || component.first().is_some_and(|block| {
                    cfg.succs[block.index()]
                        .iter()
                        .any(|edge_ref| cfg.edges[edge_ref.index()].to == *block)
                }),
        );
        for block in component {
            block_scc[block.index()] = Some(SccId(index));
        }
    }
    let mut predecessors = vec![Vec::new(); components.len()];
    for edge in &cfg.edges {
        let (Some(from), Some(to)) = (block_scc[edge.from.index()], block_scc[edge.to.index()])
        else {
            continue;
        };
        if from == to {
            continue;
        }
        // Kosaraju 的第二轮按第一轮逆完成序访问反图，先产出源 SCC；此不变量是
        // 下游拓扑范围裁剪的前提，不能把任意 SCC 编号误作可达性证明。
        if from > to {
            return Err(StructureError::invalid(
                "SCC condensation violates topological order",
            ));
        }
        predecessors[to.index()].push(from);
    }
    for preds in &mut predecessors {
        preds.sort_unstable();
        preds.dedup();
    }
    Ok(SccFacts {
        components,
        block_scc,
        cyclic,
        predecessors,
    })
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
    traversal: &DfsTraversal<BlockRef>,
) -> Result<DominatorTree, StructureError> {
    compute_tree(cfg, traversal, FlowDirection::Forward)
}

fn compute_post_dominator_tree(
    cfg: &Cfg,
    traversal: &DfsTraversal<BlockRef>,
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

fn compute_natural_loops(
    cfg: &Cfg,
    backedges: &[EdgeRef],
    reachable: &DenseBlockSet,
) -> Vec<NaturalLoop> {
    if backedges.is_empty() {
        return Vec::new();
    }
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

fn compute_tree(
    cfg: &Cfg,
    traversal: &DfsTraversal<BlockRef>,
    direction: FlowDirection,
) -> Result<DominatorTree, StructureError> {
    let tree = graph::dominator_tree(traversal, BlockRef::index, BlockRef, |block| {
        direction
            .incoming_edges(cfg, block)
            .iter()
            .map(move |&edge| direction.incoming_source(cfg, edge))
    })
    .map_err(StructureError::invalid)?;
    let (depth, ancestors) = tree_lca_index(&tree.parent, &tree.order);
    Ok(DominatorTree {
        parent: tree.parent,
        children: tree.children,
        order: tree.order,
        preorder_index: tree.preorder_index,
        subtree_end: tree.subtree_end,
        depth,
        ancestors,
    })
}

type TreeLcaIndex = (Vec<Option<usize>>, Vec<Vec<Option<BlockRef>>>);

fn tree_lca_index(parent: &[Option<BlockRef>], order: &[BlockRef]) -> TreeLcaIndex {
    let mut depth = vec![None; parent.len()];
    for block in order.iter().copied() {
        depth[block.index()] = Some(
            parent[block.index()]
                .and_then(|parent| depth[parent.index()])
                .map_or(0, |parent_depth| parent_depth + 1),
        );
    }

    let mut ancestors = Vec::new();
    while (1usize << (ancestors.len() + 1)) < parent.len() {
        let previous = ancestors.last().map_or(parent, Vec::as_slice);
        ancestors.push(
            previous
                .iter()
                .map(|ancestor| ancestor.and_then(|block| previous[block.index()]))
                .collect(),
        );
    }
    (depth, ancestors)
}

fn compute_dfs_traversal(
    cfg: &Cfg,
    root: BlockRef,
    visible: impl Fn(BlockRef) -> bool,
    direction: FlowDirection,
) -> DfsTraversal<BlockRef> {
    graph::depth_first(cfg.blocks.len(), root, BlockRef::index, visible, |block| {
        direction
            .outgoing_edges(cfg, block)
            .iter()
            .map(move |&edge| direction.edge_target(cfg, edge))
    })
}
