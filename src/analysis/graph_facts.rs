//! 通用 CFG 图论分析：支配树、后支配树、支配边界、SCC（不可规约检测）与自然循环嵌套树。
//!
//! 消费 `Cfg` 快照并复用 `analysis::graph` 的 Lengauer-Tarjan 支配树与强连通分量分析。

use std::collections::BTreeSet;

use super::AnalysisError;
use super::cfg::{BlockId, Cfg, EdgeId};
use super::graph::{DominatorTree, depth_first, dominator_tree, strongly_connected_components};

/// 强连通分量（仅记录非平凡环：块数 > 1 或含自环）。
#[derive(Debug, Clone)]
pub struct SccInfo {
    pub blocks: BTreeSet<BlockId>,
    /// 从分量外部进入该分量的所有不同目标块；len > 1 即不可规约多入口环。
    pub entries: Vec<BlockId>,
}

impl SccInfo {
    pub fn is_irreducible(&self) -> bool {
        self.entries.len() > 1
    }
}

/// 以唯一 header 为根的自然循环。
#[derive(Debug, Clone)]
pub struct NaturalLoop {
    pub id: usize,
    pub header: BlockId,
    pub blocks: BTreeSet<BlockId>,
    pub backedges: Vec<EdgeId>,
    pub exits: Vec<EdgeId>,
    pub parent: Option<usize>,
    pub depth: usize,
}

/// 单个 proto 的图论事实。
pub struct GraphFacts {
    pub(crate) dom: DominatorTree<BlockId>,
    pub(crate) postdom: DominatorTree<BlockId>,
    pub dom_frontier: Vec<Vec<BlockId>>,
    pub sccs: Vec<SccInfo>,
    pub natural_loops: Vec<NaturalLoop>,
    /// 按入口基本块索引的自然循环 ID 列表（同入口多层循环按外层优先排序），O(1) 查询。
    pub loops_by_header_index: Vec<Vec<usize>>,
    /// 按最内层优先排序的自然循环索引列表。
    pub loops_innermost_first: Vec<usize>,
}

impl GraphFacts {
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        self.dom.dominates(a, b, BlockId::index)
    }

    pub fn strictly_dominates(&self, a: BlockId, b: BlockId) -> bool {
        a != b && self.dominates(a, b)
    }

    pub fn postdominates(&self, a: BlockId, b: BlockId) -> bool {
        self.postdom.dominates(a, b, BlockId::index)
    }

    /// 两个基本块的最近公共后支配点（若任一方陷入永不返回循环则返回 `None`）。
    pub fn nearest_common_postdom(&self, mut a: BlockId, mut b: BlockId) -> Option<BlockId> {
        self.postdom.preorder_index[a.index()]?;
        self.postdom.preorder_index[b.index()]?;
        while a != b {
            if self.postdominates(a, b) {
                return Some(a);
            }
            if self.postdominates(b, a) {
                return Some(b);
            }
            a = self.postdom.parent[a.index()]?;
            // 交替向上走一步或直接走 a 直到支配 b
            let _ = &mut b;
        }
        Some(a)
    }

    /// 两个基本块的最近公共支配点。
    pub fn nearest_common_dom(&self, mut a: BlockId, b: BlockId) -> Option<BlockId> {
        self.dom.preorder_index[a.index()]?;
        self.dom.preorder_index[b.index()]?;
        while !self.dominates(a, b) {
            a = self.dom.parent[a.index()]?;
        }
        Some(a)
    }

    /// 检查给定基本块是否属于某个不可规约多入口 SCC。
    pub fn is_in_irreducible_scc(&self, block: BlockId) -> bool {
        self.sccs
            .iter()
            .any(|scc| scc.is_irreducible() && scc.blocks.contains(&block))
    }

    pub fn loop_by_header(&self, header: BlockId) -> Option<&NaturalLoop> {
        self.loops_by_header_index
            .get(header.index())
            .and_then(|ids| ids.first())
            .map(|&id| &self.natural_loops[id])
    }

    /// 返回以 `header` 为入口的全部自然循环（同一入口若存在严格嵌套的多层循环，按外层优先排序）。
    pub fn loops_by_header(&self, header: BlockId) -> impl Iterator<Item = &NaturalLoop> {
        self.loops_by_header_index
            .get(header.index())
            .map(Vec::as_slice)
            .unwrap_or(&[])
            .iter()
            .map(|&id| &self.natural_loops[id])
    }
}

pub(crate) fn compute_graph_facts(proto_id: usize, cfg: &Cfg) -> Result<GraphFacts, AnalysisError> {
    let n = cfg.blocks.len();

    // 1. 正向 DFS 与支配树
    let fwd_dfs = depth_first(
        n,
        cfg.entry_block,
        BlockId::index,
        |b| cfg.is_reachable(b),
        |b| cfg.succ_blocks(b).collect::<Vec<_>>(),
    );
    let dom = dominator_tree(&fwd_dfs, BlockId::index, BlockId, |b| {
        cfg.pred_blocks(b)
            .filter(|&p| cfg.is_reachable(p))
            .collect::<Vec<_>>()
    })
    .map_err(|detail| AnalysisError::DominatorFailure {
        proto: proto_id,
        detail,
    })?;

    // 2. 反向 DFS 与后支配树（从虚拟 exit_block 出发）
    let rev_dfs = depth_first(
        n,
        cfg.exit_block,
        BlockId::index,
        |b| cfg.is_reachable(b),
        |b| cfg.pred_blocks(b).collect::<Vec<_>>(),
    );
    let postdom = dominator_tree(&rev_dfs, BlockId::index, BlockId, |b| {
        cfg.succ_blocks(b)
            .filter(|&s| cfg.is_reachable(s))
            .collect::<Vec<_>>()
    })
    .map_err(|detail| AnalysisError::DominatorFailure {
        proto: proto_id,
        detail,
    })?;

    // 3. 支配边界（Cytron 线性算法）
    // 注意：entry_block 隐含一条来自函数调用入口的边 START -> entry_block；
    // 当 entry_block 作为循环头拥有至少一条回边前驱时，回边前驱到根的整条支配链都以
    // entry_block 为支配边界，这样才能正确插入参数/跨迭代变量的 Phi！
    let mut df_sets: Vec<BTreeSet<BlockId>> = vec![BTreeSet::new(); n];
    for &b in &cfg.block_order {
        let preds: Vec<BlockId> = cfg.reachable_preds(b).map(|e| e.from).collect();
        if b == cfg.entry_block {
            if !preds.is_empty() {
                for pred in preds {
                    let mut runner = pred;
                    loop {
                        df_sets[runner.index()].insert(b);
                        let Some(next) = dom.parent[runner.index()] else {
                            break;
                        };
                        runner = next;
                    }
                }
            }
            continue;
        }
        if preds.len() < 2 {
            continue;
        }
        let Some(idom_b) = dom.parent[b.index()] else {
            continue;
        };
        for pred in preds {
            let mut runner = pred;
            while runner != idom_b {
                df_sets[runner.index()].insert(b);
                let Some(next) = dom.parent[runner.index()] else {
                    break;
                };
                runner = next;
            }
        }
    }
    let dom_frontier = df_sets
        .into_iter()
        .map(|s| s.into_iter().collect())
        .collect();

    // 4. 强连通分量与不可规约环检测
    let raw_sccs = strongly_connected_components(n, &fwd_dfs.postorder, BlockId::index, |b| {
        cfg.pred_blocks(b)
            .filter(|&p| cfg.is_reachable(p))
            .collect::<Vec<_>>()
    });
    let mut sccs = Vec::new();
    for comp in raw_sccs {
        let is_cycle = comp.len() > 1
            || comp
                .first()
                .is_some_and(|&b| cfg.succ_blocks(b).any(|s| s == b));
        if !is_cycle {
            continue;
        }
        let blocks: BTreeSet<BlockId> = comp.into_iter().collect();
        let mut entries = BTreeSet::new();
        for &b in &blocks {
            if b == cfg.entry_block
                || cfg
                    .reachable_preds(b)
                    .any(|edge| !blocks.contains(&edge.from))
            {
                entries.insert(b);
            }
        }
        sccs.push(SccInfo {
            blocks,
            entries: entries.into_iter().collect(),
        });
    }

    // 5. 自然循环（合并同 header 的非显式 for 协议回边）
    // 显式 NumericFor / GenericFor 协议回边由 `loop_protocols` 专职结构化，
    // 不混入通用自然循环，避免在 for 循环体里误套一层 `while true` 或干扰同 header 的内层 while。
    let mut protocol_backedges: BTreeSet<(BlockId, BlockId)> = BTreeSet::new();
    for hint in &cfg.loop_protocols {
        match hint {
            super::cfg::LoopProtocolHint::NumericFor {
                body_entry,
                latch_blocks,
                ..
            } => {
                for &latch in latch_blocks {
                    protocol_backedges.insert((latch, *body_entry));
                }
            }
            super::cfg::LoopProtocolHint::GenericFor {
                header_block,
                ..
            } => {
                // `EdgeKind::LoopBody` 已在下方过滤；此处仅排除循环体跳回 `header_block` 的协议回边，
                // 避免像 `while ... do for k in xs do break end end` 中 `body_entry == exit_block == 外层 header`
                // 时把 `LoopExit` 误排除出外层自然循环！
                for pred in cfg.reachable_preds(*header_block) {
                    if dom.dominates(*header_block, pred.from, BlockId::index) {
                        protocol_backedges.insert((pred.from, *header_block));
                    }
                }
            }
        }
    }

    let mut backedges_by_header: Vec<Vec<EdgeId>> = vec![Vec::new(); n];
    for edge in &cfg.edges {
        if cfg.is_reachable(edge.from)
            && dom.dominates(edge.to, edge.from, BlockId::index)
            && edge.kind != super::cfg::EdgeKind::LoopBody
            && !protocol_backedges.contains(&(edge.from, edge.to))
        {
            backedges_by_header[edge.to.index()].push(edge.id);
        }
    }

    let mut natural_loops = Vec::new();
    for &header in &cfg.block_order {
        let backedges = &backedges_by_header[header.index()];
        if backedges.is_empty() {
            continue;
        }
        // 为同一 header 的每条回边分别计算其单回边自然循环块集；
        // 若两条回边的块集不可比或相等则合并为同一循环；若严格真包含（如共享入口的嵌套 repeat/while），
        // 保留为独立的内/外层自然循环（按块集从大到小即外层优先排列）。
        let mut groups: Vec<(BTreeSet<BlockId>, Vec<EdgeId>)> = Vec::with_capacity(backedges.len());
        for &eid in backedges {
            let mut blocks = BTreeSet::new();
            blocks.insert(header);
            let src = cfg.edges[eid.index()].from;
            let mut worklist = Vec::new();
            if blocks.insert(src) {
                worklist.push(src);
            }
            while let Some(node) = worklist.pop() {
                for edge in cfg.reachable_preds(node) {
                    if blocks.insert(edge.from) {
                        worklist.push(edge.from);
                    }
                }
            }
            groups.push((blocks, vec![eid]));
        }

        // 合并相等或互不包含（非严格嵌套）的回边组，直到同 header 下全部循环形成严格嵌套链。
        // 重要不变量：若较小组 `inner` 严格真包含于较大组 `outer`，但 `header` 本身存在直接离开 `outer`
        // 且非返回块的退出边（例如 `while cond do if ... then continue end; ... end` 中 `continue` 的回边），
        // 则 `inner` 只是 `outer` 的 `continue` 捷径回边而非独立内层循环，必须合并进 `outer`！
        let header_exits_outside = |outer: &BTreeSet<BlockId>| -> bool {
            cfg.succs[header.index()].iter().any(|&eid| {
                let e = cfg.edges[eid.index()];
                !matches!(e.kind, super::cfg::EdgeKind::Return | super::cfg::EdgeKind::TailCall)
                    && e.to != cfg.exit_block
                    && !outer.contains(&e.to)
                    && !matches!(
                        cfg.succs[e.to.index()].as_slice(),
                        [seid] if matches!(
                            cfg.edges[seid.index()].kind,
                            super::cfg::EdgeKind::Return | super::cfg::EdgeKind::TailCall
                        )
                    )
            })
        };
        loop {
            let mut merged_pair: Option<(usize, usize)> = None;
            'outer: for i in 0..groups.len() {
                for j in (i + 1)..groups.len() {
                    let a = &groups[i].0;
                    let b = &groups[j].0;
                    let strictly_nested = (a.len() < b.len()
                        && a.is_subset(b)
                        && !header_exits_outside(b))
                        || (b.len() < a.len() && b.is_subset(a) && !header_exits_outside(a));
                    if !strictly_nested {
                        merged_pair = Some((i, j));
                        break 'outer;
                    }
                }
            }
            if let Some((i, j)) = merged_pair {
                let (b_blocks, b_edges) = groups.remove(j);
                groups[i].0.extend(b_blocks);
                groups[i].1.extend(b_edges);
            } else {
                break;
            }
        }

        // 外层（块集更大）排在前面，便于结构化器从外到内逐层展开共享入口的嵌套循环。
        groups.sort_by_key(|g| std::cmp::Reverse(g.0.len()));

        for (loop_blocks, group_backedges) in groups {
            let mut exits = Vec::new();
            for &b in &loop_blocks {
                for &eid in &cfg.succs[b.index()] {
                    let target = cfg.edges[eid.index()].to;
                    if !loop_blocks.contains(&target) {
                        exits.push(eid);
                    }
                }
            }
            let id = natural_loops.len();
            natural_loops.push(NaturalLoop {
                id,
                header,
                blocks: loop_blocks,
                backedges: group_backedges,
                exits,
                parent: None,
                depth: 0,
            });
        }
    }

    // 构建循环嵌套父子关系与深度：按基本块反查包含其 header 的候选外层循环，避免顺序多循环 O(L²) 两两比对。
    let loop_count = natural_loops.len();
    let mut loops_containing_block: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut loops_by_header_index: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (j, nl) in natural_loops.iter().enumerate() {
        loops_by_header_index[nl.header.index()].push(j);
        for &b in &nl.blocks {
            loops_containing_block[b.index()].push(j);
        }
    }
    for i in 0..loop_count {
        let mut best_parent: Option<(usize, usize)> = None;
        let header_i = natural_loops[i].header;
        for &j in &loops_containing_block[header_i.index()] {
            if i == j {
                continue;
            }
            if natural_loops[j].blocks.len() > natural_loops[i].blocks.len()
                && natural_loops[i].blocks.is_subset(&natural_loops[j].blocks)
            {
                let size = natural_loops[j].blocks.len();
                if best_parent.is_none_or(|(_, best_size)| size < best_size) {
                    best_parent = Some((j, size));
                }
            }
        }
        natural_loops[i].parent = best_parent.map(|(p, _)| p);
    }
    for i in 0..loop_count {
        let mut depth = 0usize;
        let mut cur = natural_loops[i].parent;
        while let Some(p) = cur {
            depth += 1;
            cur = natural_loops[p].parent;
        }
        natural_loops[i].depth = depth;
    }

    let mut loops_innermost_first: Vec<usize> = (0..loop_count).collect();
    loops_innermost_first.sort_by(|&a, &b| {
        natural_loops[b]
            .depth
            .cmp(&natural_loops[a].depth)
            .then_with(|| natural_loops[a].blocks.len().cmp(&natural_loops[b].blocks.len()))
            .then_with(|| natural_loops[a].header.cmp(&natural_loops[b].header))
    });

    Ok(GraphFacts {
        dom,
        postdom,
        dom_frontier,
        sccs,
        natural_loops,
        loops_by_header_index,
        loops_innermost_first,
    })
}
