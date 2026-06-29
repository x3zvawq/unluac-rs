use std::collections::VecDeque;

use super::*;

pub(super) fn compute_phi_candidates(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    defs: &[Def],
    live_in: &[BTreeSet<Reg>],
    block_out: &[FixedState],
) -> Vec<PhiCandidate> {
    let mut def_blocks = BTreeMap::<Reg, BTreeSet<BlockRef>>::new();
    for def in defs {
        if cfg.reachable_blocks.contains(&def.block) {
            def_blocks.entry(def.reg).or_default().insert(def.block);
        }
    }

    let mut phi_candidates = Vec::new();

    for (reg, blocks) in def_blocks {
        // 经典 Cytron 算法用 def-based 迭代去放 phi：从 reg 的 def blocks 出发沿
        // 支配边界扩散，把每个放过 phi 的 frontier_block 当作“pseudo-def”再继续扩散。
        // 这里需要做两次循环：外层保留已放 phi 的集合，内层每轮都用这个集合重新尝试
        // 之前拒绝掉的 frontier，因为一条 pred 其实已经被上游 phi 合过一次的情形只有
        // 在 phi 集合收敛之后才能完整识别。否则就会漏掉“直接 def 与 phi 合流”这种
        // 只看 reaching defs 看不出差别、但值语义上是两个来源的 block。
        let mut phi_blocks = BTreeSet::<BlockRef>::new();
        let mut placed_phis = BTreeMap::<BlockRef, PhiCandidate>::new();

        loop {
            let mut placed = BTreeSet::new();
            let mut worklist = blocks.iter().copied().collect::<VecDeque<_>>();
            worklist.extend(phi_blocks.iter().copied());
            let mut changed = false;

            while let Some(block) = worklist.pop_front() {
                for frontier_block in graph_facts.dominance_frontier_blocks(block) {
                    if !live_in[frontier_block.index()].contains(&reg)
                        || !placed.insert(frontier_block)
                    {
                        continue;
                    }

                    if !phi_blocks.contains(&frontier_block)
                        && let Some(candidate) = build_phi_candidate(
                            cfg,
                            graph_facts,
                            frontier_block,
                            reg,
                            block_out,
                            &phi_blocks,
                            &blocks,
                        )
                    {
                        phi_blocks.insert(frontier_block);
                        placed_phis.insert(frontier_block, candidate);
                        changed = true;
                    }

                    if !blocks.contains(&frontier_block) {
                        worklist.push_back(frontier_block);
                    }
                }
            }

            if !changed {
                break;
            }
        }

        phi_candidates.extend(placed_phis.into_values());
    }

    add_entry_header_loop_phi_candidates(cfg, graph_facts, live_in, block_out, &mut phi_candidates);

    phi_candidates.sort_by_key(|candidate| (candidate.block, candidate.reg));
    for (index, candidate) in phi_candidates.iter_mut().enumerate() {
        candidate.id = PhiId(index);
    }
    phi_candidates
}

/// 某个 pred 对 phi 贡献的“来源身份”。
///
/// SSA phi 的放置依据是：这个 block 的所有 pred 是否带来了“不同的 SSA 值”。经典
/// def-based 迭代 DF 算法只看每条 pred 的 reaching defs 是否不同，这会漏掉一种形状：
/// 当一条 pred 的值沿途经过某个更早的 phi 合过一次时，它与另一条由直接 def 到达的
/// pred 在值语义上属于两个不同 SSA 名，但底层 reaching defs 可能完全相同（这种情况
/// 下老算法会误判为“单一来源”拒绝放 phi）。我们同时用两种信号：
/// 1) reaching defs —— 捕获“经过 CFG 不同路径带来不同原始 def”的常规形状；
///
/// 2) 从 pred 沿 dominator 链向上走找到的第一个 def-block 或 phi-block —— 捕获
///    “沿途是否被更早的 phi 合流过”这层 SSA 名信息。
///
/// 只要两条 pred 在任一信号上不同，就视为两个来源。
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
struct PredSource {
    /// pred block_out 中 reg 的 reaching defs（升序去重）。空集合代表 entry。
    reaching_defs: Vec<DefId>,
    /// 从 pred 沿 dominator 链向上找到的最近 def-block 或 phi-block。`None` 表示
    /// 没有任何 def/phi 支配这条 pred（即来自入口）。
    ancestor: Option<AncestorKind>,
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
enum AncestorKind {
    DefBlock(BlockRef),
    PhiBlock(BlockRef),
}

fn build_phi_candidate(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    block: BlockRef,
    reg: Reg,
    block_out: &[FixedState],
    phi_blocks: &BTreeSet<BlockRef>,
    def_blocks: &BTreeSet<BlockRef>,
) -> Option<PhiCandidate> {
    let mut incoming = Vec::new();
    let mut distinct_sources = BTreeSet::<PredSource>::new();

    for edge_ref in &cfg.preds[block.index()] {
        let pred = cfg.edges[edge_ref.index()].from;
        if !cfg.reachable_blocks.contains(&pred) {
            continue;
        }

        let defs = block_out
            .get(pred.index())
            .map(|defs_by_reg| defs_by_reg.get(reg))?
            .clone();

        let mut reaching_defs: Vec<DefId> = defs.iter().copied().collect();
        reaching_defs.sort();

        let ancestor =
            nearest_def_or_phi_ancestor(graph_facts, phi_blocks, def_blocks, pred, block);

        distinct_sources.insert(PredSource {
            reaching_defs,
            ancestor,
        });

        incoming.push(PhiIncoming {
            pred: Some(pred),
            defs: defs.iter().copied().collect(),
        });
    }

    if incoming.len() < 2 || distinct_sources.len() < 2 {
        return None;
    }

    incoming.sort_by_key(|incoming| incoming.pred);
    Some(PhiCandidate {
        id: PhiId(0),
        block,
        reg,
        incoming,
    })
}

/// 函数入口块本身作为 loop header 时，没有真实 preheader edge 能代表“入函数初值”。
/// 对这种形状，普通 def-frontier phi 放置只能看到回边 defs，后续 HIR 会把 header
/// 条件读到的寄存器判成多来源 unresolved。这里补一条 entry pseudo-incoming，形成
/// “entry 初值 + loop backedge defs”的 header phi，让 loop state 恢复在结构层完成。
fn add_entry_header_loop_phi_candidates(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    live_in: &[BTreeSet<Reg>],
    block_out: &[FixedState],
    phi_candidates: &mut Vec<PhiCandidate>,
) {
    let header = cfg.entry_block;
    if !cfg.reachable_blocks.contains(&header) {
        return;
    }

    let loop_blocks = graph_facts
        .natural_loops
        .iter()
        .filter(|natural_loop| natural_loop.header == header)
        .flat_map(|natural_loop| natural_loop.blocks.iter().copied())
        .collect::<BTreeSet<_>>();
    if loop_blocks.is_empty() {
        return;
    }

    let existing = phi_candidates
        .iter()
        .filter(|candidate| candidate.block == header)
        .map(|candidate| candidate.reg)
        .collect::<BTreeSet<_>>();

    for &reg in &live_in[header.index()] {
        if existing.contains(&reg) {
            continue;
        }

        let mut incoming = vec![PhiIncoming {
            pred: None,
            defs: BTreeSet::new(),
        }];
        let mut has_backedge_def = false;

        for edge_ref in &cfg.preds[header.index()] {
            let pred = cfg.edges[edge_ref.index()].from;
            if !cfg.reachable_blocks.contains(&pred) || !loop_blocks.contains(&pred) {
                continue;
            }

            let defs = block_out[pred.index()].get(reg).clone();
            has_backedge_def |= !defs.is_empty();
            incoming.push(PhiIncoming {
                pred: Some(pred),
                defs: defs.iter().copied().collect(),
            });
        }

        if has_backedge_def && incoming.len() >= 2 {
            incoming.sort_by_key(|incoming| incoming.pred);
            phi_candidates.push(PhiCandidate {
                id: PhiId(0),
                block: header,
                reg,
                incoming,
            });
        }
    }
}

/// 从 `pred` 沿 dominator 链向上查找最近的 def-block 或 phi-block，二者以先遇到的
/// 为准（这也是该 pred 在值语义上“当前 SSA 名”的来源）。`exclude` 用于跳过正在考
/// 虑的 frontier_block 自身，避免自引用。若整条链都没有 def/phi，返回 None，表示
/// 该 pred 来自入口。
fn nearest_def_or_phi_ancestor(
    graph_facts: &GraphFacts,
    phi_blocks: &BTreeSet<BlockRef>,
    def_blocks: &BTreeSet<BlockRef>,
    pred: BlockRef,
    exclude: BlockRef,
) -> Option<AncestorKind> {
    let parents = &graph_facts.dominator_tree.parent;
    let mut cursor = Some(pred);
    while let Some(node) = cursor {
        if node != exclude {
            if def_blocks.contains(&node) {
                return Some(AncestorKind::DefBlock(node));
            }
            if phi_blocks.contains(&node) {
                return Some(AncestorKind::PhiBlock(node));
            }
        }
        cursor = parents.get(node.index()).copied().flatten();
    }
    None
}
