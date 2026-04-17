use std::collections::VecDeque;

use super::*;

pub(super) fn compute_phi_candidates(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    defs: &[Def],
    live_in: &[BTreeSet<Reg>],
    block_out: &[FixedState],
    fixed_def_lookup: &[FixedDefLookup],
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
                            fixed_def_lookup,
                        )
                    {
                        phi_blocks.insert(frontier_block);
                        placed_phis.insert(frontier_block, candidate);
                        changed = true;
                    }

                    if !block_defines_reg(cfg, frontier_block, reg, fixed_def_lookup) {
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
    fixed_def_lookup: &[FixedDefLookup],
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

        let ancestor = nearest_def_or_phi_ancestor(
            cfg,
            graph_facts,
            phi_blocks,
            fixed_def_lookup,
            pred,
            reg,
            block,
        );

        distinct_sources.insert(PredSource {
            reaching_defs,
            ancestor,
        });

        incoming.push(PhiIncoming {
            pred,
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

/// 从 `pred` 沿 dominator 链向上查找最近的 def-block 或 phi-block，二者以先遇到的
/// 为准（这也是该 pred 在值语义上“当前 SSA 名”的来源）。`exclude` 用于跳过正在考
/// 虑的 frontier_block 自身，避免自引用。若整条链都没有 def/phi，返回 None，表示
/// 该 pred 来自入口。
fn nearest_def_or_phi_ancestor(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    phi_blocks: &BTreeSet<BlockRef>,
    fixed_def_lookup: &[FixedDefLookup],
    pred: BlockRef,
    reg: Reg,
    exclude: BlockRef,
) -> Option<AncestorKind> {
    let parents = &graph_facts.dominator_tree.parent;
    let mut cursor = Some(pred);
    while let Some(node) = cursor {
        if node != exclude {
            if block_defines_reg(cfg, node, reg, fixed_def_lookup) {
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

fn block_defines_reg(
    cfg: &Cfg,
    block: BlockRef,
    reg: Reg,
    fixed_def_lookup: &[FixedDefLookup],
) -> bool {
    let Some(mut instr_indices) = super::instr_indices(cfg, block) else {
        return false;
    };

    instr_indices.any(|instr_index| fixed_def_lookup[instr_index].defines(reg))
}
