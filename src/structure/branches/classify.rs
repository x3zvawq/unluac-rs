//! 分类 if/else、guard、透明跳转与 soft merge；依赖 CFG 后支配事实，不负责候选细化；例如为无显式 merge 的终止 arm 找到局部软合流。

use super::*;

pub(super) fn classify_if_else_branch(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BranchCandidate> {
    let merge = graph_facts.nearest_common_postdom(then_entry, else_entry)?;
    if merge == cfg.exit_block {
        // 严格后支配合流是 exit block，说明两侧都有提前 return 的路径。
        // 若两臂仍有唯一共同 dominance frontier，它就是正常路径的 soft merge；
        // 提前 return 只作为 arm exit，不改变外层的词法 continuation。
        let soft = find_soft_merge(cfg, graph_facts, header, then_entry, else_entry);
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: Some(else_entry),
            merge: soft,
            kind: BranchKind::IfElse,
            invert_hint: false,
        });
    }

    if merge == then_entry {
        return Some(BranchCandidate {
            header,
            then_entry: else_entry,
            else_entry: None,
            merge: Some(then_entry),
            kind: BranchKind::IfThen,
            invert_hint: true,
        });
    }

    if merge == else_entry {
        return Some(BranchCandidate {
            header,
            then_entry,
            else_entry: None,
            merge: Some(else_entry),
            kind: BranchKind::IfThen,
            invert_hint: false,
        });
    }

    Some(BranchCandidate {
        header,
        then_entry,
        else_entry: Some(else_entry),
        merge: Some(merge),
        kind: BranchKind::IfElse,
        invert_hint: false,
    })
}

pub(in crate::structure) fn transparent_jump_target(
    cfg: &Cfg,
    block: BlockRef,
) -> Option<BlockRef> {
    let [edge_ref] = cfg.succs[block.index()].as_slice() else {
        return None;
    };
    let edge = cfg.edges[edge_ref.index()];
    (cfg.blocks[block.index()].instrs.len == 1 && edge.kind == EdgeKind::Jump).then_some(edge.to)
}

pub(super) fn classify_guard_branch(
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> BranchCandidate {
    // 前面的 postdom、loop-boundary 与 soft-merge 规则都无法证明 continuation 时，
    // 不再用“哪一臂可达块更多”猜 guard。保留无 merge 的双臂 owner，后续 plan 会
    // 分别声明两侧出口；这既不丢控制边，也避免每个 branch 做一次全图 DFS。
    BranchCandidate {
        header,
        then_entry,
        else_entry: Some(else_entry),
        merge: None,
        kind: BranchKind::IfElse,
        invert_hint: false,
    }
}

/// 当严格后支配合流 = exit block 时，从两臂共同的 dominance frontier 中找一个
/// "软合流"。它必须是两臂控制流真实汇入的 join，而不是只在全图上绕路可达。
///
/// 典型触发形状：
/// ```text
/// if A then        ← header
///     if B then return end   ← then 侧提前 return，导致 postdom(then)=exit
///     C
/// else
///     D
/// end
/// E                ← 软合流 = 两臂共同的 dominance frontier
/// ```
pub(in crate::structure) fn find_soft_merge(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    header: BlockRef,
    then_entry: BlockRef,
    else_entry: BlockRef,
) -> Option<BlockRef> {
    let else_frontier = graph_facts.dominance_frontier.get(else_entry.index())?;
    let is_common = |candidate: &BlockRef| {
        *candidate != cfg.exit_block
            && graph_facts.dominates(header, *candidate)
            && else_frontier.contains(candidate)
    };
    let nearest = graph_facts
        .dominance_frontier_blocks(then_entry)
        .filter(is_common)
        .min_by_key(|candidate| {
            graph_facts.dominator_tree.depth[candidate.index()].unwrap_or(usize::MAX)
        })?;
    graph_facts
        .dominance_frontier_blocks(then_entry)
        .filter(is_common)
        .all(|candidate| graph_facts.dominates(nearest, candidate))
        .then_some(nearest)
}
