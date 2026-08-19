//! 推导循环 continuation、空 return 出口与线性退出尾；依赖循环候选和 CFG，不负责循环形态识别；例如识别共享 cleanup 后的空返回。

use super::*;

pub(super) fn loop_continuation(
    proto: &LoweredProto,
    candidate: &LoopCandidate,
    condition: Option<&ConditionPlanInput>,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    exit_block: super::super::BlockRef,
) -> Option<super::super::BlockRef> {
    let condition_exit = condition.and_then(|condition| {
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            return None;
        };
        let is_iteration_target = |block| {
            candidate.blocks.contains(&block)
                || candidate.control_blocks.contains(&block)
                || candidate.continue_target == Some(block)
        };
        let direct = match (is_iteration_target(truthy), is_iteration_target(falsy)) {
            (true, false) if falsy != exit_block => Some(falsy),
            (false, true) if truthy != exit_block => Some(truthy),
            (true, true) | (false, false) | (true, false) | (false, true) => None,
        }?;
        Some(loops::transparent_loop_exit_target(proto, cfg, direct).unwrap_or(direct))
    });
    let mut exits = candidate.exits.iter().copied();
    let first = exits.next()?;
    let common = exits
        .try_fold(first, |common, exit| {
            graph_facts.nearest_common_postdom(common, exit)
        })
        .filter(|continuation| *continuation != exit_block);
    if common.is_none()
        && matches!(
            candidate.kind_hint,
            super::super::LoopKindHint::Unknown | super::super::LoopKindHint::WhileTrueLike
        )
        && let Some(continuation) =
            unique_cleanup_to_empty_return_exit(proto, cfg, &candidate.exits)
        && (condition_exit.is_some_and(|exit| loop_exit_is_terminal(proto, cfg, exit))
            || candidate
                .exits
                .iter()
                .copied()
                .any(|exit| exit != continuation && loop_exit_is_terminal(proto, cfg, exit)))
    {
        // Unknown/while-true 的 header guard 可以直接 return；它不是 loop 的 break
        // continuation。若另有唯一 Close-only 路径落到空 return，则该路径才是词法
        // break 后的函数尾，选它可保留 loop scope 而无需伪 goto。
        return Some(continuation);
    }
    match (condition_exit, common) {
        (Some(direct), Some(common))
            if direct != common && !linear_loop_exit_tail(cfg, candidate, direct, common) =>
        {
            Some(direct)
        }
        (Some(direct), None) => Some(direct),
        (_, common) => common,
    }
}

pub(super) fn unique_cleanup_to_empty_return_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    exits: &BTreeSet<super::super::BlockRef>,
) -> Option<super::super::BlockRef> {
    let mut continuation = None;
    for exit in exits {
        let range = cfg.blocks.get(exit.index())?.instrs;
        let [edge_ref] = cfg.succs.get(exit.index())?.as_slice() else {
            continue;
        };
        let edge = cfg.edges.get(edge_ref.index())?;
        if !matches!(edge.kind, EdgeKind::Fallthrough | EdgeKind::Jump) {
            continue;
        }
        let body_end = range.last().map_or(range.end(), |last| {
            if matches!(proto.instrs.get(last.index()), Some(LowInstr::Jump(_))) {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if range.start.index() == body_end
            || !(range.start.index()..body_end)
                .all(|index| matches!(proto.instrs.get(index), Some(LowInstr::Close(_))))
        {
            continue;
        }
        let Some(target) = cfg.blocks.get(edge.to.index()) else {
            continue;
        };
        let Some(return_instr) = target.instrs.last() else {
            continue;
        };
        if !(target.instrs.start.index()..return_instr.index())
            .all(|index| matches!(proto.instrs.get(index), Some(LowInstr::Close(_))))
            || !matches!(
                proto.instrs.get(return_instr.index()),
                Some(LowInstr::Return(return_))
                    if matches!(
                        return_.values,
                        crate::transformer::ValuePack::Fixed(range) if range.len == 0
                    )
            )
        {
            continue;
        }
        if continuation.replace(*exit).is_some() {
            return None;
        }
    }
    continuation
}

pub(super) fn loop_exit_is_terminal(
    proto: &LoweredProto,
    cfg: &Cfg,
    exit: super::super::BlockRef,
) -> bool {
    let is_terminal = |block| {
        matches!(
            cfg.terminator(&proto.instrs, block),
            Some(LowInstr::Return(_) | LowInstr::TailCall(_))
        )
    };
    is_terminal(exit)
        || cfg
            .unique_reachable_successor(exit)
            .is_some_and(is_terminal)
}

pub(super) fn linear_loop_exit_tail(
    cfg: &Cfg,
    candidate: &LoopCandidate,
    mut block: super::super::BlockRef,
    continuation: super::super::BlockRef,
) -> bool {
    let mut remaining = cfg.blocks.len();
    while block != continuation && remaining > 0 {
        if candidate.blocks.contains(&block) || candidate.control_blocks.contains(&block) {
            return false;
        }
        let Some([edge]) = cfg.succs.get(block.index()).map(Vec::as_slice) else {
            return false;
        };
        block = cfg.edges[edge.index()].to;
        remaining -= 1;
    }
    block == continuation
}
