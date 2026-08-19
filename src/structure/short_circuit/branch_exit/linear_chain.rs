//! 索引线性条件链、推断统一出口并冻结节点目标；依赖 branch successor 与安全块约束，不负责闭合 DAG；例如将末端真假 target 分类为 Node 或 Exit。

use super::*;

pub(super) enum ResolvedGuardTarget {
    Final(GuardExitTempTarget),
    Header(BlockRef),
}

#[derive(Clone, Copy, Default)]
pub(super) enum LinearChainNext {
    #[default]
    End,
    One(BlockRef),
    Two(BlockRef, BlockRef),
}

pub(super) struct LinearChainIndex {
    next_by_header: Vec<LinearChainNext>,
}

impl LinearChainIndex {
    pub(super) fn branch_then(
        block_count: usize,
        branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
        candidates: &[BranchCandidate],
    ) -> Self {
        let mut next_by_header = vec![LinearChainNext::End; block_count];
        for candidate in candidates {
            if candidate.kind == BranchKind::IfThen
                && let Some(next) = branch_by_header.get(&candidate.then_entry)
            {
                next_by_header[candidate.header.index()] = LinearChainNext::One(next.header);
            }
        }
        Self { next_by_header }
    }

    pub(super) fn cfg(
        proto: &LoweredProto,
        cfg: &Cfg,
        branch_by_header: &BTreeMap<BlockRef, &BranchCandidate>,
        candidates: &[BranchCandidate],
    ) -> Self {
        let mut next_by_header = vec![LinearChainNext::End; cfg.blocks.len()];
        for candidate in candidates {
            let Some((truthy, falsy)) = truthy_falsy_targets(proto, cfg, candidate.header) else {
                continue;
            };
            let mut first = None;
            let mut second = None;
            for target in [truthy, falsy] {
                if !branch_by_header.contains_key(&target)
                    || cfg.preds[target.index()].len() > 1
                    || first == Some(target)
                {
                    continue;
                }
                if first.is_none() {
                    first = Some(target);
                } else {
                    second = Some(target);
                }
            }
            next_by_header[candidate.header.index()] = match (first, second) {
                (Some(first), Some(second)) if first < second => {
                    LinearChainNext::Two(first, second)
                }
                (Some(first), Some(second)) => LinearChainNext::Two(second, first),
                (Some(next), None) => LinearChainNext::One(next),
                (None, _) => LinearChainNext::End,
            };
        }
        Self { next_by_header }
    }

    pub(super) fn next(
        &self,
        header: BlockRef,
        visited: &DenseMarks,
        epoch: u32,
    ) -> Option<BlockRef> {
        match self.next_by_header.get(header.index()).copied()? {
            LinearChainNext::End => None,
            LinearChainNext::One(next) => (!visited.contains(next, epoch)).then_some(next),
            LinearChainNext::Two(first, second) => match (
                visited.contains(first, epoch),
                visited.contains(second, epoch),
            ) {
                (false, true) => Some(first),
                (true, false) => Some(second),
                (false, false) | (true, true) => None,
            },
        }
    }
}

pub(super) fn collect_if_else_branch_exit_chain(
    root: &BranchCandidate,
    chains: &LinearChainIndex,
    visited: &mut DenseMarks,
) -> Vec<BlockRef> {
    let mut headers = Vec::new();
    let visited_epoch = visited.begin();
    let mut current = root.header;

    while visited.insert(current, visited_epoch) {
        headers.push(current);
        let Some(next) = chains.next(current, visited, visited_epoch) else {
            break;
        };
        current = next;
    }

    headers
}

pub(super) fn infer_linear_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<ShortCircuitExit> {
    let mut truthy_exit = None;
    let mut falsy_exit = None;

    for (index, header) in headers.iter().enumerate() {
        let next = headers.get(index + 1).copied();
        let (truthy_target, falsy_target) = truthy_falsy_targets(proto, cfg, *header)?;

        match next {
            Some(next_header) if truthy_target == next_header => {
                falsy_exit.get_or_insert(falsy_target);
                if falsy_exit != Some(falsy_target) {
                    return None;
                }
            }
            Some(next_header) if falsy_target == next_header => {
                truthy_exit.get_or_insert(truthy_target);
                if truthy_exit != Some(truthy_target) {
                    return None;
                }
            }
            Some(_) => return None,
            None => {
                truthy_exit.get_or_insert(truthy_target);
                falsy_exit.get_or_insert(falsy_target);
                if truthy_exit != Some(truthy_target) || falsy_exit != Some(falsy_target) {
                    return None;
                }
            }
        }
    }

    Some(ShortCircuitExit::BranchExit {
        truthy: truthy_exit?,
        falsy: falsy_exit?,
    })
}

pub(super) fn infer_longest_linear_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<(usize, ShortCircuitExit)> {
    let mut truthy_exit = None;
    let mut falsy_exit = None;
    let mut best = None;

    for (index, header) in headers.iter().copied().enumerate() {
        let Some((truthy_target, falsy_target)) = truthy_falsy_targets(proto, cfg, header) else {
            break;
        };
        if index >= 1
            && truthy_exit.is_none_or(|exit| exit == truthy_target)
            && falsy_exit.is_none_or(|exit| exit == falsy_target)
        {
            best = Some((
                index + 1,
                ShortCircuitExit::BranchExit {
                    truthy: truthy_target,
                    falsy: falsy_target,
                },
            ));
        }

        let Some(next) = headers.get(index + 1).copied() else {
            break;
        };
        let valid = if truthy_target == next {
            constrain_linear_exit(&mut falsy_exit, falsy_target)
        } else if falsy_target == next {
            constrain_linear_exit(&mut truthy_exit, truthy_target)
        } else {
            false
        };
        if !valid {
            break;
        }
    }

    best
}

pub(super) fn infer_longest_if_else_branch_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
) -> Option<(usize, ShortCircuitExit)> {
    let (&first_header, remaining_headers) = headers.split_first()?;
    let mut previous_targets = truthy_falsy_targets(proto, cfg, first_header)?;
    let mut external_targets = BTreeMap::<BlockRef, usize>::new();
    for target in [previous_targets.0, previous_targets.1] {
        *external_targets.entry(target).or_default() += 1;
    }
    let mut strict_truthy_exit = None;
    let mut strict_falsy_exit = None;
    let mut strict_possible = true;
    let mut best = None;

    for (index, header) in remaining_headers.iter().copied().enumerate() {
        let Some(targets) = truthy_falsy_targets(proto, cfg, header) else {
            break;
        };
        for target in [previous_targets.0, previous_targets.1] {
            if target == header && !decrement_target_count(&mut external_targets, target) {
                return best;
            }
        }

        if previous_targets.0 == header {
            strict_possible = strict_possible
                && constrain_linear_exit(&mut strict_falsy_exit, previous_targets.1);
        } else if previous_targets.1 == header {
            strict_possible = strict_possible
                && constrain_linear_exit(&mut strict_truthy_exit, previous_targets.0);
        } else {
            strict_possible = false;
        }

        for target in [targets.0, targets.1] {
            *external_targets.entry(target).or_default() += 1;
        }
        previous_targets = targets;

        let strict_exit = (strict_possible
            && strict_truthy_exit.is_none_or(|exit| exit == targets.0)
            && strict_falsy_exit.is_none_or(|exit| exit == targets.1))
        .then_some(ShortCircuitExit::BranchExit {
            truthy: targets.0,
            falsy: targets.1,
        });
        let relaxed_exit = || {
            let mut exits = external_targets.keys().copied();
            let (Some(truthy), Some(falsy), None) = (exits.next(), exits.next(), exits.next())
            else {
                return None;
            };
            Some(ShortCircuitExit::BranchExit { truthy, falsy })
        };

        if let Some(exit) = strict_exit.or_else(relaxed_exit) {
            best = Some((index + 2, exit));
        }
    }

    best
}

pub(super) fn constrain_linear_exit(exit: &mut Option<BlockRef>, target: BlockRef) -> bool {
    match *exit {
        Some(existing) => existing == target,
        None => {
            *exit = Some(target);
            true
        }
    }
}

pub(super) fn decrement_target_count(
    targets: &mut BTreeMap<BlockRef, usize>,
    target: BlockRef,
) -> bool {
    let Some(count) = targets.get_mut(&target) else {
        return false;
    };
    *count -= 1;
    if *count == 0 {
        targets.remove(&target);
    }
    true
}

pub(super) fn build_linear_branch_exit_nodes(
    proto: &LoweredProto,
    cfg: &Cfg,
    headers: &[BlockRef],
    exit: &ShortCircuitExit,
) -> Option<Vec<ShortCircuitNode>> {
    let ShortCircuitExit::BranchExit { truthy, falsy } = *exit else {
        return None;
    };

    let node_ids = headers
        .iter()
        .enumerate()
        .map(|(index, header)| (*header, ShortCircuitNodeRef(index)))
        .collect::<BTreeMap<_, _>>();

    headers
        .iter()
        .enumerate()
        .map(|(index, header)| {
            let next = headers.get(index + 1).and_then(|header| {
                node_ids
                    .get(header)
                    .copied()
                    .map(|node_ref| (*header, node_ref))
            });
            let (truthy_target, falsy_target) = truthy_falsy_targets(proto, cfg, *header)?;

            Some(ShortCircuitNode {
                id: ShortCircuitNodeRef(index),
                header: *header,
                truthy: classify_linear_target(truthy_target, next, truthy, falsy)?,
                falsy: classify_linear_target(falsy_target, next, truthy, falsy)?,
            })
        })
        .collect()
}

pub(super) fn classify_linear_target(
    block: BlockRef,
    next: Option<(BlockRef, ShortCircuitNodeRef)>,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ShortCircuitTarget> {
    match next {
        Some((next_block, next_ref)) if block == next_block => {
            Some(ShortCircuitTarget::Node(next_ref))
        }
        _ if block == truthy_exit => Some(ShortCircuitTarget::TruthyExit),
        _ if block == falsy_exit => Some(ShortCircuitTarget::FalsyExit),
        _ => None,
    }
}

pub(super) fn classify_guard_branch_exits(
    cfg: &Cfg,
    post_dom_tree: &PostDominatorTree,
    first_exit: BlockRef,
    second_exit: BlockRef,
) -> Option<(BlockRef, BlockRef)> {
    match (
        post_dom_tree.dominates(first_exit, second_exit),
        post_dom_tree.dominates(second_exit, first_exit),
    ) {
        (true, false) => return Some((second_exit, first_exit)),
        (false, true) => return Some((first_exit, second_exit)),
        _ => {}
    }

    match (
        cfg.can_reach(first_exit, second_exit),
        cfg.can_reach(second_exit, first_exit),
    ) {
        (true, false) => Some((first_exit, second_exit)),
        (false, true) => Some((second_exit, first_exit)),
        (false, false) => Some((first_exit, second_exit)),
        (true, true) => Some((first_exit, second_exit)),
    }
}

pub(super) fn finalize_guard_exit_target(
    target: GuardExitTempTarget,
    truthy_exit: BlockRef,
    falsy_exit: BlockRef,
) -> Option<ShortCircuitTarget> {
    match target {
        GuardExitTempTarget::Node(node_ref) => Some(ShortCircuitTarget::Node(node_ref)),
        GuardExitTempTarget::Exit(block) if block == truthy_exit => {
            Some(ShortCircuitTarget::TruthyExit)
        }
        GuardExitTempTarget::Exit(block) if block == falsy_exit => {
            Some(ShortCircuitTarget::FalsyExit)
        }
        GuardExitTempTarget::Exit(_) => None,
    }
}
