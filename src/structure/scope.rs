//! 这个文件实现 scope 候选提取与 cleanup owner 消解。
//!
//! 它依赖 graph facts 和显式 `Close` 指令，负责把真正含 cleanup 的 block 整理成
//! `ScopeCandidate`。
//! 它不会越权恢复最终词法块，只保留 HIR 需要的 entry/exit/close-point 事实。
//!
//! 例子：
//! - 不含 `Close` 的 loop/branch 不会产生空的 scope 候选
//! - 含 `Close` 的普通 block 会产出 scope 候选，让后面的结构化阶段直接知道
//!   这些 cleanup 点属于词法边界，而不是把 `Close` 当普通语句往后拖
//! - 每条 `Close/Tbc` 最终取得唯一 `CleanupDisposition`；for 词法边界只有在覆盖的
//!   显式 TBC 全部属于唯一 loop owner 时才交给该循环，HIR 不再重跑活跃性分析

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, GraphFacts};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg, TbcKind};

use super::common::{LoopCandidate, ScopeCandidate};
use super::plan::{CleanupDisposition, LoopCandidateId, ScopeCandidateId};

pub(super) fn analyze_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Vec<ScopeCandidate> {
    let close_points_by_block = collect_close_points_by_block(proto, cfg);
    let mut scopes = close_points_by_block
        .into_iter()
        .map(|(block, close_points)| ScopeCandidate {
            entry: block,
            exit: immediate_postdom_exit(cfg, graph_facts, block),
            close_points,
        })
        .collect::<Vec<_>>();

    scopes.sort_by_key(|scope| {
        (
            scope.entry,
            scope.exit,
            scope
                .close_points
                .iter()
                .map(|instr| instr.index())
                .collect::<Vec<_>>(),
        )
    });
    scopes.dedup_by(|left, right| {
        left.entry == right.entry
            && left.exit == right.exit
            && left.close_points == right.close_points
    });
    scopes
}

pub(super) fn analyze_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    scopes: &[ScopeCandidate],
) -> Vec<Option<CleanupDisposition>> {
    let explicit_tbc_close_origins = explicit_tbc_close_origins(proto, cfg);
    let mut lexical_owners = vec![None; proto.instrs.len()];
    for (index, scope) in scopes.iter().enumerate() {
        for close in &scope.close_points {
            let close_block = cfg.instr_to_block[close.index()];
            if scope.entry == close_block {
                assert!(
                    lexical_owners[close.index()]
                        .replace(ScopeCandidateId(index))
                        .is_none(),
                    "close {close} must have exactly one block-scope owner"
                );
            }
        }
    }

    let mut dispositions = vec![None; proto.instrs.len()];
    for block in cfg.block_order.iter().copied() {
        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            let instr_ref = InstrRef(instr_index);
            let reachable = cfg.reachable_blocks.contains(&block);
            dispositions[instr_index] = match &proto.instrs[instr_index] {
                LowInstr::Close(_) | LowInstr::Tbc(_) if !reachable => {
                    Some(CleanupDisposition::Unreachable)
                }
                LowInstr::Tbc(tbc) => Some(match tbc.kind {
                    TbcKind::Explicit => CleanupDisposition::ExplicitTbc,
                    TbcKind::GenericFor => generic_for_owner(cfg, block, loop_candidates)
                        .map(CleanupDisposition::GenericFor)
                        .expect("reachable generic-for TBC must have one loop owner"),
                }),
                LowInstr::Close(_) if explicit_tbc_close_origins.contains_key(&instr_ref) => Some(
                    explicit_tbc_loop_owner(
                        proto,
                        cfg,
                        loop_candidates,
                        instr_ref,
                        &explicit_tbc_close_origins[&instr_ref],
                    )
                    .map_or(CleanupDisposition::ExplicitTbcBoundary, |owner| {
                        CleanupDisposition::LoopTbcBoundary(owner)
                    }),
                ),
                LowInstr::Close(_) => Some(CleanupDisposition::LexicalScope(
                    lexical_owners[instr_index]
                        .expect("reachable close must have one block-scope owner"),
                )),
                _ => None,
            };
        }
    }
    validate_cleanup_dispositions(
        proto,
        cfg,
        loop_candidates,
        scopes,
        &explicit_tbc_close_origins,
        &dispositions,
    );
    dispositions
}

fn generic_for_owner(
    cfg: &Cfg,
    preheader: BlockRef,
    loop_candidates: &[LoopCandidate],
) -> Option<LoopCandidateId> {
    let mut owners = loop_candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| {
            candidate.kind_hint == super::common::LoopKindHint::GenericForLike
                && candidate.preheader == Some(preheader)
                && candidate.continue_target == Some(candidate.header)
                && cfg.unique_reachable_successor(preheader) == Some(candidate.header)
        })
        .map(|(index, _)| LoopCandidateId(index));
    let owner = owners.next()?;
    owners.next().is_none().then_some(owner)
}

fn validate_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    scopes: &[ScopeCandidate],
    explicit_tbc_close_origins: &BTreeMap<InstrRef, BTreeSet<InstrRef>>,
    dispositions: &[Option<CleanupDisposition>],
) {
    assert_eq!(dispositions.len(), proto.instrs.len());
    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let block = cfg.instr_to_block[instr_index];
        let disposition = dispositions[instr_index];
        match (instr, disposition) {
            (LowInstr::Close(_) | LowInstr::Tbc(_), Some(CleanupDisposition::Unreachable)) => {
                assert!(!cfg.reachable_blocks.contains(&block));
            }
            (LowInstr::Tbc(tbc), Some(CleanupDisposition::ExplicitTbc)) => {
                assert_eq!(tbc.kind, TbcKind::Explicit);
                assert!(cfg.reachable_blocks.contains(&block));
            }
            (LowInstr::Tbc(tbc), Some(CleanupDisposition::GenericFor(id))) => {
                let owner = &loop_candidates[id.index()];
                assert_eq!(tbc.kind, TbcKind::GenericFor);
                assert_eq!(generic_for_owner(cfg, block, loop_candidates), Some(id));
                assert_eq!(owner.preheader, Some(block));
            }
            (LowInstr::Close(_), Some(CleanupDisposition::LoopTbcBoundary(id))) => {
                assert!(cfg.reachable_blocks.contains(&block));
                assert_eq!(
                    explicit_tbc_loop_owner(
                        proto,
                        cfg,
                        loop_candidates,
                        InstrRef(instr_index),
                        &explicit_tbc_close_origins[&InstrRef(instr_index)],
                    ),
                    Some(id)
                );
            }
            (LowInstr::Close(_), Some(CleanupDisposition::ExplicitTbcBoundary)) => {
                assert!(cfg.reachable_blocks.contains(&block));
                assert!(explicit_tbc_close_origins.contains_key(&InstrRef(instr_index)));
            }
            (LowInstr::Close(_), Some(CleanupDisposition::LexicalScope(id))) => {
                let owner = &scopes[id.index()];
                assert_eq!(owner.entry, block);
                assert!(owner.close_points.contains(&InstrRef(instr_index)));
            }
            (LowInstr::Close(_) | LowInstr::Tbc(_), _) => {
                panic!("cleanup @{instr_index} must have one matching disposition")
            }
            (_, None) => {}
            (_, Some(_)) => panic!("non-cleanup @{instr_index} cannot have a cleanup disposition"),
        }
    }
}

fn explicit_tbc_close_origins(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> BTreeMap<InstrRef, BTreeSet<InstrRef>> {
    if !proto
        .instrs
        .iter()
        .any(|instr| matches!(instr, LowInstr::Tbc(tbc) if tbc.kind == TbcKind::Explicit))
    {
        return BTreeMap::new();
    }

    let mut active_out = vec![BTreeMap::<usize, BTreeSet<InstrRef>>::new(); cfg.blocks.len()];
    let mut close_points = BTreeMap::new();
    let mut pending = VecDeque::from(cfg.block_order.clone());
    let mut queued = vec![true; cfg.blocks.len()];

    while let Some(block) = pending.pop_front() {
        queued[block.index()] = false;
        if !cfg.reachable_blocks.contains(&block) || block == cfg.exit_block {
            continue;
        }

        let mut active = BTreeMap::<usize, BTreeSet<InstrRef>>::new();
        for predecessor in cfg.preds[block.index()]
            .iter()
            .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        {
            for (reg, origins) in &active_out[predecessor.index()] {
                active.entry(*reg).or_default().extend(origins);
            }
        }
        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            match &proto.instrs[instr_index] {
                LowInstr::Tbc(tbc) if tbc.kind == TbcKind::Explicit => {
                    active.insert(tbc.reg.index(), BTreeSet::from([InstrRef(instr_index)]));
                }
                LowInstr::Close(close) => {
                    let covered = active
                        .range(close.from.index()..)
                        .flat_map(|(_, origins)| origins.iter().copied())
                        .collect::<BTreeSet<_>>();
                    if !covered.is_empty() {
                        close_points.insert(InstrRef(instr_index), covered);
                    }
                    active.retain(|reg, _| *reg < close.from.index());
                }
                _ => {}
            }
        }

        if active == active_out[block.index()] {
            continue;
        }
        active_out[block.index()] = active;
        for edge_ref in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge_ref.index()].to;
            if !queued[successor.index()] {
                queued[successor.index()] = true;
                pending.push_back(successor);
            }
        }
    }

    close_points
}

fn explicit_tbc_loop_owner(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    close_instr: InstrRef,
    covered_tbc_instrs: &BTreeSet<InstrRef>,
) -> Option<LoopCandidateId> {
    let close_block = cfg.instr_to_block[close_instr.index()];
    let LowInstr::Close(close) = proto.instrs[close_instr.index()] else {
        return None;
    };
    let owners = loop_candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| {
            matches!(
                candidate.kind_hint,
                super::common::LoopKindHint::NumericForLike
                    | super::common::LoopKindHint::GenericForLike
            ) && loop_lexical_base(proto, cfg, candidate)
                .is_some_and(|base| close.from.index() >= base.index())
                && covered_tbc_instrs.iter().all(|tbc| {
                    candidate
                        .body_scope_blocks
                        .contains(&cfg.instr_to_block[tbc.index()])
                })
                && loop_tbc_boundary_location_is_owned(
                    proto,
                    cfg,
                    candidate,
                    close_block,
                    close_instr,
                )
        })
        .map(|(index, _)| LoopCandidateId(index))
        .collect::<Vec<_>>();
    // 嵌套候选用集合包含关系表达词法层级；不可比较或同域的候选都保持歧义，
    // 不能再用 block 数量之类的启发式抢占 cleanup。
    let mut innermost = owners.iter().copied().filter(|owner| {
        !owners.iter().copied().any(|other| {
            other != *owner
                && loop_candidates[other.index()]
                    .body_scope_blocks
                    .is_subset(&loop_candidates[owner.index()].body_scope_blocks)
                && loop_candidates[other.index()].body_scope_blocks
                    != loop_candidates[owner.index()].body_scope_blocks
        })
    });
    let owner = innermost.next()?;
    innermost.next().is_none().then_some(owner)
}

fn loop_lexical_base(proto: &LoweredProto, cfg: &Cfg, candidate: &LoopCandidate) -> Option<Reg> {
    match candidate.kind_hint {
        super::common::LoopKindHint::NumericForLike => {
            let preheader = candidate.preheader?;
            let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
                return None;
            };
            Some(init.index)
        }
        super::common::LoopKindHint::GenericForLike => {
            let range = cfg.blocks[candidate.header.index()].instrs;
            (range.start.index()..range.end()).find_map(|index| match proto.instrs[index] {
                LowInstr::GenericForCall(call) => Some(call.state.start),
                _ => None,
            })
        }
        _ => None,
    }
}

fn loop_tbc_boundary_location_is_owned(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopCandidate,
    close_block: BlockRef,
    close_instr: InstrRef,
) -> bool {
    if cfg.preds[close_block.index()].iter().any(|edge_ref| {
        let predecessor = cfg.edges[edge_ref.index()].from;
        cfg.reachable_blocks.contains(&predecessor)
            && !candidate.body_scope_blocks.contains(&predecessor)
            && candidate.preheader != Some(predecessor)
    }) {
        return false;
    }

    let range = cfg.blocks[close_block.index()].instrs;
    if candidate.exits.contains(&close_block) {
        return (range.start.index()..close_instr.index())
            .all(|index| matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_)));
    }
    if !candidate.body_scope_blocks.contains(&close_block)
        || (close_instr.index() + 1..range.end()).any(|index| {
            !matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_))
                && !proto.instrs[index].is_control_terminator()
        })
    {
        return false;
    }
    if candidate.continue_target == Some(close_block)
        || candidate.control_blocks.contains(&close_block)
    {
        return true;
    }
    cfg.unique_reachable_successor(close_block)
        .is_some_and(|successor| candidate.exits.contains(&successor))
}

fn collect_close_points_by_block(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> BTreeMap<BlockRef, Vec<InstrRef>> {
    let mut close_points_by_block = BTreeMap::<BlockRef, Vec<InstrRef>>::new();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if !matches!(instr, LowInstr::Close(_instr)) {
            continue;
        }

        let block = cfg.instr_to_block[instr_index];
        if !cfg.reachable_blocks.contains(&block) {
            continue;
        }

        close_points_by_block
            .entry(block)
            .or_default()
            .push(InstrRef(instr_index));
    }

    close_points_by_block
}

fn immediate_postdom_exit(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BlockRef> {
    graph_facts.post_dominator_tree.parent[block.index()].filter(|exit| *exit != cfg.exit_block)
}
