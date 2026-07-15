//! 这个文件实现 scope 候选提取与 cleanup owner 消解。
//!
//! 它依赖 loop/branch/graph facts 已经给好的结构边界和显式 `Close` 指令，负责把
//! “哪些 block 天然形成一个词法收束点”整理成 `ScopeCandidate`。
//! 它不会越权恢复最终词法块，只保留 HIR 需要的 entry/exit/close-point 事实。
//!
//! 例子：
//! - `while ... do ... end` 会产出一条 `LoopScope`，entry 是 loop header，exit 是
//!   结构层已经识别出的单出口
//! - 含 `Close` 的普通 block 会额外产出 `BlockScope`，让后面的结构化阶段直接知道
//!   这些 cleanup 点属于词法边界，而不是把 `Close` 当普通语句往后拖
//! - 每条 `Close/Tbc` 最终取得唯一 `CleanupDisposition`；HIR 只消费该结论，不再
//!   重新运行一套显式 TBC 活跃性分析

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, GraphFacts};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, TbcKind};

use super::common::{BranchRegionFact, LoopCandidate, ScopeCandidate, ScopeKind};
use super::plan::{CleanupDisposition, LoopCandidateId, ScopeCandidateId};

pub(super) fn analyze_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_regions: &[BranchRegionFact],
) -> Vec<ScopeCandidate> {
    let close_points_by_block = collect_close_points_by_block(proto, cfg);
    let mut scopes = Vec::new();

    for loop_candidate in loop_candidates {
        scopes.push(ScopeCandidate {
            entry: loop_candidate.header,
            exit: single_exit(&loop_candidate.exits),
            close_points: collect_close_points(&loop_candidate.blocks, &close_points_by_block),
            kind: ScopeKind::LoopScope,
        });
    }

    for branch_region in branch_regions {
        scopes.push(ScopeCandidate {
            entry: branch_region.header,
            exit: Some(branch_region.merge),
            close_points: collect_close_points(
                &branch_region.structured_blocks,
                &close_points_by_block,
            ),
            kind: ScopeKind::BranchScope,
        });
    }

    for (block, close_points) in close_points_by_block {
        scopes.push(ScopeCandidate {
            entry: block,
            exit: immediate_postdom_exit(cfg, graph_facts, block),
            close_points,
            kind: ScopeKind::BlockScope,
        });
    }

    scopes.sort_by_key(|scope| {
        (
            scope.entry,
            scope_kind_rank(scope.kind),
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
            && left.kind == right.kind
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
    let explicit_tbc_close_points = explicit_tbc_close_points(proto, cfg);
    let mut lexical_owners = vec![None; proto.instrs.len()];
    for (index, scope) in scopes
        .iter()
        .enumerate()
        .filter(|(_, scope)| scope.kind == ScopeKind::BlockScope)
    {
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
                LowInstr::Close(_) if explicit_tbc_close_points.contains(&instr_ref) => {
                    Some(CleanupDisposition::ExplicitTbcBoundary)
                }
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
        &explicit_tbc_close_points,
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
    explicit_tbc_close_points: &BTreeSet<InstrRef>,
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
            (LowInstr::Close(_), Some(CleanupDisposition::ExplicitTbcBoundary)) => {
                assert!(cfg.reachable_blocks.contains(&block));
                assert!(explicit_tbc_close_points.contains(&InstrRef(instr_index)));
            }
            (LowInstr::Close(_), Some(CleanupDisposition::LexicalScope(id))) => {
                let owner = &scopes[id.index()];
                assert_eq!(owner.kind, ScopeKind::BlockScope);
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

fn explicit_tbc_close_points(proto: &LoweredProto, cfg: &Cfg) -> BTreeSet<InstrRef> {
    let mut active_out = vec![BTreeSet::<usize>::new(); cfg.blocks.len()];
    let mut close_points = BTreeSet::new();
    let mut pending = VecDeque::from(cfg.block_order.clone());
    let mut queued = vec![true; cfg.blocks.len()];

    while let Some(block) = pending.pop_front() {
        queued[block.index()] = false;
        if !cfg.reachable_blocks.contains(&block) || block == cfg.exit_block {
            continue;
        }

        let mut active = cfg.preds[block.index()]
            .iter()
            .flat_map(|edge_ref| {
                let predecessor = cfg.edges[edge_ref.index()].from;
                active_out[predecessor.index()].iter().copied()
            })
            .collect::<BTreeSet<_>>();
        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            match &proto.instrs[instr_index] {
                LowInstr::Tbc(tbc) if tbc.kind == TbcKind::Explicit => {
                    active.insert(tbc.reg.index());
                }
                LowInstr::Close(close) => {
                    if active.range(close.from.index()..).next().is_some() {
                        close_points.insert(InstrRef(instr_index));
                    }
                    active.retain(|reg| *reg < close.from.index());
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

fn collect_close_points(
    blocks: &BTreeSet<BlockRef>,
    close_points_by_block: &BTreeMap<BlockRef, Vec<InstrRef>>,
) -> Vec<InstrRef> {
    let mut close_points = blocks
        .iter()
        .filter_map(|block| close_points_by_block.get(block))
        .flat_map(|points| points.iter().copied())
        .collect::<Vec<_>>();
    close_points.sort_by_key(|instr| instr.index());
    close_points
}

fn single_exit(exits: &BTreeSet<BlockRef>) -> Option<BlockRef> {
    if exits.len() == 1 {
        exits.iter().next().copied()
    } else {
        None
    }
}

fn immediate_postdom_exit(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BlockRef> {
    graph_facts.post_dominator_tree.parent[block.index()].filter(|exit| *exit != cfg.exit_block)
}

fn scope_kind_rank(kind: ScopeKind) -> u8 {
    match kind {
        ScopeKind::BlockScope => 0,
        ScopeKind::LoopScope => 1,
        ScopeKind::BranchScope => 2,
    }
}
