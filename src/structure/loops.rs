//! 这个文件实现共享循环候选提取。
//!
//! 循环形态只产出 hint，不在这里过早绑定成最终 `while/repeat/for` 语法。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, EdgeRef, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto};

use super::common::{LoopCandidate, LoopKindHint};
use super::helpers::{branch_edges, collect_region_exits};

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Vec<LoopCandidate> {
    let mut grouped_loops = BTreeMap::<BlockRef, (BTreeSet<BlockRef>, Vec<EdgeRef>)>::new();
    for natural_loop in &graph_facts.natural_loops {
        let entry = grouped_loops
            .entry(natural_loop.header)
            .or_insert_with(|| (BTreeSet::new(), Vec::new()));
        entry.0.extend(natural_loop.blocks.iter().copied());
        entry.1.push(natural_loop.backedge);
    }

    let mut loop_candidates = grouped_loops
        .into_iter()
        .map(|(header, (blocks, mut backedges))| {
            backedges.sort();
            backedges.dedup();
            let exits = collect_region_exits(cfg, &blocks);
            let reducible = is_reducible_loop(cfg, header, &blocks);
            let (kind_hint, continue_target) =
                infer_loop_shape(proto, cfg, header, &blocks, &backedges);

            LoopCandidate {
                header,
                blocks,
                backedges,
                exits,
                continue_target,
                kind_hint,
                reducible,
            }
        })
        .collect::<Vec<_>>();

    loop_candidates.sort_by_key(|candidate| candidate.header);
    loop_candidates
}

fn infer_loop_shape(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
    backedges: &[EdgeRef],
) -> (LoopKindHint, Option<BlockRef>) {
    let backedge_sources = backedges
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .collect::<BTreeSet<_>>();

    if backedge_sources.len() == 1 {
        let source = *backedge_sources
            .iter()
            .next()
            .expect("set length already checked");
        if let Some(terminator) = cfg.terminator(&proto.instrs, source)
            && matches!(terminator, LowInstr::NumericForLoop(_instr))
        {
            return (LoopKindHint::NumericForLike, Some(source));
        }
    }

    // generic-for 的 header 本身就携带了比普通回边更强的形状证据。
    // 如果这里先按“回边源是 branch”去判断，很容易把正常的 generic-for
    // 误认成 repeat-like，后面 HIR 就只能回到 unresolved 的 VM 级控制块。
    if matches!(
        cfg.terminator(&proto.instrs, header),
        Some(LowInstr::GenericForLoop(instr))
            if generic_for_has_loop_body_and_exit(proto, cfg, header, instr, blocks)
    ) {
        return (LoopKindHint::GenericForLike, Some(header));
    }

    // Luau 会把一部分 loop-invariant 的常量准备直接塞进 header block，再接 branch。
    // 这种前缀并不属于源码里的 loop body；如果这里还坚持“header 只能有一条 branch”，
    // 很多最普通的 `while i < 3 do ... end` 都会被误打成 repeat/unknown，后面整片
    // 结构恢复就只能回退成 label/goto。
    if block_is_while_header_like(proto, cfg, header)
        && branch_has_loop_body_and_exit(cfg, header, blocks)
    {
        return (LoopKindHint::WhileLike, Some(header));
    }

    if backedge_sources.len() == 1 {
        let source = *backedge_sources
            .iter()
            .next()
            .expect("set length already checked");
        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Branch(_instr)) if branch_has_header_and_exit(cfg, source, header, blocks)
        ) {
            return (LoopKindHint::RepeatLike, Some(source));
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == header
                    && repeat_continue_target_via_backedge_pad(proto, cfg, source, blocks).is_some()
        ) {
            return (
                LoopKindHint::RepeatLike,
                repeat_continue_target_via_backedge_pad(proto, cfg, source, blocks),
            );
        }
    }

    let continue_target = if backedge_sources.len() == 1 {
        backedge_sources.iter().next().copied()
    } else {
        None
    };

    (LoopKindHint::Unknown, continue_target)
}

fn branch_has_loop_body_and_exit(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = branch_edges(cfg, header) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (blocks.contains(&then_block) && !blocks.contains(&else_block))
        || (!blocks.contains(&then_block) && blocks.contains(&else_block))
}

fn branch_has_header_and_exit(
    cfg: &Cfg,
    block: BlockRef,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = branch_edges(cfg, block) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (then_block == header && !blocks.contains(&else_block))
        || (else_block == header && !blocks.contains(&then_block))
}

fn block_is_while_header_like(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    if !matches!(
        cfg.terminator(&proto.instrs, block),
        Some(LowInstr::Branch(_))
    ) {
        return false;
    }
    if range.len == 1 {
        return true;
    }

    (range.start.index()..range.end() - 1).all(|instr_index| {
        matches!(
            proto.instrs[instr_index],
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadConst(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
        )
    })
}

fn repeat_continue_target_via_backedge_pad(
    proto: &LoweredProto,
    cfg: &Cfg,
    backedge_source: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    let mut preds = cfg.preds[backedge_source.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .filter(|pred| cfg.reachable_blocks.contains(pred))
        .filter(|pred| blocks.contains(pred))
        .collect::<Vec<_>>();
    preds.sort();
    preds.dedup();
    let [continue_target] = preds.as_slice() else {
        return None;
    };

    if !matches!(
        cfg.terminator(&proto.instrs, *continue_target),
        Some(LowInstr::Branch(_))
    ) {
        return None;
    }

    let (then_edge_ref, else_edge_ref) = branch_edges(cfg, *continue_target)?;
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    if (then_block == backedge_source && !blocks.contains(&else_block))
        || (else_block == backedge_source && !blocks.contains(&then_block))
    {
        Some(*continue_target)
    } else {
        None
    }
}

fn generic_for_has_loop_body_and_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    instr: &crate::transformer::GenericForLoopInstr,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let range = cfg.blocks[header.index()].instrs;
    if range.len < 2 {
        return false;
    }
    let Some(call_instr_index) = range.end().checked_sub(2) else {
        return false;
    };
    let Some(LowInstr::GenericForCall(call)) = proto.instrs.get(call_instr_index) else {
        return false;
    };
    let body_block = cfg.instr_to_block[instr.body_target.index()];
    let exit_block = cfg.instr_to_block[instr.exit_target.index()];

    matches!(call.results, crate::transformer::ResultPack::Fixed(range) if range == instr.bindings)
        && blocks.contains(&body_block)
        && !blocks.contains(&exit_block)
}

fn is_reducible_loop(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    blocks.iter().all(|block| {
        if *block == header {
            true
        } else {
            cfg.preds[block.index()].iter().all(|edge_ref| {
                let pred = cfg.edges[edge_ref.index()].from;
                !cfg.reachable_blocks.contains(&pred) || blocks.contains(&pred)
            })
        }
    })
}
