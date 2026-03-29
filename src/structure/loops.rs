//! 这个文件实现共享循环候选提取。
//!
//! 这个 pass 只消费 CFG / GraphFacts / Dataflow / low-IR terminator，产出“循环形态 hint +
//! 可直接复用的源码绑定证据 + loop merge incoming 事实”，不会越权决定最终
//! `while/repeat/for` 语法。
//!
//! 例子：
//! - `NumericForInit/Loop` 会产出 `LoopKindHint::NumericForLike`，并把源码绑定寄存器
//!   记录成 `LoopSourceBindings::Numeric`
//! - `GenericForCall/Loop` 会产出 `LoopKindHint::GenericForLike`，并把源码绑定区间
//!   记录成 `LoopSourceBindings::Generic`
//! - `while ... do ... end` 的 header/exit phi 会被整理成 `inside/outside` 两臂的
//!   incoming facts，后续 HIR 直接消费这些结构事实，不再自己回头拆 `phi.incoming`
//! - 普通 `while/repeat` 只保留形态 hint，不会伪造额外 binding 证据

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, Cfg, DataflowFacts, EdgeRef, GraphFacts};
use crate::transformer::{LowInstr, LoweredProto};

use super::common::{
    LoopCandidate, LoopExitValueMergeCandidate, LoopKindHint, LoopSourceBindings, LoopValueMerge,
};
use super::helpers::{collect_region_exits, is_reducible_region};
use super::phi_facts::loop_value_merges_in_block;

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
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
            let preheader = unique_loop_preheader(cfg, header, &blocks);
            let exits = collect_region_exits(cfg, &blocks);
            let reducible = is_reducible_region(cfg, header, &blocks);
            let (kind_hint, continue_target, source_bindings) =
                infer_loop_shape(proto, cfg, header, &blocks, &backedges, preheader);
            let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
            let exit_value_merges = analyze_loop_exit_value_merges(dataflow, &exits, &blocks);

            LoopCandidate {
                header,
                preheader,
                blocks,
                backedges,
                exits,
                continue_target,
                kind_hint,
                source_bindings,
                header_value_merges,
                exit_value_merges,
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
    preheader: Option<BlockRef>,
) -> (LoopKindHint, Option<BlockRef>, Option<LoopSourceBindings>) {
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
            return (
                LoopKindHint::NumericForLike,
                Some(source),
                numeric_for_source_bindings(proto, cfg, preheader),
            );
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
        return (
            LoopKindHint::GenericForLike,
            Some(header),
            generic_for_source_bindings(proto, cfg, header),
        );
    }

    // Luau 会把一部分 loop-invariant 的常量准备直接塞进 header block，再接 branch。
    // 这种前缀并不属于源码里的 loop body；如果这里还坚持“header 只能有一条 branch”，
    // 很多最普通的 `while i < 3 do ... end` 都会被误打成 repeat/unknown，后面整片
    // 结构恢复就只能回退成 label/goto。
    if block_is_while_header_like(proto, cfg, header)
        && branch_has_loop_body_and_exit(cfg, header, blocks)
    {
        return (LoopKindHint::WhileLike, Some(header), None);
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
            return (LoopKindHint::RepeatLike, Some(source), None);
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
                None,
            );
        }
    }

    let continue_target = if backedge_sources.len() == 1 {
        backedge_sources.iter().next().copied()
    } else {
        None
    };

    (LoopKindHint::Unknown, continue_target, None)
}

fn numeric_for_source_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    preheader: Option<BlockRef>,
) -> Option<LoopSourceBindings> {
    let preheader = preheader?;
    let instr_ref = cfg.blocks[preheader.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        LowInstr::NumericForInit(instr) => Some(LoopSourceBindings::Numeric(instr.binding)),
        _ => None,
    }
}

fn generic_for_source_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
) -> Option<LoopSourceBindings> {
    let instr_ref = cfg.blocks[header.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        LowInstr::GenericForLoop(instr) => Some(LoopSourceBindings::Generic(instr.bindings)),
        _ => None,
    }
}

fn analyze_loop_header_value_merges(
    dataflow: &DataflowFacts,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopValueMerge> {
    loop_value_merges_in_block(dataflow, header, loop_blocks)
        .into_iter()
        .filter(loop_value_has_inside_and_outside_incoming)
        .collect()
}

fn analyze_loop_exit_value_merges(
    dataflow: &DataflowFacts,
    exits: &BTreeSet<BlockRef>,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopExitValueMergeCandidate> {
    exits
        .iter()
        .copied()
        .filter_map(|exit| {
            let values = loop_value_merges_in_block(dataflow, exit, loop_blocks)
                .into_iter()
                .filter(|value| !value.inside_arm.is_empty())
                .collect::<Vec<_>>();
            (!values.is_empty()).then_some(LoopExitValueMergeCandidate { exit, values })
        })
        .collect()
}

fn loop_value_has_inside_and_outside_incoming(value: &LoopValueMerge) -> bool {
    !value.inside_arm.is_empty() && !value.outside_arm.is_empty()
}

fn unique_loop_preheader(
    cfg: &Cfg,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    let preds = cfg
        .reachable_predecessors(header)
        .into_iter()
        .filter(|pred| !loop_blocks.contains(pred))
        .collect::<Vec<_>>();
    let [preheader] = preds.as_slice() else {
        return None;
    };
    Some(*preheader)
}

fn branch_has_loop_body_and_exit(cfg: &Cfg, header: BlockRef, blocks: &BTreeSet<BlockRef>) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = cfg.branch_edges(header) else {
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
    let Some((then_edge_ref, else_edge_ref)) = cfg.branch_edges(block) else {
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
    let preds = cfg
        .reachable_predecessors(backedge_source)
        .into_iter()
        .filter(|pred| blocks.contains(pred))
        .collect::<Vec<_>>();
    let [continue_target] = preds.as_slice() else {
        return None;
    };

    if !matches!(
        cfg.terminator(&proto.instrs, *continue_target),
        Some(LowInstr::Branch(_))
    ) {
        return None;
    }

    let (then_edge_ref, else_edge_ref) = cfg.branch_edges(*continue_target)?;
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
