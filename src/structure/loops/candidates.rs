//! 构造常规及退化 numeric/generic-for 循环候选；依赖 natural domain 与 VM 指令状态，不负责 body scope 精化；例如恢复无自身回边的 generic-for owner。

use super::*;

pub(super) fn build_loop_candidate(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    header: BlockRef,
    blocks: BTreeSet<BlockRef>,
    mut backedges: Vec<EdgeRef>,
) -> LoopCandidate {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    backedges.sort();
    backedges.dedup();
    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let exits = collect_region_exits(cfg, &blocks);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    let (kind_hint, continue_target, source_bindings) = infer_loop_shape(LoopShapeInput {
        proto,
        cfg,
        dataflow,
        header,
        blocks: &blocks,
        backedges: &backedges,
        exits: &exits,
        preheader,
        header_value_merges: &header_value_merges,
    });
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (kind_hint, continue_target),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );
    let exit_value_merges = analyze_loop_exit_value_merges(
        cfg,
        dataflow,
        &exits,
        shared_exit.as_ref(),
        &blocks,
        &blocks,
    );

    LoopCandidate {
        header,
        preheader,
        blocks,
        body_scope_blocks,
        control_blocks: Vec::new(),
        normalized_exit_aliases: Vec::new(),
        backedges,
        exits,
        continue_target,
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint,
        source_bindings,
        header_value_merges,
        exit_value_merges,
    }
}

pub(super) fn degenerate_numeric_for_loop(
    context: &LoopAnalysisContext<'_>,
    numeric_headers: &[bool],
    numeric_for_latches: &NumericForLatchIndex<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    preheader: BlockRef,
) -> Option<LoopCandidate> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    let Some(LowInstr::NumericForInit(init)) = cfg.terminator(&proto.instrs, preheader) else {
        return None;
    };
    let header = cfg.instr_to_block[init.body_target.index()];
    let exit = cfg.instr_to_block[init.exit_target.index()];
    if numeric_headers[header.index()] || header == exit {
        return None;
    }

    let latch = numeric_for_latches
        .get(&numeric_for_init_state(init))?
        .iter()
        .find_map(|(latch, loop_instr)| {
            // Luau 会把不可达 latch 的 body edge 直接改指向 loop exit。立即 break
            // 还会把 latch exit 留在不可达 jump pad，但仍共享同一个数值循环身份。
            ((loop_instr.body_target == init.body_target
                || loop_instr.body_target == init.exit_target)
                && same_or_equivalent_exit_target(
                    proto,
                    cfg,
                    loop_instr.exit_target,
                    init.exit_target,
                ))
            .then_some(*latch)
        })?;
    if cfg.reachable_blocks.contains(&latch)
        || latch == preheader
        || latch == header
        || latch == exit
    {
        return None;
    }

    let mut blocks = collect_forward_region_blocks(
        cfg,
        [header],
        Some(exit),
        Some((header, &graph_facts.dominator_tree)),
    );
    blocks.insert(latch);
    let mut exits = collect_region_exits(cfg, &blocks);
    // 立即 break/return 的 body 不会物理抵达零迭代出口；preheader 的 LoopExit
    // 仍是源码 numeric-for 的唯一正常 continuation，必须显式保留。
    exits.insert(exit);
    if !is_reducible_region(cfg, header, &blocks) {
        return None;
    }
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (LoopKindHint::NumericForLike, Some(latch)),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );

    Some(LoopCandidate {
        header,
        preheader: Some(preheader),
        body_scope_blocks,
        control_blocks: Vec::new(),
        normalized_exit_aliases: Vec::new(),
        backedges: Vec::new(),
        exits: exits.clone(),
        continue_target: Some(latch),
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint: LoopKindHint::NumericForLike,
        source_bindings: Some(LoopSourceBindings::Numeric(init.binding)),
        header_value_merges: analyze_loop_header_value_merges(dataflow, header, &blocks),
        exit_value_merges: analyze_loop_exit_value_merges(
            cfg,
            dataflow,
            &exits,
            shared_exit.as_ref(),
            &blocks,
            &blocks,
        ),
        blocks,
    })
}

pub(super) fn same_or_equivalent_exit_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    actual: crate::transformer::InstrRef,
    expected: crate::transformer::InstrRef,
) -> bool {
    same_or_transparent_jump_target(proto, cfg, actual, expected)
        || equivalent_single_return_targets(proto, cfg, actual, expected)
}

/// generic-for 的零迭代出口可以先经过一层纯 jump 汇入原始 body target；
/// body target 本身不能继续穿透，否则会把祖先 loop latch 误当成普通空 body。
pub(in crate::structure) fn generic_for_immediate_break(
    proto: &LoweredProto,
    cfg: &Cfg,
    instr: &GenericForLoopInstr,
) -> bool {
    cfg.instr_to_block[instr.exit_target.index()] == cfg.instr_to_block[instr.body_target.index()]
        || same_or_transparent_jump_target(proto, cfg, instr.exit_target, instr.body_target)
}

pub(super) fn analyze_degenerate_generic_for_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    grouped_headers: &[bool],
    shared_exit_workspace: &mut SharedExitWorkspace,
) -> Vec<LoopCandidate> {
    cfg.reachable_blocks
        .iter()
        .copied()
        .filter(|header| !grouped_headers[header.index()])
        .filter_map(|header| {
            degenerate_generic_for_loop(
                proto,
                cfg,
                dataflow,
                graph_facts,
                shared_exit_workspace,
                header,
            )
        })
        .collect()
}

pub(super) fn degenerate_generic_for_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph_facts: &GraphFacts,
    shared_exit_workspace: &mut SharedExitWorkspace,
    header: BlockRef,
) -> Option<LoopCandidate> {
    let Some(LowInstr::GenericForLoop(instr)) = cfg.terminator(&proto.instrs, header) else {
        return None;
    };
    let body = cfg.instr_to_block[instr.body_target.index()];
    let exit = cfg.instr_to_block[instr.exit_target.index()];
    // Luau 会把 `for ... do break end` 编译成 body/exit 同目标，或让 exit 先经过
    // 单条 jump pad 再汇入 body；这不是“没有循环”，候选只需让 header 持有控制结构。
    let immediate_break = generic_for_immediate_break(proto, cfg, instr);
    let mut blocks = BTreeSet::from([header]);
    if !immediate_break {
        blocks.extend(collect_forward_region_blocks(
            cfg,
            [body],
            Some(exit),
            Some((body, &graph_facts.dominator_tree)),
        ));
    }
    if body == header
        || exit == header
        || (!immediate_break && blocks.contains(&exit))
        || !generic_for_has_loop_body_and_exit(proto, cfg, header, instr, &blocks)
    {
        return None;
    }

    let exits = collect_region_exits(cfg, &blocks);
    if !exits.contains(&exit) || !is_reducible_region(cfg, header, &blocks) {
        return None;
    }
    let shared_exit = shared_exit_continuation(proto, &exits, cfg, shared_exit_workspace);
    let body_scope_blocks = loop_body_scope(
        (LoopKindHint::GenericForLike, Some(header)),
        &blocks,
        &exits,
        shared_exit.as_ref(),
        header,
        cfg,
        graph_facts,
    );

    let preheader = unique_loop_preheader(cfg, header, &blocks);
    let header_value_merges = analyze_loop_header_value_merges(dataflow, header, &blocks);
    // 退化 generic-for 没有自身回边：header -> exit 表示零次迭代，语义上属于
    // 循环外初值；只有被 body 支配的完整区域到 exit 的边才是循环内写回。
    let mut body_blocks = blocks.clone();
    body_blocks.remove(&header);
    let exit_value_merges = analyze_loop_exit_value_merges(
        cfg,
        dataflow,
        &exits,
        shared_exit.as_ref(),
        &body_blocks,
        &blocks,
    );

    Some(LoopCandidate {
        header,
        preheader,
        blocks,
        body_scope_blocks,
        control_blocks: Vec::new(),
        normalized_exit_aliases: Vec::new(),
        backedges: Vec::new(),
        exits,
        continue_target: Some(header),
        continue_edges: BTreeSet::new(),
        condition_header: None,
        kind_hint: LoopKindHint::GenericForLike,
        source_bindings: generic_for_source_bindings(proto, cfg, header),
        header_value_merges,
        exit_value_merges,
    })
}
