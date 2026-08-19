//! 推断 loop kind、source bindings、body scope 与初步 value merge；依赖 CFG/SSA 和候选域，不负责共享退出路径；例如区分 while/repeat/for 的控制前缀。

use super::*;

pub(super) struct LoopShapeInput<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) header: BlockRef,
    pub(super) blocks: &'a BTreeSet<BlockRef>,
    pub(super) backedges: &'a [EdgeRef],
    pub(super) exits: &'a BTreeSet<BlockRef>,
    pub(super) preheader: Option<BlockRef>,
    pub(super) header_value_merges: &'a [LoopValueMerge],
}

pub(super) fn infer_loop_shape(
    input: LoopShapeInput<'_>,
) -> (LoopKindHint, Option<BlockRef>, Option<LoopSourceBindings>) {
    let LoopShapeInput {
        proto,
        cfg,
        dataflow,
        header,
        blocks,
        backedges,
        exits,
        preheader,
        header_value_merges,
    } = input;
    let backedge_sources = backedges
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .collect::<BTreeSet<_>>();

    if let Some(source) = numeric_for_latch_for_preheader(
        proto,
        cfg,
        header,
        preheader,
        backedge_sources.iter().copied(),
    ) {
        return (
            LoopKindHint::NumericForLike,
            Some(source),
            numeric_for_source_bindings(proto, cfg, preheader),
        );
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

    // dialect lowering 往往会把 while 条件需要的临时准备也塞进 header block，再接 branch。
    // 这些前缀仍然属于“每轮先算条件、再决定进不进 body”的源码语义；如果这里只接受
    // 纯常量加载，像 `while i <= #values do`、`while (x & mask) ~= 0 do` 这类最普通的
    // 条件都会被误打成 repeat/unknown，后面整片 loop state 恢复就只能回退成 label/goto。
    if block_is_while_header_like(proto, cfg, dataflow, header, header_value_merges)
        && branch_has_loop_body_and_exit(cfg, header, blocks)
    {
        return (LoopKindHint::WhileLike, Some(header), None);
    }

    if backedge_sources.len() > 1
        && exits.len() > 1
        && matches!(
            cfg.terminator(&proto.instrs, header),
            Some(LowInstr::Branch(_))
        )
        && !region_has_scope_cleanup(proto, cfg, blocks)
        && exits_are_terminal(proto, cfg, exits)
    {
        // 多个 sibling latch 只是把同一轮尾部短路条件拆成多条回 header 的边；
        // 没有普通 continuation 时，header 本身就是这些回边共同拥有的下一轮入口。
        return (LoopKindHint::WhileTrueLike, Some(header), None);
    }

    if let Some(source) = (backedge_sources.len() == 1)
        .then(|| backedge_sources.iter().next().copied())
        .flatten()
    {
        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump))
                if cfg.instr_to_block[jump.target.index()] == header
        ) && let Some(continue_target) =
            repeat_continue_target_via_backedge_pad(proto, cfg, source, blocks)
        {
            // 先消费“条件 branch -> 纯 backedge pad”的 repeat 协议；若先按
            // terminal exits 把纯 jump latch 判成 while-true，这条更强的尾条件
            // 证据会永久丢失，continue 也只能退化成残余 goto。
            return (LoopKindHint::RepeatLike, Some(continue_target), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Jump(jump)) if cfg.instr_to_block[jump.target.index()] == header
        ) && !region_has_scope_cleanup(proto, cfg, blocks)
            && exits_are_terminal(proto, cfg, exits)
        {
            return (LoopKindHint::WhileTrueLike, Some(source), None);
        }

        if matches!(
            cfg.terminator(&proto.instrs, source),
            Some(LowInstr::Branch(_instr)) if branch_has_header_and_exit(cfg, source, header, blocks)
        ) {
            return (LoopKindHint::RepeatLike, Some(source), None);
        }
    }

    let continue_target = if backedge_sources.len() == 1 {
        backedge_sources.iter().next().copied()
    } else {
        None
    };

    (LoopKindHint::Unknown, continue_target, None)
}

pub(super) fn numeric_for_latch_for_preheader(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    preheader: Option<BlockRef>,
    sources: impl IntoIterator<Item = BlockRef>,
) -> Option<BlockRef> {
    let preheader = preheader?;
    let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
        return None;
    };
    if cfg.instr_to_block[init.body_target.index()] != header {
        return None;
    }

    let mut matches = sources.into_iter().filter(|source| {
        matches!(
            cfg.terminator(&proto.instrs, *source),
            Some(LowInstr::NumericForLoop(loop_instr))
                if numeric_for_instrs_match(proto, cfg, init, loop_instr)
        )
    });
    let source = matches.next()?;
    matches.next().is_none().then_some(source)
}

pub(super) fn region_has_scope_cleanup(
    proto: &LoweredProto,
    cfg: &Cfg,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    blocks.iter().copied().any(|block| {
        let range = cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).any(|instr_index| {
            matches!(
                proto.instrs[instr_index],
                LowInstr::Close(_) | LowInstr::Tbc(_)
            )
        })
    })
}

pub(super) fn exits_are_terminal(
    proto: &LoweredProto,
    cfg: &Cfg,
    exits: &BTreeSet<BlockRef>,
) -> bool {
    exits.iter().copied().all(|exit| {
        let Some(instr_ref) = cfg.blocks[exit.index()].instrs.last() else {
            return exit == cfg.exit_block;
        };
        matches!(
            proto.instrs[instr_ref.index()],
            LowInstr::Return(_) | LowInstr::TailCall(_)
        )
    })
}

pub(super) fn numeric_for_source_bindings(
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

pub(super) fn generic_for_source_bindings(
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

/// 计算源码 loop body 的词法作用域块集合。
///
/// natural loop 拓扑只包含能回到 header 的 body 块，不含通过 return/break
/// 提前离开循环的块；repeat 的条件前分支还可能先进入 nested loop，再回到尾条件。
///
/// 策略：在 candidate.blocks 基础上，追加被 header 严格支配的提前退出区域。
/// for 的 LoopExit 与 repeat 尾条件的循环外后继都是词法边界。while/while-true 不做
/// 扩张，避免把普通 post-loop 和后续 sibling loop 误纳入当前 body。
pub(super) fn loop_body_scope(
    shape: (LoopKindHint, Option<BlockRef>),
    body_blocks: &BTreeSet<BlockRef>,
    exits: &BTreeSet<BlockRef>,
    shared_exit: Option<&SharedExitContinuation>,
    header: BlockRef,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> BTreeSet<BlockRef> {
    let (kind_hint, continue_target) = shape;
    if !matches!(
        kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike | LoopKindHint::RepeatLike
    ) {
        return body_blocks.clone();
    }

    let mut scope = body_blocks.clone();
    let mut scope_boundaries = exits
        .iter()
        .copied()
        .filter(|exit| {
            cfg.preds[exit.index()].iter().any(|edge_ref| {
                let edge = &cfg.edges[edge_ref.index()];
                body_blocks.contains(&edge.from) && edge.kind == EdgeKind::LoopExit
            })
        })
        .collect::<BTreeSet<_>>();
    if kind_hint == LoopKindHint::RepeatLike
        && let Some(continue_target) = continue_target
    {
        scope_boundaries.extend(
            cfg.succs[continue_target.index()]
                .iter()
                .map(|edge_ref| cfg.edges[edge_ref.index()].to)
                .filter(|target| !body_blocks.contains(target)),
        );
    }
    if let Some(shared_exit) = shared_exit {
        scope_boundaries.insert(shared_exit.merge);
    }

    for &exit in exits {
        if exit == header || !graph_facts.dominator_tree.dominates(header, exit) {
            continue;
        }
        let reached_via_loop_exit = cfg.preds[exit.index()].iter().any(|edge_ref| {
            let edge = &cfg.edges[edge_ref.index()];
            body_blocks.contains(&edge.from) && edge.kind == EdgeKind::LoopExit
        });
        if !reached_via_loop_exit {
            scope.extend(loop_binding_early_exit_scope(
                exit,
                header,
                &scope_boundaries,
                cfg,
                graph_facts,
            ));
        }
    }
    scope
}
