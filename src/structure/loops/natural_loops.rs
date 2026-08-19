//! 分割 natural-loop 域并匹配 numeric-for latch；依赖支配/SCC 与 lowered 指令，不负责最终循环语法；例如把同 header 多回边归为一个控制身份。

use super::*;

pub(in crate::structure) fn branch_conditions_share_subject(
    proto: &LoweredProto,
    cfg: &Cfg,
    left: BlockRef,
    right: BlockRef,
) -> bool {
    let (Some(LowInstr::Branch(left)), Some(LowInstr::Branch(right))) = (
        cfg.terminator(&proto.instrs, left),
        cfg.terminator(&proto.instrs, right),
    ) else {
        return false;
    };
    left.cond.subject == right.cond.subject
}

pub(super) fn reachable_numeric_for_loop(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    domain_workspace: &mut NaturalLoopDomainWorkspace,
    natural_loop: &crate::structure::NaturalLoop,
) -> Option<Vec<LoopCandidate>> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    } = *context;
    let natural_header = natural_loop.header;
    let mut matches = natural_loop
        .backedges
        .iter()
        .copied()
        .filter_map(|backedge| {
            let latch = cfg.edges[backedge.index()].from;
            let LowInstr::NumericForLoop(loop_instr) = cfg.terminator(&proto.instrs, latch)? else {
                return None;
            };
            numeric_for_owner(proto, cfg, natural_header, loop_instr)
                .map(|(header, preheader)| (backedge, header, preheader))
        });
    let (protocol_backedge, header, preheader) = matches.next()?;
    if matches.next().is_some() {
        // 同一控制身份出现多个互相冲突的 VM numeric latch 时，不能任选其一后
        // 静默丢掉其余回边；保守交回普通 merged loop，让最终 plan 决定结构或 island。
        return None;
    }
    let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
        return None;
    };
    let exit = cfg.instr_to_block[init.exit_target.index()];
    let latch = cfg.edges[protocol_backedge.index()].from;
    let LowInstr::NumericForLoop(loop_instr) = cfg.terminator(&proto.instrs, latch)? else {
        return None;
    };
    let latch_exit = cfg.instr_to_block[loop_instr.exit_target.index()];
    let duplicated_terminal_exit = latch_exit != exit
        && equivalent_single_return_targets(proto, cfg, loop_instr.exit_target, init.exit_target);

    let mut blocks = collect_forward_region_blocks(
        cfg,
        [header],
        Some(exit),
        Some((header, &graph_facts.dominator_tree)),
    );
    if duplicated_terminal_exit {
        blocks.remove(&latch_exit);
    }
    blocks.insert(latch);
    if !natural_loop.blocks.is_subset(&blocks) || !is_reducible_region(cfg, header, &blocks) {
        return None;
    }

    let residual_backedges = natural_loop
        .backedges
        .iter()
        .copied()
        .filter(|backedge| *backedge != protocol_backedge)
        .collect::<Vec<_>>();
    let residual_blocks = if residual_backedges.is_empty() {
        None
    } else {
        Some(natural_loop_domain_for_backedges(
            cfg,
            natural_loop,
            &residual_backedges,
            domain_workspace,
        )?)
    };
    if residual_blocks.as_ref().is_some_and(|residual| {
        !residual_cycle_is_nested(cfg, natural_loop, residual, &residual_backedges)
    }) {
        // residual cycle 与 VM latch 无法形成严格的 containment 分区时，不能任选一个
        // 回边当 numeric-for；交回 merged candidate，最终 plan 会结构化或形成 island。
        return None;
    }

    let mut candidate = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        blocks,
        vec![protocol_backedge],
    );
    if duplicated_terminal_exit {
        candidate.exits.insert(exit);
        candidate.control_blocks.insert(latch_exit);
        candidate.normalized_exit_aliases.push(LoopExitAlias {
            block: latch_exit,
            continuation: exit,
        });
        let shared_exit =
            shared_exit_continuation(proto, &candidate.exits, cfg, shared_exit_workspace);
        candidate.exit_value_merges = analyze_loop_exit_value_merges(
            cfg,
            dataflow,
            &candidate.exits,
            shared_exit.as_ref(),
            &candidate.blocks,
            &candidate.blocks,
        );
    }
    if candidate.kind_hint != LoopKindHint::NumericForLike
        || candidate.preheader != Some(preheader)
        || !candidate.exits.contains(&exit)
    {
        return None;
    }
    if latch_exit != exit && !duplicated_terminal_exit {
        candidate.control_blocks.insert(latch_exit);
    }
    let mut partition = Vec::with_capacity(1 + usize::from(residual_blocks.is_some()));
    if let Some(residual_blocks) = residual_blocks {
        let mut child = build_loop_candidate(
            context,
            shared_exit_workspace,
            natural_header,
            residual_blocks,
            residual_backedges,
        );
        // header phi 同时可见于 wrapper 与 child，但 canonical loop-carried owner 只能是
        // VM-for wrapper；child 只负责 residual control cycle。
        child.header_value_merges.clear();
        partition.push(child);
    }
    partition.push(candidate);
    Some(partition)
}

pub(super) fn partition_repeat_like_natural_loop(
    context: &LoopAnalysisContext<'_>,
    shared_exit_workspace: &mut SharedExitWorkspace,
    domain_workspace: &mut NaturalLoopDomainWorkspace,
    natural_loop: &crate::structure::NaturalLoop,
) -> Option<Vec<LoopCandidate>> {
    let LoopAnalysisContext {
        proto,
        cfg,
        graph_facts: _,
        dataflow: _,
    } = *context;
    if natural_loop.backedges.len() < 2 {
        return None;
    }
    let header = natural_loop.header;
    let (outer_backedges, residual_backedges): (Vec<_>, Vec<_>) = natural_loop
        .backedges
        .iter()
        .copied()
        .partition(|backedge| {
            let source = cfg.edges[backedge.index()].from;
            branch_has_header_and_exit(cfg, source, header, &natural_loop.blocks)
                || repeat_continue_target_via_backedge_pad(proto, cfg, source, &natural_loop.blocks)
                    .is_some()
        });
    if outer_backedges.is_empty() || residual_backedges.is_empty() {
        return None;
    }

    let residual_blocks = natural_loop_domain_for_backedges(
        cfg,
        natural_loop,
        &residual_backedges,
        domain_workspace,
    )?;
    if !residual_cycle_is_nested(cfg, natural_loop, &residual_blocks, &residual_backedges) {
        return None;
    }

    let mut child = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        residual_blocks,
        residual_backedges,
    );
    child.header_value_merges.clear();
    let outer = build_loop_candidate(
        context,
        shared_exit_workspace,
        header,
        natural_loop.blocks.clone(),
        outer_backedges,
    );
    Some(vec![child, outer])
}

pub(super) struct NaturalLoopDomainWorkspace {
    marks: Vec<usize>,
    next_mark: usize,
}

impl NaturalLoopDomainWorkspace {
    pub(super) fn new(block_count: usize) -> Self {
        Self {
            marks: vec![0; block_count],
            next_mark: 0,
        }
    }

    pub(super) fn begin(&mut self) -> usize {
        self.next_mark = self.next_mark.wrapping_add(1);
        if self.next_mark == 0 {
            self.marks.fill(0);
            self.next_mark = 1;
        }
        self.next_mark
    }
}

pub(super) fn natural_loop_domain_for_backedges(
    cfg: &Cfg,
    natural_loop: &crate::structure::NaturalLoop,
    backedges: &[EdgeRef],
    workspace: &mut NaturalLoopDomainWorkspace,
) -> Option<BTreeSet<BlockRef>> {
    let mark = workspace.begin();
    let header = natural_loop.header;
    let mut blocks = BTreeSet::from([header]);
    let mut worklist = Vec::with_capacity(backedges.len());
    workspace.marks[header.index()] = mark;

    for backedge in backedges {
        let edge = cfg.edges.get(backedge.index())?;
        if edge.to != header || !natural_loop.blocks.contains(&edge.from) {
            return None;
        }
        if workspace.marks[edge.from.index()] != mark {
            workspace.marks[edge.from.index()] = mark;
            blocks.insert(edge.from);
            worklist.push(edge.from);
        }
    }

    while let Some(block) = worklist.pop() {
        for pred_edge in &cfg.preds[block.index()] {
            let pred = cfg.edges[pred_edge.index()].from;
            if !natural_loop.blocks.contains(&pred) || workspace.marks[pred.index()] == mark {
                continue;
            }
            workspace.marks[pred.index()] = mark;
            blocks.insert(pred);
            worklist.push(pred);
        }
    }
    Some(blocks)
}

pub(super) fn residual_cycle_is_nested(
    cfg: &Cfg,
    natural_loop: &crate::structure::NaturalLoop,
    residual: &BTreeSet<BlockRef>,
    residual_backedges: &[EdgeRef],
) -> bool {
    if residual == &natural_loop.blocks
        || residual.len() <= 1
        || !is_reducible_region(cfg, natural_loop.header, residual)
        || !collect_region_exits(cfg, residual).is_subset(&natural_loop.blocks)
    {
        return false;
    }

    let successors = cfg.succs[natural_loop.header.index()]
        .iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<BTreeSet<_>>();
    if successors.len() <= 1 {
        return true;
    }
    if successors.len() != 2
        || successors
            .iter()
            .filter(|block| residual.contains(block))
            .count()
            != 1
    {
        return false;
    }
    let Some(outer_only_start) = successors
        .iter()
        .copied()
        .find(|block| !residual.contains(block))
        .map(|block| cfg.blocks[block.index()].instrs.start.index())
    else {
        return false;
    };

    // 两条 sibling latch 也可能各自带“回 header / 离开循环”的局部分支。真正的
    // nested residual 在布局上先完成内层回边，再进入 outer-only arm；若 residual
    // latch 已位于 outer arm 之后，它只是同一轮的另一条 sibling 路径。
    residual_backedges.iter().all(|backedge| {
        let source = cfg.edges[backedge.index()].from;
        cfg.blocks[source.index()].instrs.end() <= outer_only_start
    })
}

pub(super) fn numeric_for_owner(
    proto: &LoweredProto,
    cfg: &Cfg,
    natural_header: BlockRef,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> Option<(BlockRef, BlockRef)> {
    let mut body_entries = BTreeSet::from([natural_header]);
    body_entries.extend(
        cfg.reachable_predecessors(natural_header)
            .into_iter()
            .filter(|body| {
                *body != natural_header
                    && matches!(
                        cfg.terminator(&proto.instrs, *body),
                        Some(LowInstr::Jump(jump))
                            if cfg.instr_to_block[jump.target.index()] == natural_header
                    )
            }),
    );

    let mut owners = body_entries.into_iter().flat_map(|header| {
        cfg.reachable_predecessors(header)
            .into_iter()
            .filter_map(
                move |preheader| match cfg.terminator(&proto.instrs, preheader) {
                    Some(LowInstr::NumericForInit(init))
                        if numeric_for_instrs_match(proto, cfg, init, loop_instr) =>
                    {
                        Some((header, preheader))
                    }
                    _ => None,
                },
            )
    });
    let owner = owners.next()?;
    owners.next().is_none().then_some(owner)
}

pub(super) fn numeric_for_instrs_match(
    proto: &LoweredProto,
    cfg: &Cfg,
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> bool {
    numeric_for_state_matches(init, loop_instr)
        && (loop_instr.body_target == init.body_target
            || matches!(
                cfg.terminator(&proto.instrs, cfg.instr_to_block[init.body_target.index()]),
                Some(LowInstr::Jump(jump))
                    if cfg.instr_to_block[jump.target.index()]
                        == cfg.instr_to_block[loop_instr.body_target.index()]
            ))
        && same_or_equivalent_exit_target(proto, cfg, loop_instr.exit_target, init.exit_target)
}

pub(super) fn numeric_for_state_matches(
    init: &crate::transformer::NumericForInitInstr,
    loop_instr: &crate::transformer::NumericForLoopInstr,
) -> bool {
    numeric_for_init_state(init) == numeric_for_loop_state(loop_instr)
}

pub(super) type NumericForState = (Reg, Reg, Reg, Reg);
pub(super) type NumericForLatchIndex<'a> =
    BTreeMap<NumericForState, Vec<(BlockRef, &'a crate::transformer::NumericForLoopInstr)>>;

pub(super) fn numeric_for_init_state(
    instr: &crate::transformer::NumericForInitInstr,
) -> NumericForState {
    (instr.index, instr.limit, instr.step, instr.binding)
}

pub(super) fn numeric_for_loop_state(
    instr: &crate::transformer::NumericForLoopInstr,
) -> NumericForState {
    (instr.index, instr.limit, instr.step, instr.binding)
}

pub(super) fn index_numeric_for_latches<'a>(
    proto: &'a LoweredProto,
    cfg: &Cfg,
) -> NumericForLatchIndex<'a> {
    let mut latches = NumericForLatchIndex::new();
    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::NumericForLoop(loop_instr) = instr else {
            continue;
        };
        latches
            .entry(numeric_for_loop_state(loop_instr))
            .or_default()
            .push((cfg.instr_to_block[instr_index], loop_instr));
    }
    latches
}
