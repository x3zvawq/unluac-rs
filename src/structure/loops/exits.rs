//! 分析共享退出 continuation、早退 binding scope 与 loop value merge；依赖透明跳转和 phi 事实，不负责候选分组；例如收敛多条 cleanup exit 到同一 continuation。

use super::*;

pub(super) struct SharedExitContinuation {
    pub(super) merge: BlockRef,
    path_blocks: BTreeSet<BlockRef>,
}

pub(super) struct SharedExitWorkspace {
    seen_marks: Vec<usize>,
    next_path_mark: usize,
    path_counts: Vec<usize>,
    counted_blocks: Vec<BlockRef>,
}

impl SharedExitWorkspace {
    pub(super) fn new(block_count: usize) -> Self {
        Self {
            seen_marks: vec![0; block_count],
            next_path_mark: 0,
            path_counts: vec![0; block_count],
            counted_blocks: Vec::new(),
        }
    }

    pub(super) fn begin_path(&mut self) -> usize {
        self.next_path_mark = self.next_path_mark.wrapping_add(1);
        if self.next_path_mark == 0 {
            self.seen_marks.fill(0);
            self.next_path_mark = 1;
        }
        self.next_path_mark
    }

    pub(super) fn clear_path_counts(&mut self) {
        for block in self.counted_blocks.drain(..) {
            self.path_counts[block.index()] = 0;
        }
    }

    pub(super) fn count_path_block(&mut self, block: BlockRef) {
        let count = &mut self.path_counts[block.index()];
        if *count == 0 {
            self.counted_blocks.push(block);
        }
        *count += 1;
    }
}

pub(super) fn shared_exit_continuation(
    proto: &LoweredProto,
    exits: &BTreeSet<BlockRef>,
    cfg: &Cfg,
    workspace: &mut SharedExitWorkspace,
) -> Option<SharedExitContinuation> {
    if exits.len() < 2 {
        return None;
    }
    let mut paths = Vec::with_capacity(exits.len());
    for exit in exits.iter().copied() {
        let path_mark = workspace.begin_path();
        paths.push(loop_exit_continuation_path(
            proto,
            cfg,
            exit,
            &mut workspace.seen_marks,
            path_mark,
        ));
    }
    workspace.clear_path_counts();
    for path in &paths {
        for block in path {
            workspace.count_path_block(*block);
        }
    }
    let merge = paths.first()?.iter().copied().find(|block| {
        *block != cfg.exit_block && workspace.path_counts[block.index()] == paths.len()
    })?;
    let path_blocks = paths
        .iter()
        .flat_map(|path| path.iter().copied().take_while(|block| *block != merge))
        .collect();
    Some(SharedExitContinuation { merge, path_blocks })
}

pub(super) fn loop_exit_continuation_path(
    proto: &LoweredProto,
    cfg: &Cfg,
    exit: BlockRef,
    seen_marks: &mut [usize],
    path_mark: usize,
) -> Vec<BlockRef> {
    let mut path = vec![exit];
    seen_marks[exit.index()] = path_mark;
    let Some(mut cursor) = cfg.unique_reachable_successor(exit) else {
        return path;
    };
    while seen_marks[cursor.index()] != path_mark {
        seen_marks[cursor.index()] = path_mark;
        path.push(cursor);
        let Some(next) = transparent_loop_exit_target(proto, cfg, cursor) else {
            break;
        };
        cursor = next;
    }
    path
}

pub(super) fn loop_binding_early_exit_scope(
    exit: BlockRef,
    header: BlockRef,
    scope_boundaries: &BTreeSet<BlockRef>,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> BTreeSet<BlockRef> {
    let mut scope = BTreeSet::new();
    let mut stack = vec![exit];

    while let Some(block) = stack.pop() {
        if block == cfg.exit_block
            || scope_boundaries.contains(&block)
            || !graph_facts.dominator_tree.dominates(header, block)
            || !scope.insert(block)
        {
            continue;
        }

        for edge_ref in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge_ref.index()].to;
            if !scope_boundaries.contains(&successor) {
                stack.push(successor);
            }
        }
    }

    scope
}

pub(super) fn analyze_loop_header_value_merges(
    dataflow: &DataflowFacts,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopValueMerge> {
    loop_value_merges_in_block(dataflow, header, loop_blocks)
        .into_iter()
        .filter(loop_value_has_inside_and_outside_incoming)
        .collect()
}

pub(super) fn analyze_loop_exit_value_merges(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    exits: &BTreeSet<BlockRef>,
    shared_exit: Option<&SharedExitContinuation>,
    value_inside_blocks: &BTreeSet<BlockRef>,
    exit_owner_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopExitValueMergeCandidate> {
    let shared_merge = shared_loop_exit_merge(cfg, shared_exit, exit_owner_blocks);
    let shared_merge_block = shared_merge.map(|continuation| continuation.merge);
    let mut candidates = exits
        .iter()
        .copied()
        .filter(|exit| Some(*exit) != shared_merge_block)
        .filter_map(|exit| loop_exit_value_merge_in_block(dataflow, exit, value_inside_blocks))
        .collect::<Vec<_>>();

    if let Some(shared_merge) = shared_merge {
        let mut ownership_blocks = value_inside_blocks.clone();
        ownership_blocks.extend(shared_merge.path_blocks.iter().copied());
        if let Some(candidate) =
            loop_exit_value_merge_in_block(dataflow, shared_merge.merge, &ownership_blocks)
        {
            candidates.push(candidate);
        }
    }
    candidates.sort_by_key(|candidate| candidate.exit);
    candidates
}

pub(super) fn loop_exit_value_merge_in_block(
    dataflow: &DataflowFacts,
    exit: BlockRef,
    ownership_blocks: &BTreeSet<BlockRef>,
) -> Option<LoopExitValueMergeCandidate> {
    let values = loop_value_merges_in_block(dataflow, exit, ownership_blocks)
        .into_iter()
        .filter(|value| !value.inside_arm.is_empty())
        .collect::<Vec<_>>();
    (!values.is_empty()).then_some(LoopExitValueMergeCandidate { exit, values })
}

pub(super) fn shared_loop_exit_merge<'a>(
    cfg: &Cfg,
    continuation: Option<&'a SharedExitContinuation>,
    exit_owner_blocks: &BTreeSet<BlockRef>,
) -> Option<&'a SharedExitContinuation> {
    // 出口块自身可以写回 live-out；只要它们直接汇入同一 block，merge 的 incoming
    // 仍完整对应这些出口。透明性只约束继续跨越的中间 pad，不能反过来丢掉直接合流。
    let continuation = continuation?;
    let path_blocks = &continuation.path_blocks;

    // ownership_blocks 会把这些 predecessor 的完整输出视为 loop 内值；只要某个块还能
    // 从循环外进入，它的输出就可能已经混合外部路径，不能再整项交给 loop owner。
    path_blocks
        .iter()
        .all(|block| {
            cfg.preds[block.index()].iter().all(|edge| {
                let pred = cfg.edges[edge.index()].from;
                !cfg.reachable_blocks.contains(&pred)
                    || exit_owner_blocks.contains(&pred)
                    || path_blocks.contains(&pred)
            })
        })
        .then_some(continuation)
}

pub(in crate::structure) fn transparent_loop_exit_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> Option<BlockRef> {
    if let Some(target) = transparent_jump_target(proto, cfg, block) {
        return Some(target);
    }
    let range = cfg.blocks[block.index()].instrs;
    if range.is_empty()
        || (range.start.index()..range.end())
            .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
    {
        return None;
    }
    cfg.unique_reachable_successor(block)
}

pub(super) fn loop_value_has_inside_and_outside_incoming(value: &LoopValueMerge) -> bool {
    !value.inside_arm.is_empty() && !value.outside_arm.is_empty()
}

pub(super) fn unique_loop_preheader(
    cfg: &Cfg,
    header: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    cfg.unique_reachable_predecessor_matching(header, |pred| !loop_blocks.contains(&pred))
}

pub(super) fn branch_has_loop_body_and_exit(
    cfg: &Cfg,
    header: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> bool {
    let Some((then_edge_ref, else_edge_ref)) = cfg.branch_edges(header) else {
        return false;
    };
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    (blocks.contains(&then_block) && !blocks.contains(&else_block))
        || (!blocks.contains(&then_block) && blocks.contains(&else_block))
}

pub(super) fn branch_has_header_and_exit(
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

pub(super) fn block_is_while_header_like(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: BlockRef,
    header_value_merges: &[LoopValueMerge],
) -> bool {
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

    let carried_regs = header_value_merges
        .iter()
        .map(|value| value.reg)
        .collect::<BTreeSet<_>>();
    let terminator_index = range.end() - 1;
    let Some(branch_effect) = dataflow.instr_effects.get(terminator_index) else {
        return false;
    };
    let mut needed_regs = branch_effect.fixed_uses.clone();

    (range.start.index()..terminator_index)
        .rev()
        .all(|instr_index| {
            let instr = &proto.instrs[instr_index];
            let Some(effect) = dataflow.instr_effects.get(instr_index) else {
                return false;
            };
            if carried_regs.iter().any(|reg| effect.must_define(*reg))
                || !instr_is_while_header_prefix(instr)
            {
                return false;
            }
            let writes_needed = needed_regs.iter().any(|reg| effect.must_define(*reg));
            if !writes_needed {
                return dataflow
                    .effect_summaries
                    .get(instr_index)
                    .is_some_and(|summary| summary.tags.is_empty());
            }

            for reg in &effect.fixed_must_defs {
                needed_regs.remove(reg);
            }
            if let Some(open_def) = effect.open_must_def {
                needed_regs.retain(|reg| reg.index() < open_def.index());
            }
            needed_regs.extend(effect.fixed_uses.iter().copied());
            if let Some(open_use) = effect.open_use {
                needed_regs.insert(open_use);
            }
            true
        })
}

/// while 条件求值中不可能出现的指令。这些指令要么是控制流终结指令（已由
/// terminator 位置单独处理），要么是纯副作用写出指令（SetUpvalue / SetTable /
/// SetList），要么是 scope 管理指令（Close / Tbc），不可能出现在 Lua 编译器
/// 为 expression 上下文生成的条件求值序列里。
///
/// 使用排除列表而非允许列表，避免新增 LowInstr 变体时遗漏导致合法的 while
/// 条件被误判为 repeat/unknown。
pub(super) fn instr_is_while_header_prefix(instr: &LowInstr) -> bool {
    !matches!(
        instr,
        LowInstr::SetUpvalue(_)
            | LowInstr::SetTable(_)
            | LowInstr::SetList(_)
            | LowInstr::TailCall(_)
            | LowInstr::Return(_)
            | LowInstr::Close(_)
            | LowInstr::Tbc(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForPrep(_)
            | LowInstr::GenericForCall(_)
            | LowInstr::GenericForLoop(_)
            | LowInstr::Jump(_)
            | LowInstr::Branch(_)
    )
}

pub(super) fn repeat_continue_target_via_backedge_pad(
    proto: &LoweredProto,
    cfg: &Cfg,
    backedge_source: BlockRef,
    blocks: &BTreeSet<BlockRef>,
) -> Option<BlockRef> {
    // 条件 branch 后的纯 jump/close pad 可以属于 repeat 控制；普通赋值或调用则仍是
    // while/retry body 的尾部，若把它当条件 pad，HIR 会跳过本轮副作用。
    transparent_jump_target(proto, cfg, backedge_source)?;
    let continue_target =
        cfg.unique_reachable_predecessor_matching(backedge_source, |pred| blocks.contains(&pred))?;

    if !matches!(
        cfg.terminator(&proto.instrs, continue_target),
        Some(LowInstr::Branch(_))
    ) {
        return None;
    }

    let (then_edge_ref, else_edge_ref) = cfg.branch_edges(continue_target)?;
    let then_block = cfg.edges[then_edge_ref.index()].to;
    let else_block = cfg.edges[else_edge_ref.index()].to;

    if (then_block == backedge_source && !blocks.contains(&else_block))
        || (else_block == backedge_source && !blocks.contains(&then_block))
    {
        Some(continue_target)
    } else {
        None
    }
}

pub(super) fn transparent_jump_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> Option<BlockRef> {
    let range = cfg.blocks[block.index()].instrs;
    let last = range.last()?;
    let LowInstr::Jump(jump) = &proto.instrs[last.index()] else {
        return None;
    };
    if (range.start.index()..last.index())
        .any(|instr_index| !matches!(proto.instrs[instr_index], LowInstr::Close(_)))
    {
        return None;
    }
    Some(cfg.instr_to_block[jump.target.index()])
}

pub(super) fn generic_for_has_loop_body_and_exit(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: BlockRef,
    instr: &GenericForLoopInstr,
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

    call.control == instr.control_target
        && matches!(call.results, crate::transformer::ResultPack::Fixed(range) if range == instr.bindings)
        && (generic_for_immediate_break(proto, cfg, instr) || blocks.contains(&body_block))
        && !blocks.contains(&exit_block)
}
