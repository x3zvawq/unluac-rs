//! 这个文件承载 HIR 结构恢复的主体实现。
//!
//! 外层 `structure/mod.rs` 只负责做入口和模块拼装，这里集中放真正的分支/merge/region
//! 结构恢复逻辑。这样后续继续拆 `branch merge`、`loop exits` 之类的细节时，
//! 不会再把 facade 文件重新撑回一个巨型实现。

mod branch_exit_assignments;
mod branch_stops;
mod branches;
mod entry_overrides;
mod escapes;
mod loop_controls;
mod path_checks;
mod prefix_temps;
mod short_circuits;
mod value_merges;

use std::{cell::RefCell, ops::Range};

use super::*;

/// 尝试基于现有结构候选恢复一个更接近源码的 HIR block。
pub(super) fn build_structured_body(
    target: AstTargetDialect,
    lowering: &ProtoLowering<'_>,
) -> Option<HirBlock> {
    if lowering
        .structure
        .goto_requirements
        .iter()
        .any(|requirement| !supports_structured_goto_requirement(requirement.reason))
    {
        return None;
    }

    let mut lowerer = StructuredBodyLowerer::new(target, lowering);
    let body = lowerer.lower_region(lowering.cfg.entry_block, None, &BTreeMap::new())?;
    lowerer.all_reachable_blocks_covered().then_some(body)
}

pub(super) struct StructuredBodyLowerer<'a, 'b> {
    pub(super) target: AstTargetDialect,
    pub(super) lowering: &'b ProtoLowering<'a>,
    pub(super) branch_by_header: BTreeMap<BlockRef, &'b BranchCandidate>,
    pub(super) branch_regions_by_header: BTreeMap<BlockRef, &'b BranchRegionFact>,
    pub(super) branch_value_merges_by_header: BTreeMap<BlockRef, &'b BranchValueMergeCandidate>,
    pub(super) loop_by_header: BTreeMap<BlockRef, &'b LoopCandidate>,
    pub(super) label_map: BTreeMap<BlockRef, HirLabelId>,
    pub(super) required_labels: BTreeSet<BlockRef>,
    pub(super) merge_allowed_blocks: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    pub(super) overrides: StructureOverrideState,
    pub(super) structured_close_points: BTreeSet<InstrRef>,
    pub(super) tbc_scope_regs: BTreeSet<usize>,
    pub(super) visited: BTreeSet<BlockRef>,
    pub(super) active_loops: Vec<ActiveLoopContext>,
    reachability: RefCell<BTreeMap<(BlockRef, BlockRef), bool>>,
}

#[derive(Debug)]
pub(super) struct StructuredBranchPlan {
    pub(super) cond: HirExpr,
    pub(super) then_entry: BlockRef,
    pub(super) else_entry: Option<BlockRef>,
    pub(super) merge: Option<BlockRef>,
    pub(super) consumed_headers: Vec<BlockRef>,
    // 短路候选的语义节点只包含条件 header；某些出口会先经过空 jump pad 再到
    // truthy/falsy 出口。pad 不参与条件重写，但需要计入覆盖性检查。
    pub(super) consumed_blocks: Vec<BlockRef>,
}

#[derive(Debug, Clone)]
pub(super) struct LoopStateSlot {
    pub(super) phi_id: Option<PhiId>,
    pub(super) reg: Reg,
    pub(super) target: HirLValue,
    pub(super) init: HirExpr,
}

#[derive(Debug, Clone, Default)]
pub(super) struct LoopStatePlan {
    pub(super) states: Vec<LoopStateSlot>,
    pub(super) backedge_target_overrides: BTreeMap<TempId, HirLValue>,
}

#[derive(Debug, Clone)]
pub(super) struct ActiveLoopContext {
    pub(super) header: BlockRef,
    pub(super) loop_blocks: BTreeSet<BlockRef>,
    pub(super) post_loop: BlockRef,
    pub(super) downstream_post_loop: Option<BlockRef>,
    pub(super) continue_target: Option<BlockRef>,
    pub(super) continue_sources: BTreeSet<BlockRef>,
    pub(super) break_exits: BTreeMap<BlockRef, BreakExitBlock>,
    pub(super) state_slots: Vec<LoopStateSlot>,
}

#[derive(Debug, Clone)]
pub(super) struct BreakExitBlock {
    pub(super) block: HirBlock,
    pub(super) blocks: BTreeSet<BlockRef>,
}

#[derive(Debug, Clone)]
pub(super) struct StructureStateCheckpoint {
    required_labels: BTreeSet<BlockRef>,
    merge_allowed_blocks: BTreeMap<BlockRef, BTreeSet<BlockRef>>,
    overrides: StructureOverrideState,
    visited: BTreeSet<BlockRef>,
    active_loops: Vec<ActiveLoopContext>,
    stmts_len: usize,
}

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn checkpoint_state(&self, stmts_len: usize) -> StructureStateCheckpoint {
        StructureStateCheckpoint {
            required_labels: self.required_labels.clone(),
            merge_allowed_blocks: self.merge_allowed_blocks.clone(),
            overrides: self.overrides.clone(),
            visited: self.visited.clone(),
            active_loops: self.active_loops.clone(),
            stmts_len,
        }
    }

    pub(super) fn restore_state_checkpoint(
        &mut self,
        checkpoint: StructureStateCheckpoint,
        stmts: &mut Vec<HirStmt>,
    ) {
        self.required_labels = checkpoint.required_labels;
        self.merge_allowed_blocks = checkpoint.merge_allowed_blocks;
        self.overrides = checkpoint.overrides;
        self.visited = checkpoint.visited;
        self.active_loops = checkpoint.active_loops;
        stmts.truncate(checkpoint.stmts_len);
    }

    fn new(target: AstTargetDialect, lowering: &'b ProtoLowering<'a>) -> Self {
        let branch_by_header = lowering
            .structure
            .branch_candidates
            .iter()
            .map(|candidate| (candidate.header, candidate))
            .collect();
        let branch_value_merges_by_header =
            unique_branch_value_merges_by_header(&lowering.structure.branch_value_merge_candidates);
        let branch_regions_by_header = lowering
            .structure
            .branch_region_facts
            .iter()
            .map(|fact| (fact.header, fact))
            .collect();
        let loop_by_header = lowering
            .structure
            .loop_candidates
            .iter()
            .map(|candidate| (candidate.header, candidate))
            .collect();
        let structured_close_points = lowering
            .structure
            .scope_candidates
            .iter()
            .flat_map(|scope| scope.close_points.iter().copied())
            .collect();
        let tbc_scope_regs = lowering
            .proto
            .instrs
            .iter()
            .filter_map(|instr| match instr {
                LowInstr::Tbc(tbc) => Some(tbc.reg.index()),
                _ => None,
            })
            .collect();

        Self {
            target,
            lowering,
            branch_by_header,
            branch_regions_by_header,
            branch_value_merges_by_header,
            loop_by_header,
            label_map: build_label_map_for_summary(lowering.cfg),
            required_labels: BTreeSet::new(),
            merge_allowed_blocks: BTreeMap::new(),
            overrides: StructureOverrideState::default(),
            structured_close_points,
            tbc_scope_regs,
            visited: BTreeSet::new(),
            active_loops: Vec::new(),
            reachability: RefCell::new(BTreeMap::new()),
        }
    }

    pub(super) fn can_reach(&self, from: BlockRef, to: BlockRef) -> bool {
        let key = (from, to);
        if let Some(can_reach) = self.reachability.borrow().get(&key).copied() {
            return can_reach;
        }

        let can_reach = self.lowering.cfg.can_reach(from, to);
        self.reachability.borrow_mut().insert(key, can_reach);
        can_reach
    }

    fn all_reachable_blocks_covered(&self) -> bool {
        self.lowering
            .cfg
            .block_order
            .iter()
            .filter(|block| self.lowering.cfg.reachable_blocks.contains(block))
            .filter(|block| **block != self.lowering.cfg.exit_block)
            .all(|block| self.visited.contains(block))
    }

    pub(super) fn can_emit_continue_stmt(&self) -> bool {
        self.target.caps.continue_stmt
    }

    pub(super) fn explicit_continue_block(&self) -> Option<HirBlock> {
        self.can_emit_continue_stmt().then(|| HirBlock {
            stmts: vec![HirStmt::Continue],
        })
    }

    pub(super) fn lower_region(
        &mut self,
        start: BlockRef,
        stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        self.lower_region_with_suppressed_loop(start, stop, target_overrides, None)
    }

    pub(super) fn lower_region_with_suppressed_loop(
        &mut self,
        start: BlockRef,
        stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
        suppressed_loop_header: Option<BlockRef>,
    ) -> Option<HirBlock> {
        let mut current = Some(start);
        let mut stmts = Vec::new();

        while let Some(block) = current {
            if Some(block) == stop || block == self.lowering.cfg.exit_block {
                break;
            }
            if let Some(loop_escape_stmts) = self.active_loop_escape_stmts(block) {
                stmts.extend(loop_escape_stmts);
                break;
            }
            if !self.lowering.cfg.reachable_blocks.contains(&block) {
                return None;
            }
            if self.visited.contains(&block) {
                if self.block_is_terminal_exit(block) {
                    // 终止 return 块没有 fallthrough；多条源码路径共享同一个 return 尾块时，
                    // 后到达的路径可以安全克隆这段终止语句，而不应让整颗 proto 回退成
                    // label/goto fallback。每条运行时路径仍只执行一次 return。
                    let cloned = self.lower_terminal_exit_block_clone(block, target_overrides)?;
                    stmts.extend(cloned.stmts);
                    break;
                }
                if let Some(stop) = stop
                    && let Some(cloned) =
                        self.lower_shared_stop_tail_block_clone(block, stop, target_overrides)
                {
                    stmts.extend(cloned.stmts);
                    break;
                }
                return None;
            }

            self.emit_required_label(block, &mut stmts);

            if self.loop_by_header.contains_key(&block) && Some(block) != suppressed_loop_header {
                current = self.lower_loop(block, stop, &mut stmts, target_overrides)?;
            } else if self.branch_by_header.contains_key(&block) {
                current = self.lower_branch(block, stop, &mut stmts, target_overrides)?;
            } else {
                current = self.lower_linear_block(block, stop, &mut stmts, target_overrides)?;
            }
        }

        Some(HirBlock { stmts })
    }

    fn emit_required_label(&self, block: BlockRef, stmts: &mut Vec<HirStmt>) {
        if !self.required_labels.contains(&block) {
            return;
        }
        stmts.push(HirStmt::Label(Box::new(HirLabel {
            id: self.label_map[&block],
        })));
    }

    fn lower_linear_block(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) = self.try_lower_numeric_for_init(block, stop, stmts, target_overrides) {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_generic_for_preheader(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        self.visited.insert(block);
        stmts.extend(self.lower_block_prefix(block, false, target_overrides)?);

        let Some((instr_ref, instr)) = self.block_terminator(block) else {
            return self.next_linear_successor(block, stop);
        };

        if !is_control_terminator(instr) {
            return self.next_linear_successor(block, stop);
        }

        match instr {
            LowInstr::Jump(jump) => {
                let target = self.lowering.cfg.instr_to_block[jump.target.index()];
                self.follow_linear_target(block, target, stop, stmts)
            }
            LowInstr::Branch(branch)
                if self.lowering.cfg.instr_to_block[branch.then_target.index()]
                    == self.lowering.cfg.instr_to_block[branch.else_target.index()] =>
            {
                let target = self.lowering.cfg.instr_to_block[branch.then_target.index()];
                self.follow_linear_target(block, target, stop, stmts)
            }
            LowInstr::Return(_) | LowInstr::TailCall(_) => {
                let empty_labels = BTreeMap::new();
                let mut lowered =
                    lower_control_instr(self.lowering, block, instr_ref, instr, &empty_labels);
                // return/tail-call 虽然是控制终结指令，但它们读取的表达式同样可能来自
                // loop state。这里必须和普通前缀指令一样应用 target overrides，否则
                // `return carried` 会退回成未物化的 phi temp。
                apply_loop_rewrites(&mut lowered, target_overrides);
                if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
                    for stmt in &mut lowered {
                        rewrite_stmt_exprs(stmt, entry_expr_overrides);
                    }
                }
                stmts.extend(lowered);
                Some(None)
            }
            LowInstr::Branch(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_) => None,
            _ => None,
        }
    }

    fn follow_linear_target(
        &mut self,
        block: BlockRef,
        target: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
    ) -> Option<Option<BlockRef>> {
        if Some(target) == stop || target == self.lowering.cfg.exit_block {
            return Some(if target == self.lowering.cfg.exit_block {
                None
            } else {
                Some(target)
            });
        }
        if let Some(loop_context) = self.active_loops.last() {
            if loop_context.continue_target == Some(target)
                && loop_context.continue_sources.contains(&block)
                && self.loop_continue_target_is_empty(target)
            {
                if !self.can_emit_continue_stmt() {
                    return None;
                }
                stmts.push(HirStmt::Continue);
                return Some(None);
            }
            if target == loop_context.header {
                return Some(None);
            }
            // Lua 5.2+ 的 loop break 常常直接跳到 post-loop continuation，
            // 而不会先经过额外的 break pad。这里如果继续把它当普通线性 successor，
            // body lowering 就会错误地走出当前 loop，最终把 numeric-for/while
            // 整体打回 unresolved。对当前活跃 loop 来说，这条边的语义就是 break。
            if target == loop_context.post_loop {
                stmts.push(HirStmt::Break);
                return Some(None);
            }
            if Some(target) == loop_context.downstream_post_loop {
                stmts.push(HirStmt::Break);
                return Some(None);
            }
            if let Some(break_block) = loop_context.break_exits.get(&target) {
                stmts.extend(break_block.block.stmts.clone());
                self.visited.extend(break_block.blocks.iter().copied());
                return Some(None);
            }
        }
        if self.lowering.cfg.reachable_blocks.contains(&target) {
            Some(Some(target))
        } else {
            None
        }
    }

    pub(super) fn lower_block_prefix(
        &self,
        block: BlockRef,
        expect_branch_terminator: bool,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Vec<HirStmt>> {
        let empty_allowed_blocks = BTreeSet::new();
        let allowed_blocks = self
            .merge_allowed_blocks
            .get(&block)
            .unwrap_or(&empty_allowed_blocks);
        let overridden_phis = self.overrides.block_phi_exprs(block);
        let mut stmts = overridden_phis
            .into_iter()
            .flat_map(|phi_exprs| phi_exprs.iter())
            .map(|(phi_id, value)| {
                let temp = self.lowering.bindings.phi_temps[phi_id.index()];
                assign_stmt(vec![HirLValue::Temp(temp)], vec![value.clone()])
            })
            .collect::<Vec<_>>();
        stmts.extend(lower_phi_materialization_with_allowed_blocks_except(
            self.lowering,
            block,
            |phi_id| self.overrides.phi_is_suppressed_for_block(block, phi_id),
            allowed_blocks,
        ));
        // phi 物化语句里的 TempRef 和赋值目标都可能引用被 target_overrides
        // 重定向过的 temp。典型场景：内层短路的 phi temp 被外层 BVM 收编后，
        // 物化结果的写入目标需要跟着改到外层 BVM 的 arm target。
        if !target_overrides.is_empty() {
            let phi_expr_overrides = temp_expr_overrides(target_overrides);
            for stmt in &mut stmts {
                rewrite_stmt_exprs(stmt, &phi_expr_overrides);
                rewrite_stmt_targets(stmt, target_overrides);
            }
        }
        let entry_expr_overrides = self.block_entry_expr_overrides(block);
        for instr_index in self.block_prefix_instr_indices(block, expect_branch_terminator)? {
            let instr_ref = InstrRef(instr_index);
            let instr = &self.lowering.proto.instrs[instr_index];
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            // `Close` 只在 low-IR 里显式出现；一旦结构层已经用 `scope_candidates` 证明
            // 这些 cleanup 点属于某个词法边界，HIR 就不该继续把它们暴露成伪语句。
            // 否则 while/repeat/if 已经结构化了，dump 里仍会残留“close from rX”的噪音，
            // 迫使后面的 AST/readability 再去反推这其实只是作用域结束。
            if self.structured_close_points.contains(&instr_ref)
                && matches!(instr, LowInstr::Close(close) if !self.tbc_scope_regs.contains(&close.from.index()))
            {
                continue;
            }
            let mut lowered = lower_regular_instr(self.lowering, block, instr_ref, instr);
            apply_loop_rewrites(&mut lowered, target_overrides);
            if let Some(entry_expr_overrides) = entry_expr_overrides {
                for stmt in &mut lowered {
                    rewrite_stmt_exprs(stmt, entry_expr_overrides);
                }
            }
            stmts.extend(lowered);
        }

        Some(stmts)
    }

    fn lower_shared_stop_tail_block_clone(
        &self,
        block: BlockRef,
        stop: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if self.required_labels.contains(&block)
            || self.branch_by_header.contains_key(&block)
            || self.loop_by_header.contains_key(&block)
            || !self
                .lowering
                .dataflow
                .phi_candidates_in_block(block)
                .is_empty()
            || self.lowering.cfg.unique_reachable_successor(block) != Some(stop)
        {
            return None;
        }
        if let Some((_instr_ref, instr)) = self.block_terminator(block)
            && is_control_terminator(instr)
            && !matches!(instr, LowInstr::Jump(_))
        {
            return None;
        }

        // 多个嵌套分支可共享同一个直线 continuation block。这里复制的是“到当前
        // stop 为止”的无 phi 线性尾块，运行时仍只会沿被选中的分支执行一次。
        Some(HirBlock {
            stmts: self.lower_block_prefix(block, false, target_overrides)?,
        })
    }

    pub(in crate::hir::analyze::structure) fn build_plain_branch_plan(
        &self,
        block: BlockRef,
    ) -> Option<StructuredBranchPlan> {
        let candidate = *self.branch_by_header.get(&block)?;

        match candidate.kind {
            BranchKind::IfElse => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: candidate.else_entry,
                merge: candidate.merge,
                consumed_headers: vec![block],
                consumed_blocks: vec![block],
            }),
            BranchKind::IfThen | BranchKind::Guard => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: None,
                merge: candidate.merge,
                consumed_headers: vec![block],
                consumed_blocks: vec![block],
            }),
        }
    }

    pub(super) fn lower_candidate_cond(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
    ) -> Option<HirExpr> {
        self.lower_branch_cond_for_target(block, candidate.then_entry)
    }

    pub(super) fn lower_branch_cond_for_target(
        &self,
        block: BlockRef,
        target: BlockRef,
    ) -> Option<HirExpr> {
        let (instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::Branch(branch) = instr else {
            return None;
        };
        let control_cond = lower_branch_cond(self.lowering, block, instr_ref, branch.cond);
        let (then_target, else_target) = self.branch_target_blocks(block)?;

        let mut cond = if target == then_target {
            control_cond
        } else if target == else_target {
            control_cond.negate()
        } else {
            return None;
        };

        if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
            rewrite_expr_temps(&mut cond, entry_expr_overrides);
        }

        Some(cond)
    }

    fn branch_target_blocks(&self, block: BlockRef) -> Option<(BlockRef, BlockRef)> {
        let (_instr_ref, instr) = self.block_terminator(block)?;
        let LowInstr::Branch(branch) = instr else {
            return None;
        };

        Some((
            self.lowering.cfg.instr_to_block[branch.then_target.index()],
            self.lowering.cfg.instr_to_block[branch.else_target.index()],
        ))
    }

    pub(super) fn block_terminator(&self, block: BlockRef) -> Option<(InstrRef, &LowInstr)> {
        let instr_ref = self.lowering.cfg.blocks[block.index()].instrs.last()?;
        Some((instr_ref, &self.lowering.proto.instrs[instr_ref.index()]))
    }

    pub(super) fn block_prefix_instr_indices(
        &self,
        block: BlockRef,
        expect_branch_terminator: bool,
    ) -> Option<Range<usize>> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return Some(range.start.index()..range.start.index());
        }

        let end = if let Some((_instr_ref, instr)) = self.block_terminator(block) {
            if expect_branch_terminator && !matches!(instr, LowInstr::Branch(_)) {
                return None;
            }

            if is_control_terminator(instr) {
                range.end() - 1
            } else {
                range.end()
            }
        } else {
            range.end()
        };
        Some(range.start.index()..end)
    }

    fn next_linear_successor(
        &self,
        block: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<BlockRef>> {
        match self.lowering.cfg.reachable_successor_shape(block) {
            ReachableSuccessorShape::Empty => Some(None),
            ReachableSuccessorShape::Single(succ) if succ == self.lowering.cfg.exit_block => {
                Some(None)
            }
            ReachableSuccessorShape::Single(succ) if Some(succ) == stop => Some(Some(succ)),
            ReachableSuccessorShape::Single(succ) => Some(Some(succ)),
            ReachableSuccessorShape::Multiple => None,
        }
    }
}

fn unique_branch_value_merges_by_header(
    candidates: &[BranchValueMergeCandidate],
) -> BTreeMap<BlockRef, &BranchValueMergeCandidate> {
    let mut by_header = BTreeMap::new();
    let mut duplicated_headers = BTreeSet::new();

    for candidate in candidates {
        if by_header.insert(candidate.header, candidate).is_some() {
            duplicated_headers.insert(candidate.header);
        }
    }

    for header in duplicated_headers {
        by_header.remove(&header);
    }

    by_header
}

fn supports_structured_goto_requirement(reason: GotoReason) -> bool {
    matches!(reason, GotoReason::UnstructuredContinueLike)
}

fn shared_target_expr_from_overrides(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> Option<HirExpr> {
    shared_expr_for_defs(
        &lowering.bindings.fixed_temps,
        short
            .value_incomings
            .iter()
            .flat_map(|incoming| incoming.defs.iter().copied()),
        target_overrides,
    )
}
