//! 这个文件承载 HIR 结构恢复的主体实现。
//!
//! 外层 `structure.rs` 只负责做入口和模块拼装，这里集中放真正的分支/merge/region
//! 结构恢复逻辑。这样后续继续拆 `branch merge`、`loop exits` 之类的细节时，
//! 不会再把 facade 文件重新撑回一个巨型实现。

mod branches;

use super::rewrites::expr_has_temp_ref_in;
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
        let branch_value_merges_by_header = lowering
            .structure
            .branch_value_merge_candidates
            .iter()
            .map(|candidate| (candidate.header, candidate))
            .collect();
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
        }
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

    fn active_loop_escape_stmts(&mut self, block: BlockRef) -> Option<Vec<HirStmt>> {
        let loop_context = self.active_loops.last()?.clone();
        if loop_context.continue_target == Some(block) && self.loop_continue_target_is_empty(block)
        {
            return self
                .can_emit_continue_stmt()
                .then(|| vec![HirStmt::Continue]);
        }
        if block == loop_context.post_loop || Some(block) == loop_context.downstream_post_loop {
            return Some(vec![HirStmt::Break]);
        }
        if let Some(break_block) = loop_context.break_exits.get(&block) {
            self.visited.extend(break_block.blocks.iter().copied());
            return Some(break_block.block.stmts.clone());
        }
        None
    }

    pub(super) fn lower_escape_edge(
        &mut self,
        from: BlockRef,
        to: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if to == self.lowering.cfg.exit_block || !self.lowering.cfg.reachable_blocks.contains(&to) {
            return None;
        }
        self.required_labels.insert(to);
        let mut stmts = self.escape_state_snapshot_stmts(from, to, target_overrides);
        stmts.extend(goto_block(self.label_map[&to]).stmts);
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

    fn escape_state_snapshot_stmts(
        &self,
        from: BlockRef,
        to: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Vec<HirStmt> {
        let live_in = self.lowering.dataflow.live_in_regs(to);
        let expr_overrides = temp_expr_overrides(target_overrides);
        let mut seen_regs = BTreeSet::new();
        let mut targets = Vec::new();
        let mut values = Vec::new();

        for loop_context in &self.active_loops {
            if loop_context.loop_blocks.contains(&to) {
                continue;
            }

            for state in &loop_context.state_slots {
                if !live_in.contains(&state.reg) || !seen_regs.insert(state.reg) {
                    continue;
                }
                let Some(target) = self.escape_state_target(to, state.reg) else {
                    continue;
                };
                let mut value = expr_for_reg_at_block_exit(self.lowering, from, state.reg);
                rewrite_expr_temps(&mut value, &expr_overrides);
                if lvalue_as_expr(&target)
                    .as_ref()
                    .is_some_and(|target_expr| *target_expr == value)
                {
                    continue;
                }
                targets.push(target);
                values.push(value);
            }
        }

        if targets.is_empty() {
            Vec::new()
        } else {
            vec![assign_stmt(targets, values)]
        }
    }

    fn escape_state_target(&self, to: BlockRef, reg: Reg) -> Option<HirLValue> {
        if let Some(target) = self
            .overrides
            .block_entry_expr(to, reg)
            .and_then(expr_as_lvalue)
        {
            return Some(target);
        }

        self.active_loops
            .iter()
            .filter(|loop_context| !loop_context.loop_blocks.contains(&to))
            .flat_map(|loop_context| loop_context.state_slots.iter())
            .find(|state| state.reg == reg)
            .map(|state| state.target.clone())
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
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return Some(stmts);
        }

        let entry_expr_overrides = self.block_entry_expr_overrides(block);

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

        for instr_index in range.start.index()..end {
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

    pub(super) fn block_entry_expr_overrides(
        &self,
        block: BlockRef,
    ) -> Option<&BTreeMap<TempId, HirExpr>> {
        self.overrides.block_entry_temp_exprs(block)
    }

    pub(super) fn block_redefines_reg(&self, block: BlockRef, reg: Reg) -> bool {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).any(|instr_index| {
            let effect = &self.lowering.dataflow.instr_effects[instr_index];
            effect.fixed_must_defs.contains(&reg) || effect.fixed_may_defs.contains(&reg)
        })
    }

    pub(super) fn install_entry_override(&mut self, block: BlockRef, reg: Reg, expr: HirExpr) {
        // 防止循环传播：如果该 block 上这个 reg 已经有完全相同的 override，不再重入。
        if self
            .overrides
            .carried_entry_expr(block, reg)
            .is_some_and(|existing| *existing == expr)
        {
            return;
        }

        let source_temp = self.block_entry_source_temp(block, reg);
        let carries_through_block = !self.block_redefines_reg(block, reg);
        self.overrides.insert_entry_expr(
            block,
            reg,
            expr.clone(),
            source_temp,
            carries_through_block,
        );
        // 当 override 能穿透当前 block（该 register 未被重定义），需要继续向后继传播。
        // 否则后续 block 的 lower_block_prefix 看不到 entry_temp_expr override，
        // 被 suppress 的 phi temp 在 RHS 表达式中就无法被正确替换。
        // 对于分支 block（多后继），所有后继都可能需要该 override，只要后继处没有
        // 该寄存器的 phi 合流（有 phi 说明多来源，不能用单条路径 override 覆盖）。
        if carries_through_block {
            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                let successor = self.lowering.cfg.edges[edge_ref.index()].to;
                if !self.lowering.cfg.reachable_blocks.contains(&successor) {
                    continue;
                }
                if self
                    .lowering
                    .dataflow
                    .phi_candidate_for_reg(successor, reg)
                    .is_none()
                {
                    self.install_entry_override(successor, reg, expr.clone());
                }
            }
        }
    }

    pub(super) fn replace_phi_with_entry_expr(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        reg: Reg,
        expr: HirExpr,
    ) {
        self.overrides.suppress_phi(phi_id);
        self.install_entry_override(block, reg, expr);
    }

    pub(super) fn replace_phi_with_entry_expr_if_local_use(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        reg: Reg,
        expr: HirExpr,
    ) {
        if self
            .lowering
            .dataflow
            .phi_used_only_in_block(self.lowering.cfg, phi_id, block)
        {
            self.replace_phi_with_entry_expr(block, phi_id, reg, expr);
        } else {
            self.overrides.insert_phi_expr(block, phi_id, expr);
        }
    }

    pub(super) fn replace_phi_with_target_expr(
        &mut self,
        block: BlockRef,
        phi_id: PhiId,
        target: &HirLValue,
        expr: HirExpr,
    ) {
        let phi_temp = self.lowering.bindings.phi_temps[phi_id.index()];
        if lvalue_as_expr(target) == Some(HirExpr::TempRef(phi_temp)) {
            self.overrides.suppress_phi(phi_id);
        } else {
            self.overrides.insert_phi_expr(block, phi_id, expr);
        }
    }

    fn block_entry_source_temp(&self, block: BlockRef, reg: Reg) -> Option<TempId> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return None;
        }
        // 即使当前 block 内会重定义该寄存器（如 `SUB r1, r1, 1000` 先读后写），
        // 入口处的 reaching value 仍然是该寄存器在 block 首条指令前的 SSA 值，
        // 对应的 temp 会出现在 RHS 表达式中。移除旧有的 block_redefines_reg 守卫，
        // 让 entry_temp_exprs 能正确建立映射，使 lower_block_prefix 的 rewrite 生效。

        let values = self
            .lowering
            .dataflow
            .reaching_values_at(range.start)
            .get(reg)?;
        if values.len() != 1 {
            return None;
        }

        Some(
            match values
                .iter()
                .next()
                .expect("len checked above, exactly one reaching value exists")
            {
                crate::cfg::SsaValue::Def(def) => self.lowering.bindings.fixed_temps[def.index()],
                crate::cfg::SsaValue::Phi(phi) => self.lowering.bindings.phi_temps[phi.index()],
            },
        )
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

    pub(in crate::hir::analyze::structure) fn try_build_short_circuit_plan(
        &self,
        header: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<StructuredBranchPlan>> {
        let Some(BranchShortCircuitPlan {
            mut cond,
            mut truthy,
            mut falsy,
            mut consumed_headers,
        }) = build_branch_short_circuit_plan(self.lowering, header)
        else {
            return Some(None);
        };
        if self.block_exits_outer_active_loop(truthy) || self.block_exits_outer_active_loop(falsy) {
            return Some(None);
        }
        if let Some(stop) = stop
            && self.active_loops.last().is_some_and(|loop_context| {
                loop_context.continue_target == Some(stop)
                    && !self.loop_continue_target_is_empty(stop)
            })
        {
            let can_falsy_stop = self.can_short_circuit_falsy_to_non_empty_continue();
            if truthy == stop && can_falsy_stop {
                cond = cond.negate();
                std::mem::swap(&mut truthy, &mut falsy);
            }
            if truthy == stop
                || consumed_headers.contains(&stop)
                || (falsy == stop && !can_falsy_stop)
            {
                return Some(None);
            }
        }

        // 当短路的 truthy 出口是一个退化分支（两条 CFG 边都指向同一个后继 == falsy）时，
        // 该 block 是 `(sc_cond) and guard then end` 中空体守卫的残留。
        // 直接把守卫条件折叠进 SC 条件，避免它作为 body 被 lower_linear_block 丢弃。
        self.absorb_degenerate_guards(&mut cond, &mut truthy, falsy, stop, &mut consumed_headers);
        let fallback_cond = cond.clone();
        let fallback_truthy = truthy;
        let fallback_falsy = falsy;
        let fallback_consumed_headers = consumed_headers.clone();
        self.extend_branch_short_circuit_exits(
            &mut cond,
            &mut truthy,
            &mut falsy,
            stop,
            &mut consumed_headers,
        );
        if !self.rewrite_short_circuit_skipped_header_prefixes(header, &consumed_headers, &mut cond)
        {
            cond = fallback_cond;
            truthy = fallback_truthy;
            falsy = fallback_falsy;
            consumed_headers = fallback_consumed_headers;
            if !self.rewrite_short_circuit_skipped_header_prefixes(
                header,
                &consumed_headers,
                &mut cond,
            ) {
                return Some(None);
            }
        }

        // 单节点 short-circuit 和普通 branch 在结构信息上是重叠的。
        // 这里如果已经有 plain branch candidate，就优先走普通 branch 恢复：
        // short-circuit 那条 `can_reach(truthy, falsy)` 启发式在 loop 图里会把
        // “经过回边才重新绕到另一臂”的路径也算进去，进而把简单的
        // `if cond then break end` / `if cond then ... end` 误折成错误的 then/merge。
        // 多节点 short-circuit 仍然保留，因为那类结构 plain branch 本来就表达不全。
        if consumed_headers.len() == 1 && self.branch_by_header.contains_key(&header) {
            return Some(None);
        }

        // 退化守卫吸收后 truthy 可能等于 falsy（body 完全为空），
        // 直接产出空 body 的 if-then，避免后续 postdom 推导制造出
        // then_entry == else_entry 的畸形 plan。
        if truthy == falsy {
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: None,
                merge: Some(falsy),
                consumed_headers,
                consumed_blocks,
            }));
        }

        // 当 then_entry 恰好等于当前 scope 的 stop 时，多数情况下可以恢复成
        // “一臂为空并回到 stop，另一臂显式 break/continue”的结构。只有候选本身
        // 把 stop block 放进 consumed_headers，才会提前 visit 外层还要消费的 stop。
        if stop == Some(truthy) && falsy != truthy && consumed_headers.contains(&truthy) {
            return Some(None);
        }
        if stop == Some(truthy) && falsy != truthy && self.block_is_active_loop_escape(falsy) {
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: Some(falsy),
                merge: Some(falsy),
                consumed_headers,
                consumed_blocks,
            }));
        }
        let truthy_flows_to_falsy = self.lowering.cfg.can_reach(truthy, falsy)
            && self
                .lowering
                .graph_facts
                .nearest_common_postdom(truthy, falsy)
                == Some(falsy);
        // 在 loop 内，全图 can_reach 可能经由回边从 then body 绕到 else body。
        // 只有 falsy 本身就是两条出口的最近共同后支配点时，才说明这是
        // `if cond then ... end` 的自然 fallthrough，而不是 `if cond then ... else ... end`。
        if stop == Some(falsy) || truthy_flows_to_falsy {
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: None,
                merge: Some(falsy),
                consumed_headers,
                consumed_blocks,
            }));
        }

        // 当 SC 的 falsy 出口本身是 `return`/`tail-call` 终结块，并且 then 入口能
        // 经由内部控制流到达同一个终结块时（典型形状：then 内部还有 `if X then return end`
        // 的早返回守卫，与 SC 失败路径共用函数尾部的隐式 return），按 IfElse 处理会
        // 让 then 在 lower 时先 visit 掉这个共享终结块，导致随后 lower else 失败、整段
        // proto 退化成 goto-label fallback。这里把这种形状显式降级成 IfThen，merge 留空：
        // 终结块由 then 内部的早返回路径自然消费，SC falsy 边落到外层 region 的自然末尾，
        // 语义上正好对齐 `if cond then ... <early return inside> ... end` 加函数末尾隐式 return。
        // 如果这条“可达”必须先经过当前 region 的 stop（如 numeric-for 的 FORLOOP latch），
        // 那就是经由下一轮循环绕回来的可达性，不能据此省略当前分支的 terminal else 臂。
        if self.block_is_terminal_exit(falsy)
            && stop.is_none_or(|stop| self.can_reach_avoiding_block(truthy, falsy, stop))
            && self.lowering.cfg.can_reach(truthy, falsy)
        {
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: None,
                merge: None,
                consumed_headers,
                consumed_blocks,
            }));
        }

        let merge = self
            .lowering
            .graph_facts
            .nearest_common_postdom(truthy, falsy)?;

        let consumed_blocks =
            self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
        Some(Some(StructuredBranchPlan {
            cond,
            then_entry: truthy,
            else_entry: Some(falsy),
            merge: (merge != self.lowering.cfg.exit_block).then_some(merge),
            consumed_headers,
            consumed_blocks,
        }))
    }

    fn branch_short_circuit_consumed_blocks(
        &self,
        consumed_headers: &[BlockRef],
        truthy: BlockRef,
        falsy: BlockRef,
        stop: Option<BlockRef>,
    ) -> Vec<BlockRef> {
        let mut consumed = consumed_headers.iter().copied().collect::<BTreeSet<_>>();
        let exits = BTreeSet::from([truthy, falsy]);
        for header in consumed_headers {
            for edge_ref in &self.lowering.cfg.succs[header.index()] {
                let successor = self.lowering.cfg.edges[edge_ref.index()].to;
                self.collect_transparent_short_circuit_exit_pads(
                    successor,
                    &exits,
                    stop,
                    &mut consumed,
                );
            }
        }
        consumed.into_iter().collect()
    }

    fn collect_transparent_short_circuit_exit_pads(
        &self,
        start: BlockRef,
        exits: &BTreeSet<BlockRef>,
        stop: Option<BlockRef>,
        consumed: &mut BTreeSet<BlockRef>,
    ) -> bool {
        if exits.contains(&start) || Some(start) == stop || consumed.contains(&start) {
            return exits.contains(&start);
        }
        if !self.block_is_transparent_short_circuit_exit_pad(start) {
            return false;
        }
        consumed.insert(start);
        let Some(successor) = self.lowering.cfg.unique_reachable_successor(start) else {
            consumed.remove(&start);
            return false;
        };
        if !exits.contains(&successor)
            && !self.collect_transparent_short_circuit_exit_pads(successor, exits, stop, consumed)
        {
            consumed.remove(&start);
            return false;
        }
        true
    }

    fn block_is_transparent_short_circuit_exit_pad(&self, block: BlockRef) -> bool {
        if block == self.lowering.cfg.exit_block
            || self.branch_by_header.contains_key(&block)
            || self.loop_by_header.contains_key(&block)
            || !self
                .lowering
                .dataflow
                .phi_candidates_in_block(block)
                .is_empty()
        {
            return false;
        }

        let range = self.lowering.cfg.blocks[block.index()].instrs;
        match range.len {
            0 => true,
            1 => matches!(
                self.lowering.proto.instrs.get(range.start.index()),
                Some(LowInstr::Jump(_))
            ),
            _ => false,
        }
    }

    fn extend_branch_short_circuit_exits(
        &self,
        cond: &mut HirExpr,
        truthy: &mut BlockRef,
        falsy: &mut BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &mut Vec<BlockRef>,
    ) {
        loop {
            if self.extend_truthy_branch_short_circuit_exit(
                cond,
                truthy,
                falsy,
                stop,
                consumed_headers,
            ) || self.extend_falsy_branch_short_circuit_exit(
                cond,
                truthy,
                falsy,
                stop,
                consumed_headers,
            ) {
                continue;
            }
            break;
        }
    }

    fn extend_truthy_branch_short_circuit_exit(
        &self,
        cond: &mut HirExpr,
        truthy: &mut BlockRef,
        falsy: &mut BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &mut Vec<BlockRef>,
    ) -> bool {
        let Some(next) = self.nestable_branch_short_circuit_plan(*truthy, stop, consumed_headers)
        else {
            return false;
        };
        if next.truthy == *falsy {
            let old_cond = std::mem::replace(cond, HirExpr::Boolean(false));
            *cond = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: old_cond.negate(),
                rhs: next.cond,
            }));
            *truthy = *falsy;
            *falsy = next.falsy;
        } else if next.falsy == *falsy {
            let old_cond = std::mem::replace(cond, HirExpr::Boolean(false));
            *cond = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: old_cond,
                rhs: next.cond,
            }));
            *truthy = next.truthy;
        } else {
            return false;
        }
        consumed_headers.extend(next.consumed_headers);
        true
    }

    fn extend_falsy_branch_short_circuit_exit(
        &self,
        cond: &mut HirExpr,
        truthy: &mut BlockRef,
        falsy: &mut BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &mut Vec<BlockRef>,
    ) -> bool {
        let Some(next) = self.nestable_branch_short_circuit_plan(*falsy, stop, consumed_headers)
        else {
            return false;
        };
        if next.truthy == *truthy {
            let old_cond = std::mem::replace(cond, HirExpr::Boolean(false));
            *cond = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: old_cond,
                rhs: next.cond,
            }));
            *falsy = next.falsy;
        } else if next.falsy == *truthy {
            let old_cond = std::mem::replace(cond, HirExpr::Boolean(false));
            *cond = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: old_cond.negate(),
                rhs: next.cond,
            }));
            *truthy = next.truthy;
            *falsy = next.falsy;
        } else {
            return false;
        }
        consumed_headers.extend(next.consumed_headers);
        true
    }

    fn nestable_branch_short_circuit_plan(
        &self,
        header: BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &[BlockRef],
    ) -> Option<BranchShortCircuitPlan> {
        if Some(header) == stop || consumed_headers.contains(&header) {
            return None;
        }
        if self.loop_by_header.contains_key(&header) {
            return None;
        }
        let next = build_branch_short_circuit_plan(self.lowering, header)
            .or_else(|| self.nestable_plain_branch_plan(header))?;
        if next
            .consumed_headers
            .iter()
            .any(|header| Some(*header) == stop || consumed_headers.contains(header))
        {
            return None;
        }
        Some(next)
    }

    // 普通 branch 只有在作为短路链的下一个出口时才被临时当作两出口计划。
    // 真正消费前还会由 rewrite_short_circuit_skipped_header_prefixes 校验其 prefix
    // 能否安全内联进条件，避免把带副作用或不可表达的前置语句静默吞掉。
    fn nestable_plain_branch_plan(&self, header: BlockRef) -> Option<BranchShortCircuitPlan> {
        let candidate = self.branch_by_header.get(&header).copied()?;
        let falsy = match candidate.kind {
            BranchKind::IfElse => candidate.else_entry?,
            BranchKind::IfThen | BranchKind::Guard => candidate.merge?,
        };

        Some(BranchShortCircuitPlan {
            cond: self.lower_candidate_cond(header, candidate)?,
            truthy: candidate.then_entry,
            falsy,
            consumed_headers: vec![header],
        })
    }

    fn rewrite_short_circuit_skipped_header_prefixes(
        &self,
        header: BlockRef,
        consumed_headers: &[BlockRef],
        cond: &mut HirExpr,
    ) -> bool {
        let target_overrides = BTreeMap::new();
        consumed_headers
            .iter()
            .copied()
            .filter(|consumed| *consumed != header)
            .all(|consumed| {
                let Some(prefix) = self.lower_block_prefix(consumed, true, &target_overrides)
                else {
                    return false;
                };
                if prefix.is_empty() {
                    return true;
                }

                let (expr_overrides, all_prefix_temps) =
                    self.block_prefix_temp_expr_overrides(consumed);
                rewrite_expr_temps(cond, &expr_overrides);

                let mut prefix_temps = BTreeSet::new();
                for stmt in prefix {
                    let HirStmt::Assign(assign) = stmt else {
                        return false;
                    };
                    if assign.targets.len() != assign.values.len() {
                        return false;
                    }
                    for target in assign.targets {
                        let HirLValue::Temp(temp) = target else {
                            return false;
                        };
                        prefix_temps.insert(temp);
                    }
                }
                let mut unresolved_prefix_temps = prefix_temps;
                unresolved_prefix_temps.extend(all_prefix_temps);
                for temp in expr_overrides.keys() {
                    unresolved_prefix_temps.remove(temp);
                }
                !expr_has_temp_ref_in(cond, &unresolved_prefix_temps)
            })
    }

    fn can_short_circuit_falsy_to_non_empty_continue(&self) -> bool {
        let Some(loop_context) = self.active_loops.last() else {
            return false;
        };
        self.loop_by_header
            .get(&loop_context.header)
            .is_some_and(|candidate| {
                matches!(
                    candidate.kind_hint,
                    LoopKindHint::NumericForLike
                        | LoopKindHint::GenericForLike
                        | LoopKindHint::Unknown
                )
            })
    }

    /// 当短路候选的 truthy 出口指向一个退化分支 block（两条 CFG 边都流向同一目标），
    /// 且该目标恰好等于 falsy 出口时，把那个退化 block 的条件吸收成 `cond and guard`。
    ///
    /// 典型场景：`if (A or B) and C then end`，编译器为空体保留了 TEST 退化 block，
    /// 其 truthy/falsy 都流向 merge。如果不做吸收，该退化 block 会作为 body 被
    /// `lower_linear_block` 直接跳过，丢失 `and C` 部分。
    fn absorb_degenerate_guards(
        &self,
        cond: &mut HirExpr,
        truthy: &mut BlockRef,
        falsy: BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &mut Vec<BlockRef>,
    ) {
        loop {
            // 如果当前 truthy 恰好是外层 region 的 stop（即上层分支的 merge），
            // 吸收它会连带把 visit 标记提前打上，等外层 merge 回来时发现 block 已被
            // 访问过而导致结构化整体失败。此时放弃吸收，让外层自然处理。
            if Some(*truthy) == stop {
                break;
            }
            let Some(degenerate_target) = self.degenerate_branch_target(*truthy) else {
                break;
            };
            if degenerate_target != falsy {
                break;
            }
            let Some(guard_subject) = lower_short_circuit_subject(self.lowering, *truthy) else {
                break;
            };
            let old_cond = std::mem::replace(cond, HirExpr::Boolean(false));
            *cond = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: old_cond,
                rhs: guard_subject,
            }));
            consumed_headers.push(*truthy);
            *truthy = degenerate_target;
        }
    }

    /// 返回退化分支 block 的唯一后继（两条 CFG 边都指向同一 block），
    /// 非退化分支或非分支 block 返回 None。
    fn degenerate_branch_target(&self, block: BlockRef) -> Option<BlockRef> {
        let (then_edge, else_edge) = self.lowering.cfg.branch_edges(block)?;
        let then_target = self.lowering.cfg.edges[then_edge.index()].to;
        let else_target = self.lowering.cfg.edges[else_edge.index()].to;
        if then_target == else_target {
            Some(then_target)
        } else {
            None
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

    fn next_linear_successor(
        &self,
        block: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<BlockRef>> {
        let mut successors = self.lowering.cfg.succs[block.index()]
            .iter()
            .map(|edge_ref| self.lowering.cfg.edges[edge_ref.index()].to)
            .filter(|succ| self.lowering.cfg.reachable_blocks.contains(succ))
            .collect::<Vec<_>>();
        successors.sort();
        successors.dedup();

        match successors.as_slice() {
            [] => Some(None),
            [succ] if *succ == self.lowering.cfg.exit_block => Some(None),
            [succ] if Some(*succ) == stop => Some(Some(*succ)),
            [succ] => Some(Some(*succ)),
            _ => None,
        }
    }

    fn branch_stop_for_region(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        merge: Option<BlockRef>,
        stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        if stop.is_none() {
            return merge.or_else(|| {
                self.branch_shared_continuation_stop(block, then_entry, else_entry, merge, None)
            });
        }
        let Some(stop) = stop else {
            return merge;
        };
        // if-then 没有显式 else 时，缺席的 else 路径本身就是落到 merge。
        // 即使 merge 是 terminal exit，也必须把它留作分支之后的共享 continuation；
        // 否则 then 臂会先消费 terminal merge，随后缺席 else 再次进入同一块而重入失败。
        if let Some(merge) = merge
            && merge != stop
            && else_entry.is_some()
            && self.block_is_terminal_exit(merge)
        {
            return if self.terminal_exit_block_is_clone_safe(merge) {
                Some(stop)
            } else {
                Some(merge)
            };
        }
        // if-then 的 terminal merge 既可能是共享尾部（`if cond then body end; return`），
        // 也可能是缺席 else 臂的早返回（`if not cond then return end; continue`）。
        // 当 then 臂能绕开这个 terminal merge 到达外层 stop 时，merge 只能归入隐式
        // else；否则把 then 臂截到 merge 会截断后续 loop body。
        if let Some(merge) = merge
            && merge != stop
            && else_entry.is_none()
            && self.block_is_terminal_exit(merge)
            && self.can_reach_avoiding_block(then_entry, stop, merge)
        {
            return Some(stop);
        }
        if then_entry == stop || else_entry == Some(stop) {
            return Some(stop);
        }
        if let Some(loop_continuation) =
            self.loop_body_shared_continuation_stop(block, then_entry, else_entry, stop)
        {
            return Some(loop_continuation);
        }
        if let Some(shared_continuation) =
            self.branch_shared_continuation_stop(block, then_entry, else_entry, merge, Some(stop))
        {
            return Some(shared_continuation);
        }
        let same_merge_stop = merge == Some(stop);
        let can_truncate_to_loop_escape = merge.is_some_and(|merge| {
            merge != stop
                && self
                    .branch_can_truncate_to_stop_or_loop_escape(then_entry, else_entry, stop, merge)
        });
        let can_truncate_to_stop =
            self.branch_can_truncate_to_stop(block, then_entry, else_entry, stop);
        if same_merge_stop || can_truncate_to_loop_escape || can_truncate_to_stop {
            return Some(stop);
        }

        merge.or(Some(stop))
    }

    fn branch_shared_continuation_stop(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        merge: Option<BlockRef>,
        region_stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let else_entry = else_entry?;
        if let Some(merge) = merge {
            return self
                .branch_shared_continuation_candidate_is_valid(
                    block,
                    then_entry,
                    else_entry,
                    merge,
                    region_stop,
                )
                .then_some(merge);
        }

        self.lowering
            .cfg
            .block_order
            .iter()
            .copied()
            .find(|candidate| {
                self.lowering.cfg.can_reach(then_entry, *candidate)
                    && self.lowering.cfg.can_reach(else_entry, *candidate)
                    && self.branch_shared_continuation_candidate_is_valid(
                        block,
                        then_entry,
                        else_entry,
                        *candidate,
                        region_stop,
                    )
            })
    }

    fn branch_shared_continuation_candidate_is_valid(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: BlockRef,
        candidate: BlockRef,
        region_stop: Option<BlockRef>,
    ) -> bool {
        if candidate == block
            || candidate == then_entry
            || Some(candidate) == region_stop
            || candidate == self.lowering.cfg.exit_block
            || self.block_is_terminal_exit(candidate)
            || self.block_is_active_loop_escape(candidate)
        {
            return false;
        }
        if let Some(region_stop) = region_stop
            && (self.lowering.cfg.can_reach(region_stop, candidate)
                || !self.lowering.cfg.can_reach(candidate, region_stop))
        {
            return false;
        }

        let boundary = region_stop.unwrap_or(self.lowering.cfg.exit_block);
        self.branch_arm_reaches_shared_continuation_or_terminate(then_entry, candidate, boundary)
            && self.branch_arm_reaches_shared_continuation_or_terminate(
                else_entry, candidate, boundary,
            )
    }

    fn branch_arm_reaches_shared_continuation_or_terminate(
        &self,
        entry: BlockRef,
        continuation: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            continuation: BlockRef,
            boundary: BlockRef,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == continuation {
                return true;
            }
            if block == boundary || !lowerer.lowering.cfg.reachable_blocks.contains(&block) {
                return false;
            }
            if block == lowerer.lowering.cfg.exit_block || lowerer.block_is_terminal_exit(block) {
                return true;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return true;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(lowerer, successor, continuation, boundary, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            continuation,
            boundary,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    fn loop_body_shared_continuation_stop(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
    ) -> Option<BlockRef> {
        // while 体内的 if/elseif 链经常有两类出口：一类是 break，另一类先汇合到
        // “本轮收尾”块（例如 i = i + 1）再回到 header。StructureFacts 的分支 merge
        // 会被 break 出口拉到 loop 外，此时若直接把分支臂降到 header，两条臂会重复
        // 消费同一个收尾块。这里只在所有非 escape 路径都能到达同一个回 header 块时，
        // 把该块作为当前分支的局部 stop，让它由外层 loop body 统一消费一次。
        let loop_context = self.active_loops.last()?;
        if loop_context.header != stop {
            return None;
        }
        let region = self.branch_regions_by_header.get(&block)?;
        let continuation = region
            .structured_blocks
            .iter()
            .copied()
            .filter(|candidate| *candidate != block)
            .filter(|candidate| *candidate != then_entry && Some(*candidate) != else_entry)
            .filter(|candidate| {
                self.lowering.cfg.unique_reachable_successor(*candidate) == Some(stop)
            })
            .find(|candidate| {
                self.branch_arm_reaches_loop_continuation_or_escape(then_entry, *candidate, stop)
                    && else_entry.is_none_or(|else_entry| {
                        self.branch_arm_reaches_loop_continuation_or_escape(
                            else_entry, *candidate, stop,
                        )
                    })
            })?;

        Some(continuation)
    }

    fn branch_arm_reaches_loop_continuation_or_escape(
        &self,
        entry: BlockRef,
        continuation: BlockRef,
        stop: BlockRef,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            continuation: BlockRef,
            stop: BlockRef,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == continuation {
                return true;
            }
            if block == stop || block == lowerer.lowering.cfg.exit_block {
                return false;
            }
            if lowerer.block_is_active_loop_escape(block) {
                return true;
            }
            if !lowerer.lowering.cfg.reachable_blocks.contains(&block) {
                return false;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return true;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(lowerer, successor, continuation, stop, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            continuation,
            stop,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    fn branch_can_truncate_to_stop_or_loop_escape(
        &self,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        self.branch_arm_reaches_stop_or_loop_escape(then_entry, stop, boundary)
            && else_entry.is_none_or(|else_entry| {
                self.branch_arm_reaches_stop_or_loop_escape(else_entry, stop, boundary)
            })
    }

    fn branch_arm_reaches_stop_or_loop_escape(
        &self,
        entry: BlockRef,
        stop: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            stop: BlockRef,
            boundary: BlockRef,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == stop {
                return true;
            }
            if block == boundary {
                return lowerer.block_is_active_loop_escape(block);
            }
            if block == lowerer.lowering.cfg.exit_block || lowerer.block_is_terminal_exit(block) {
                return true;
            }
            if !lowerer.lowering.cfg.reachable_blocks.contains(&block) {
                return false;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return true;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(lowerer, successor, stop, boundary, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            stop,
            boundary,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    fn block_is_active_loop_escape(&self, block: BlockRef) -> bool {
        self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target == Some(block)
                || loop_context.post_loop == block
                || loop_context.downstream_post_loop == Some(block)
                || loop_context.break_exits.contains_key(&block)
        })
    }

    fn block_exits_outer_active_loop(&self, block: BlockRef) -> bool {
        self.active_loops.iter().rev().skip(1).any(|loop_context| {
            loop_context.post_loop == block
                || loop_context.downstream_post_loop == Some(block)
                || loop_context.break_exits.contains_key(&block)
        })
    }

    fn loop_continue_target_is_empty(&self, block: BlockRef) -> bool {
        if self.branch_by_header.contains_key(&block) {
            return false;
        }
        let terminator = self.block_terminator(block).map(|(instr_ref, _)| instr_ref);
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).all(|instr_idx| {
            let instr_ref = InstrRef(instr_idx);
            Some(instr_ref) == terminator
                || self
                    .lowering
                    .proto
                    .instrs
                    .get(instr_idx)
                    .is_some_and(is_control_terminator)
        })
    }

    pub(super) fn terminal_exit_block_is_clone_safe(&self, block: BlockRef) -> bool {
        if !self.block_is_terminal_exit(block) {
            return false;
        }
        let terminator = self.block_terminator(block).map(|(instr_ref, _)| instr_ref);
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        (range.start.index()..range.end()).all(|instr_idx| {
            let instr_ref = InstrRef(instr_idx);
            // Closure capture 记录的是父级词法槽位身份；复制同一条 raw CLOSURE 会把
            // 一个 child proto 伪造成多个创建点，后续 naming 无法得到单一 provenance。
            Some(instr_ref) == terminator
                || !matches!(
                    self.lowering.proto.instrs.get(instr_idx),
                    Some(LowInstr::Closure(_))
                )
        })
    }

    pub(super) fn branch_arm_stop(
        &self,
        entry: BlockRef,
        sibling_entry: Option<BlockRef>,
        merge: Option<BlockRef>,
        branch_stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let Some(branch_stop) = branch_stop else {
            return merge;
        };
        let Some(merge) = merge else {
            return Some(branch_stop);
        };

        // 当一条臂本身就是外层 stop 时，另一条臂如果继续使用外层 stop 作为边界，
        // 可能会沿 CFG 一直降到自己的 merge 之后，提前 visit 掉外层 stop 也需要消费的
        // 共享尾部块。普通 merge 下非 stop 臂只降到自己的 merge；但 merge 若是当前
        // loop 的 break/continue 出口，仍要保留外层 stop，让 follow_linear_target 有机会
        // 把跳向 merge 的边恢复成显式 break/continue。
        if merge != branch_stop
            && sibling_entry == Some(branch_stop)
            && entry != branch_stop
            && entry != merge
        {
            if self.block_is_active_loop_escape(merge) {
                Some(branch_stop)
            } else if self
                .loop_by_header
                .get(&merge)
                .is_some_and(|loop_candidate| loop_candidate.preheader == Some(entry))
            {
                // 分支的一臂直接回到外层 loop continue，另一臂入口可能正好是嵌套
                // for-loop 的 preheader；此时 postdom 给出的 merge 是内层 loop header，
                // 但它语义上属于这一条 arm，而不是两臂共享 tail。若把 arm 截到
                // header 前，generic-for preheader lowering 就没有机会运行，整段会退回
                // label/goto。
                Some(branch_stop)
            } else {
                Some(merge)
            }
        } else {
            Some(branch_stop)
        }
    }

    fn branch_can_truncate_to_stop(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
    ) -> bool {
        let Some(region) = self.branch_regions_by_header.get(&block).copied() else {
            return false;
        };
        if !region.structured_blocks.contains(&stop) {
            return false;
        }

        let mut allowed_blocks = region.structured_blocks.clone();
        allowed_blocks.insert(stop);
        let arm_can_truncate_to_stop =
            |entry| self.branch_arm_can_truncate_to_stop(entry, stop, &allowed_blocks);

        // `if-then` / guard 没有显式 else 臂时，缺席的那一臂本来就代表“当前 region 不再
        // 产生额外语句，直接把控制权交回外层 stop”。这里如果仍然要求 else_entry 存在，
        // 嵌套 guard 会被错误地强推到自己的 merge 上，跨出外层 region，最后在更深的
        // merge block 上重入并把整片结构化打回失败。
        arm_can_truncate_to_stop(then_entry) && else_entry.is_none_or(arm_can_truncate_to_stop)
    }

    fn branch_arm_can_truncate_to_stop(
        &self,
        entry: BlockRef,
        stop: BlockRef,
        allowed_blocks: &BTreeSet<BlockRef>,
    ) -> bool {
        if entry == stop {
            return true;
        }

        if self.branch_arm_crosses_live_continuation(entry, stop) {
            return false;
        }

        self.lowering
            .cfg
            .can_reach_within(entry, stop, allowed_blocks)
            || self.branch_arm_terminates_before_stop(entry, stop)
    }

    fn branch_arm_crosses_live_continuation(&self, entry: BlockRef, stop: BlockRef) -> bool {
        let mut visited = BTreeSet::new();
        let mut stack = vec![entry];

        while let Some(block) = stack.pop() {
            if block == stop
                || block == self.lowering.cfg.exit_block
                || !self.lowering.cfg.reachable_blocks.contains(&block)
                || !visited.insert(block)
            {
                continue;
            }

            // 如果某条内层分支绕过外层 stop 直接进入 stop 之后的普通延续块，
            // 把它截断到外层 stop 会把后续语句吸进当前分支臂，破坏外层 region。
            // 但 Lua 5.1 的 guard/elseif 链常会让“处理完的路径”直接跳到函数尾
            // return；这种终止块没有可继续结构化的 fallthrough，可以安全地留在臂内。
            if self.lowering.cfg.can_reach(stop, block) && !self.block_is_terminal_exit(block) {
                return true;
            }

            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                stack.push(self.lowering.cfg.edges[edge_ref.index()].to);
            }
        }

        false
    }

    fn branch_arm_terminates_before_stop(&self, entry: BlockRef, stop: BlockRef) -> bool {
        let mut visited = BTreeSet::new();
        let mut stack = vec![entry];
        let mut saw_terminal = false;

        while let Some(block) = stack.pop() {
            if block == stop || block == self.lowering.cfg.exit_block {
                return true;
            }
            if !self.lowering.cfg.reachable_blocks.contains(&block) || !visited.insert(block) {
                continue;
            }
            if self.block_is_terminal_exit(block) {
                saw_terminal = true;
                continue;
            }

            for edge_ref in &self.lowering.cfg.succs[block.index()] {
                let successor = self.lowering.cfg.edges[edge_ref.index()].to;
                if successor != stop {
                    stack.push(successor);
                }
            }
        }

        saw_terminal
    }

    fn block_is_terminal_exit(&self, block: BlockRef) -> bool {
        let succs = &self.lowering.cfg.succs[block.index()];
        !succs.is_empty()
            && succs.iter().all(|edge_ref| {
                let edge = self.lowering.cfg.edges[edge_ref.index()];
                edge.to == self.lowering.cfg.exit_block
                    && matches!(
                        edge.kind,
                        crate::cfg::EdgeKind::Return | crate::cfg::EdgeKind::TailCall
                    )
            })
    }
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
