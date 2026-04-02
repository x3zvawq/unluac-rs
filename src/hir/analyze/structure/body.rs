//! 这个文件承载 HIR 结构恢复的主体实现。
//!
//! 外层 `structure.rs` 只负责做入口和模块拼装，这里集中放真正的分支/merge/region
//! 结构恢复逻辑。这样后续继续拆 `branch merge`、`loop exits` 之类的细节时，
//! 不会再把 facade 文件重新撑回一个巨型实现。

mod branches;

use super::*;

/// 尝试基于现有结构候选恢复一个更接近源码的 HIR block。
pub(super) fn build_structured_body(lowering: &ProtoLowering<'_>) -> Option<HirBlock> {
    if lowering
        .structure
        .goto_requirements
        .iter()
        .any(|requirement| !supports_structured_goto_requirement(requirement.reason))
    {
        return None;
    }

    let mut lowerer = StructuredBodyLowerer::new(lowering);
    let body = lowerer.lower_region(lowering.cfg.entry_block, None, &BTreeMap::new())?;
    if lowerer.all_reachable_blocks_covered() {
        Some(body)
    } else {
        None
    }
}

pub(super) struct StructuredBodyLowerer<'a, 'b> {
    pub(super) lowering: &'b ProtoLowering<'a>,
    pub(super) branch_by_header: BTreeMap<BlockRef, &'b BranchCandidate>,
    pub(super) branch_regions_by_header: BTreeMap<BlockRef, &'b BranchRegionFact>,
    pub(super) branch_value_merges_by_header: BTreeMap<BlockRef, &'b BranchValueMergeCandidate>,
    pub(super) loop_by_header: BTreeMap<BlockRef, &'b LoopCandidate>,
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
}

#[derive(Debug, Clone)]
pub(super) struct LoopStateSlot {
    pub(super) phi_id: PhiId,
    pub(super) reg: Reg,
    pub(super) temp: TempId,
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
    pub(super) post_loop: BlockRef,
    pub(super) downstream_post_loop: Option<BlockRef>,
    pub(super) continue_target: Option<BlockRef>,
    pub(super) continue_sources: BTreeSet<BlockRef>,
    pub(super) break_exits: BTreeMap<BlockRef, HirBlock>,
}

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    fn new(lowering: &'b ProtoLowering<'a>) -> Self {
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
            lowering,
            branch_by_header,
            branch_regions_by_header,
            branch_value_merges_by_header,
            loop_by_header,
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
            if !self.lowering.cfg.reachable_blocks.contains(&block) || self.visited.contains(&block)
            {
                return None;
            }

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

    fn lower_linear_block(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if let Some(next) = self.try_lower_numeric_for_init(block, stop, stmts, target_overrides) {
            return Some(next);
        }

        if let Some(next) =
            self.try_lower_generic_for_preheader(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }

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
                if let Some(loop_context) = self.active_loops.last() {
                    if loop_context.continue_target == Some(target)
                        && loop_context.continue_sources.contains(&block)
                    {
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
                        stmts.extend(break_block.stmts.clone());
                        self.visited.insert(target);
                        return Some(None);
                    }
                }
                if Some(target) == stop || target == self.lowering.cfg.exit_block {
                    Some(if target == self.lowering.cfg.exit_block {
                        None
                    } else {
                        Some(target)
                    })
                } else if self.lowering.cfg.reachable_blocks.contains(&target) {
                    Some(Some(target))
                } else {
                    None
                }
            }
            LowInstr::Return(_) | LowInstr::TailCall(_) => {
                let empty_labels = BTreeMap::new();
                let mut lowered =
                    lower_control_instr(self.lowering, block, instr_ref, instr, &empty_labels);
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

    fn block_entry_expr_overrides(&self, block: BlockRef) -> Option<&BTreeMap<TempId, HirExpr>> {
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
        let source_temp = self.block_entry_source_temp(block, reg);
        let carries_through_block = !self.block_redefines_reg(block, reg);
        self.overrides
            .insert_entry_expr(block, reg, expr, source_temp, carries_through_block);
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
        target_temp: TempId,
        expr: HirExpr,
    ) {
        if target_temp == self.lowering.bindings.phi_temps[phi_id.index()] {
            self.overrides.suppress_phi(phi_id);
        } else {
            self.overrides.insert_phi_expr(block, phi_id, expr);
        }
    }

    fn block_entry_source_temp(&self, block: BlockRef, reg: Reg) -> Option<TempId> {
        let range = self.lowering.cfg.blocks[block.index()].instrs;
        if range.is_empty() || self.block_redefines_reg(block, reg) {
            return None;
        }

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

    fn build_plain_branch_plan(&self, block: BlockRef) -> Option<StructuredBranchPlan> {
        let candidate = *self.branch_by_header.get(&block)?;

        match candidate.kind {
            BranchKind::IfElse => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: candidate.else_entry,
                merge: candidate.merge,
                consumed_headers: vec![block],
            }),
            BranchKind::IfThen | BranchKind::Guard => Some(StructuredBranchPlan {
                cond: self.lower_candidate_cond(block, candidate)?,
                then_entry: candidate.then_entry,
                else_entry: None,
                merge: candidate.merge,
                consumed_headers: vec![block],
            }),
        }
    }

    fn try_build_short_circuit_plan(
        &self,
        header: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<StructuredBranchPlan>> {
        let Some(BranchShortCircuitPlan {
            cond,
            truthy,
            falsy,
            consumed_headers,
        }) = build_branch_short_circuit_plan(self.lowering, header)
        else {
            return Some(None);
        };

        // 单节点 short-circuit 和普通 branch 在结构信息上是重叠的。
        // 这里如果已经有 plain branch candidate，就优先走普通 branch 恢复：
        // short-circuit 那条 `can_reach(truthy, falsy)` 启发式在 loop 图里会把
        // “经过回边才重新绕到另一臂”的路径也算进去，进而把简单的
        // `if cond then break end` / `if cond then ... end` 误折成错误的 then/merge。
        // 多节点 short-circuit 仍然保留，因为那类结构 plain branch 本来就表达不全。
        if consumed_headers.len() == 1 && self.branch_by_header.contains_key(&header) {
            return Some(None);
        }

        if stop == Some(falsy) || self.lowering.cfg.can_reach(truthy, falsy) {
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: None,
                merge: Some(falsy),
                consumed_headers,
            }));
        }

        let merge = self
            .lowering
            .graph_facts
            .nearest_common_postdom(truthy, falsy)?;

        Some(Some(StructuredBranchPlan {
            cond,
            then_entry: truthy,
            else_entry: Some(falsy),
            merge: (merge != self.lowering.cfg.exit_block).then_some(merge),
            consumed_headers,
        }))
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
            negate_expr(control_cond)
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
        let Some(stop) = stop else {
            return merge;
        };
        if merge == Some(stop)
            || self.branch_can_truncate_to_stop(block, then_entry, else_entry, stop)
        {
            return Some(stop);
        }

        merge.or(Some(stop))
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
        let arm_reaches_stop = |entry| {
            entry == stop
                || self
                    .lowering
                    .cfg
                    .can_reach_within(entry, stop, &allowed_blocks)
        };

        arm_reaches_stop(then_entry) && else_entry.is_some_and(arm_reaches_stop)
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

fn negate_expr(expr: HirExpr) -> HirExpr {
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => unary.expr,
        expr => HirExpr::Unary(Box::new(HirUnaryExpr {
            op: HirUnaryOpKind::Not,
            expr,
        })),
    }
}
