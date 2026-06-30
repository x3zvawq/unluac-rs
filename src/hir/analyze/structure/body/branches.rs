//! 这个文件承载 structured body lowering 里的分支恢复细节。
//!
//! `body/mod.rs` 里既有 region 主循环，也有各种 branch/value-merge/loop-control 的细分
//! 恢复逻辑。把后者单独拆出来，是为了让“主流程如何行走 block”与“某个分支具体怎么
//! 降”分开维护；后面继续打磨 shared continuation、break/continue 或 terminal guard
//! 语义时，不需要在一个超大文件里来回跳转。
//!
//! 例子：`BranchCandidate { header, then, else, merge }` →
//! `HirStmt::If { cond, then_block, else_block }`。

use super::*;

#[derive(Debug, Clone, Copy)]
struct SharedContinuationBranch {
    gated_entry: BlockRef,
    shared_entry: BlockRef,
    negate_cond: bool,
}

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn lower_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_single_pass_repeat_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        // 下面几个快捷路径都会在成功时直接消费一段 region；其中有些路径需要先
        // 试降子 region 才知道自己是否成立。失败后必须把 visited/override 等状态
        // 回滚，让后续普通 branch lowering 面对的是同一个输入图，而不是半消费状态。
        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_conditional_reassign_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_statement_value_merge_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) = self.try_lower_value_merge_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_branch_exit_value_assignment(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_loop_continue_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) = self.try_lower_loop_break_branch(block, stop, stmts, target_overrides) {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_loop_terminal_else_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(escape_target) = self.cross_structure_escape_target(block)
            && let Some(next) = self.lower_cross_structure_escape_branch(
                block,
                escape_target,
                stop,
                stmts,
                target_overrides,
            )
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) =
            self.try_lower_terminal_else_guard_branch(block, stop, stmts, target_overrides)
        {
            return Some(next);
        }
        self.restore_state_checkpoint(checkpoint, stmts);

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);

        let short_plan = self.try_build_short_circuit_plan(block, stop)?;
        let plan = short_plan.or_else(|| self.build_plain_branch_plan(block))?;

        if let Some(shared) = self.shared_continuation_branch(&plan, stop) {
            let checkpoint = self.checkpoint_state(stmts.len());
            if let Some(next) =
                self.lower_shared_continuation_branch(shared, &plan, stmts, target_overrides)
            {
                return Some(next);
            }
            self.restore_state_checkpoint(checkpoint, stmts);
        }

        if let Some(shared) = self.terminal_loop_continuation_branch(&plan, stop) {
            let checkpoint = self.checkpoint_state(stmts.len());
            if let Some(next) =
                self.lower_shared_continuation_branch(shared, &plan, stmts, target_overrides)
            {
                return Some(next);
            }
            self.restore_state_checkpoint(checkpoint, stmts);
        }

        for block in &plan.consumed_blocks {
            self.visited.insert(*block);
        }
        let mut branch_stop =
            self.branch_stop_for_region(block, plan.then_entry, plan.else_entry, plan.merge, stop);
        if let Some(downstream) = self.if_then_downstream_merge_stop(&plan, branch_stop, stop) {
            branch_stop = Some(downstream);
        }
        let branch_value_headers = plan
            .consumed_headers
            .iter()
            .copied()
            .filter(|header| self.branch_value_merges_by_header.contains_key(header))
            .collect::<Vec<_>>();
        let branch_target_overrides = (!branch_value_headers.is_empty()).then(|| {
            let mut overrides = target_overrides.clone();
            for header in &branch_value_headers {
                overrides = self.branch_value_target_overrides(*header, &overrides);
            }
            overrides
        });
        if let Some(branch_target_overrides) = branch_target_overrides.as_ref() {
            for header in &branch_value_headers {
                stmts.extend(
                    self.branch_value_preserved_entry_stmts(*header, branch_target_overrides),
                );
            }
        }
        let then_target_overrides = branch_target_overrides
            .as_ref()
            .map(|branch_target_overrides| {
                self.branch_value_then_target_overrides(block, branch_target_overrides)
            })
            .unwrap_or_else(|| target_overrides.clone());
        let else_target_overrides = branch_target_overrides
            .as_ref()
            .map(|branch_target_overrides| {
                self.branch_value_else_target_overrides(block, branch_target_overrides)
            })
            .unwrap_or_else(|| target_overrides.clone());
        let effective_else_entry = plan
            .else_entry
            .or_else(|| self.implicit_else_merge_entry(&plan, branch_stop));
        let then_stop = if plan.else_entry.is_none()
            && effective_else_entry == plan.merge
            && branch_stop != plan.merge
            && Some(plan.then_entry) != branch_stop
            && plan.merge.is_some_and(|merge| {
                !self.block_is_terminal_exit(merge)
                    && !branch_stop.is_some_and(|stop| {
                        self.can_reach_avoiding_block(plan.then_entry, stop, merge)
                    })
            }) {
            plan.merge
        } else {
            self.branch_arm_stop(
                plan.then_entry,
                effective_else_entry,
                plan.merge,
                branch_stop,
            )
        };
        let else_stop = effective_else_entry.and_then(|else_entry| {
            self.branch_arm_stop(else_entry, Some(plan.then_entry), plan.merge, branch_stop)
        });
        let then_block = self.lower_region(plan.then_entry, then_stop, &then_target_overrides)?;
        let else_block = match effective_else_entry {
            Some(else_entry) => {
                Some(self.lower_region(else_entry, else_stop, &else_target_overrides)?)
            }
            // IfThen 无 else 臂时，不再为 merge block 上的 phi 生成隐式 else 赋值。
            // 这些 phi 会在 merge block 的 lower_block_prefix 中由 idom 兜底统一
            // 物化（idom 对于 IfThen 就是 header，值与隐式 else 赋值完全一致），
            // 避免双重物化导致冗余临时变量、多余引用和无意义 else 分支。
            None => None,
        };
        stmts.push(branch_stmt(
            {
                let mut cond = plan.cond;
                rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));
                cond
            },
            then_block,
            else_block,
        ));
        self.install_stop_boundary_value_merge_override(block, branch_stop, target_overrides);
        for header in &plan.consumed_headers {
            let branch_value_overrides = branch_target_overrides
                .clone()
                .unwrap_or_else(|| self.branch_value_target_overrides(*header, target_overrides));
            self.install_branch_value_merge_overrides(*header, &branch_value_overrides);
        }

        // 当普通分支路径处理了一个 header，而该 header 同时拥有 SC 值合流候选
        // 时（SC 由于 BVM 共存而退让到了这里），需要把 header 加入
        // merge_allowed_blocks。这样 merge block 的 lower_phi_materialization
        // 才能在 SC 恢复时识别 header 内的 temp 为"安全可引用"，正确恢复
        // SC phi 的值表达式。
        if let Some(sc) = value_merge_candidate_by_header(self.lowering, block)
            && let ShortCircuitExit::ValueMerge(sc_merge) = sc.exit
            && branch_stop == Some(sc_merge)
        {
            self.merge_allowed_blocks
                .entry(sc_merge)
                .or_default()
                .insert(block);
        }

        match branch_stop {
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next) => Some(Some(next)),
            None => Some(None),
        }
    }

    fn if_then_downstream_merge_stop(
        &self,
        plan: &StructuredBranchPlan,
        branch_stop: Option<BlockRef>,
        region_stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let merge = plan.merge?;
        if plan.else_entry.is_some()
            || branch_stop != Some(merge)
            || region_stop == Some(merge)
            || self.branch_by_header.contains_key(&merge)
            || self.loop_by_header.contains_key(&merge)
            || self.block_is_terminal_exit(merge)
        {
            return None;
        }
        let downstream = self.lowering.cfg.unique_reachable_successor(merge)?;
        // if-then 的缺席 else 会先经过 merge；但只有 then 臂能绕过 merge 直接到达
        // downstream 时，merge 才是在语义上独占的隐式 else 块。若 then 臂必须经过
        // merge，merge 就是两条路径共享的 tail，不能被提前放进 else 臂。
        self.can_reach_avoiding_block(plan.then_entry, downstream, merge)
            .then_some(downstream)
    }

    fn implicit_else_merge_entry(
        &self,
        plan: &StructuredBranchPlan,
        branch_stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let merge = plan.merge?;
        if Some(merge) == branch_stop {
            return None;
        }
        if self.block_is_terminal_exit(merge) {
            return Some(merge);
        }
        let stop = branch_stop?;
        if plan.else_entry.is_none()
            && plan.then_entry == stop
            && self.branch_arm_reaches_stop_or_loop_escape(merge, stop, stop)
        {
            return Some(merge);
        }
        self.lowering
            .cfg
            .unique_reachable_successor(merge)
            .filter(|successor| *successor == stop)
            .map(|_| merge)
    }

    fn shared_continuation_branch(
        &self,
        plan: &StructuredBranchPlan,
        stop: Option<BlockRef>,
    ) -> Option<SharedContinuationBranch> {
        if plan.consumed_headers.is_empty() {
            return None;
        }
        let else_entry = plan.else_entry?;
        let merge = plan.merge.unwrap_or(self.lowering.cfg.exit_block);
        if self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target.is_none()
                && loop_context.post_loop == merge
                && stop.is_some_and(|stop| {
                    self.branch_regions_by_header
                        .get(&plan.consumed_headers[0])
                        .is_some_and(|region| region.structured_blocks.contains(&stop))
                })
        }) {
            return None;
        }
        if self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target == Some(merge) && self.loop_continue_target_is_empty(merge)
        }) {
            // 当前 merge 是空的 loop latch 时，一条臂走到 merge 只表示“本轮自然结束”，
            // 不能把另一条臂误认成 shared continuation。否则 `if a then body else tail end`
            // 会被拆成 `if a then body; continue end; tail`，Lua 5.1 目标只能退成 goto。
            return None;
        }
        if self.block_has_unstructured_continue_requirement(plan.then_entry)
            || self.block_has_unstructured_continue_requirement(else_entry)
        {
            return None;
        }
        if plan
            .consumed_headers
            .iter()
            .any(|header| self.branch_value_merges_by_header.contains_key(header))
        {
            return None;
        }

        let merge_is_explicit = plan.merge.is_some();
        let then_is_shared = else_entry != merge
            && plan.then_entry != merge
            && (merge_is_explicit
                || self.loop_preheader_exits_to_shared(else_entry, plan.then_entry))
            && self.entry_reaches_shared_continuation(else_entry, plan.then_entry, merge);
        if then_is_shared {
            return Some(SharedContinuationBranch {
                gated_entry: else_entry,
                shared_entry: plan.then_entry,
                negate_cond: true,
            });
        }

        let else_is_shared = else_entry != merge
            && plan.then_entry != merge
            && (merge_is_explicit
                || self.loop_preheader_exits_to_shared(plan.then_entry, else_entry))
            && self.entry_reaches_shared_continuation(plan.then_entry, else_entry, merge);
        else_is_shared.then_some(SharedContinuationBranch {
            gated_entry: plan.then_entry,
            shared_entry: else_entry,
            negate_cond: false,
        })
    }

    fn terminal_loop_continuation_branch(
        &self,
        plan: &StructuredBranchPlan,
        stop: Option<BlockRef>,
    ) -> Option<SharedContinuationBranch> {
        if stop.is_some()
            || plan.merge.is_some()
            || plan.consumed_headers.len() != 1
            || plan
                .consumed_headers
                .iter()
                .any(|header| self.branch_value_merges_by_header.contains_key(header))
        {
            return None;
        }
        let else_entry = plan.else_entry?;
        if self.block_has_unstructured_continue_requirement(plan.then_entry)
            || self.block_has_unstructured_continue_requirement(else_entry)
        {
            return None;
        }

        if self.entry_is_terminal_generic_for_guard(else_entry, plan.then_entry) {
            return Some(SharedContinuationBranch {
                gated_entry: else_entry,
                shared_entry: plan.then_entry,
                negate_cond: true,
            });
        }
        self.entry_is_terminal_generic_for_guard(plan.then_entry, else_entry)
            .then_some(SharedContinuationBranch {
                gated_entry: plan.then_entry,
                shared_entry: else_entry,
                negate_cond: false,
            })
    }

    fn entry_is_terminal_generic_for_guard(&self, entry: BlockRef, shared: BlockRef) -> bool {
        if self.can_reach(entry, shared) {
            return false;
        }
        let Some(header) = self.lowering.cfg.unique_reachable_successor(entry) else {
            return false;
        };
        let Some(candidate) = self.loop_by_header.get(&header).copied() else {
            return false;
        };
        if !candidate.reducible
            || candidate.kind_hint != LoopKindHint::GenericForLike
            || candidate.preheader != Some(entry)
        {
            return false;
        }

        candidate.exits.iter().all(|exit| {
            !self.can_reach(*exit, shared)
                && self.entry_must_reach_shared_or_terminate(
                    *exit,
                    shared,
                    self.lowering.cfg.exit_block,
                )
        })
    }

    fn loop_preheader_exits_to_shared(&self, preheader: BlockRef, shared: BlockRef) -> bool {
        let Some(header) = self.lowering.cfg.unique_reachable_successor(preheader) else {
            return false;
        };
        self.loop_by_header.get(&header).is_some_and(|candidate| {
            candidate.preheader == Some(preheader) && candidate.exits.contains(&shared)
        })
    }

    fn entry_reaches_shared_continuation(
        &self,
        entry: BlockRef,
        shared: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        self.entry_must_reach_or_escape_before_boundary(entry, shared, boundary)
            || self.entry_must_reach_shared_or_terminate(entry, shared, boundary)
    }

    fn entry_must_reach_shared_or_terminate(
        &self,
        entry: BlockRef,
        shared: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            shared: BlockRef,
            boundary: BlockRef,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == shared {
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
                    visit(lowerer, successor, shared, boundary, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        // shared continuation 可能在 generic/numeric loop 的正常出口之后。
        // 这类 arm 内部存在回边，不能因为看到 cycle 就认定它无法到达 shared；
        // 只要所有非终止出口都被约束到 shared，就可以把 shared 留给外层顺序消费。
        visit(
            self,
            entry,
            shared,
            boundary,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    // 有些 elseif 链在结构事实上已经有共享 tail，但其中几条臂会先跳到外层 merge
    // 来跳过这段 tail。HIR 不能把这种跳转直接丢给 goto，也不能复制 tail；用一个
    // `repeat ... until true` fence 承载这些早退边，才能把共享 tail 保持为单一
    // continuation，并让后续 AST/generate 继续产出目标方言可用的结构化代码。
    fn try_lower_single_pass_repeat_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let candidate = *self.branch_by_header.get(&block)?;
        // 目前只接管 repeat header 被当作普通 branch 重新 lower 的场景。普通
        // branch-value merge 若被强行套 fence，容易把结果 phi 隔在 fence 内外两侧。
        let loop_candidate = self.loop_by_header.get(&block).copied()?;
        if loop_candidate.kind_hint != LoopKindHint::RepeatLike {
            return None;
        }
        let merge = candidate.merge?;
        if self
            .lowering
            .structure
            .short_circuit_candidates
            .iter()
            .any(|short| short.reducible && short.header == block)
        {
            return None;
        }
        if self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target.is_none() && loop_context.post_loop == merge
        }) {
            return None;
        }
        let tail = self.single_pass_repeat_tail(block, candidate)?;
        if Some(tail) == stop {
            return None;
        }

        let region = self.branch_regions_by_header.get(&block).copied()?;
        let loop_context = ActiveLoopContext {
            header: block,
            loop_blocks: region.structured_blocks.clone(),
            post_loop: merge,
            downstream_post_loop: None,
            continue_target: None,
            continue_sources: BTreeSet::new(),
            break_exits: BTreeMap::new(),
            state_slots: Vec::new(),
        };

        self.active_loops.push(loop_context);
        let body_result = self.lower_region_with_suppressed_loop(
            block,
            Some(tail),
            target_overrides,
            Some(block),
        );
        self.active_loops.pop();
        let mut body = body_result?.stmts;
        let tail_preds = BTreeSet::from([tail]);
        let tail_target_overrides =
            self.branch_value_target_overrides_for_preds(block, &tail_preds, target_overrides);
        body.extend(self.lower_block_prefix(tail, false, &tail_target_overrides)?);
        self.visited.insert(tail);
        stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock { stmts: body },
            cond: HirExpr::Boolean(true),
        })));
        Some(Some(merge))
    }

    fn single_pass_repeat_tail(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
    ) -> Option<BlockRef> {
        let merge = candidate.merge?;
        let region = self.branch_regions_by_header.get(&block).copied()?;
        region
            .structured_blocks
            .iter()
            .copied()
            .filter(|tail| {
                *tail != block
                    && *tail != merge
                    && !self.required_labels.contains(tail)
                    && !self.branch_by_header.contains_key(tail)
                    && !self.loop_by_header.contains_key(tail)
                    && self.linear_tail_target(*tail) == Some(merge)
                    && self.region_predecessor_count(*tail, &region.structured_blocks) >= 2
                    && self.branch_arm_reaches_target_or_boundary(
                        candidate.then_entry,
                        *tail,
                        merge,
                    )
                    && candidate.else_entry.is_none_or(|else_entry| {
                        self.branch_arm_reaches_target_or_boundary(else_entry, *tail, merge)
                    })
            })
            .min()
    }

    fn linear_tail_target(&self, block: BlockRef) -> Option<BlockRef> {
        if matches!(
            self.block_terminator(block)
                .map(|(_instr_ref, instr)| instr),
            Some(
                LowInstr::Branch(_)
                    | LowInstr::NumericForInit(_)
                    | LowInstr::NumericForLoop(_)
                    | LowInstr::GenericForLoop(_)
                    | LowInstr::Return(_)
                    | LowInstr::TailCall(_)
            )
        ) {
            return None;
        }
        self.lowering.cfg.unique_reachable_successor(block)
    }

    fn region_predecessor_count(&self, block: BlockRef, region: &BTreeSet<BlockRef>) -> usize {
        self.lowering.cfg.preds[block.index()]
            .iter()
            .filter(|edge_ref| region.contains(&self.lowering.cfg.edges[edge_ref.index()].from))
            .count()
    }

    fn branch_arm_reaches_target_or_boundary(
        &self,
        entry: BlockRef,
        target: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            target: BlockRef,
            boundary: BlockRef,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == target || block == boundary {
                return true;
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
                    visit(lowerer, successor, target, boundary, visiting, memo)
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            target,
            boundary,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    fn block_has_unstructured_continue_requirement(&self, block: BlockRef) -> bool {
        self.lowering
            .structure
            .goto_requirements
            .iter()
            .any(|requirement| {
                requirement.from == block
                    && requirement.reason == GotoReason::UnstructuredContinueLike
            })
    }

    fn entry_must_reach_or_escape_before_boundary(
        &self,
        entry: BlockRef,
        target: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        let boundary_is_loop_escape = self.active_loops.last().is_some_and(|loop_context| {
            (loop_context.continue_target == Some(boundary)
                && self.loop_continue_target_is_empty(boundary))
                || loop_context.post_loop == boundary
                || loop_context.downstream_post_loop == Some(boundary)
        });

        fn visit(
            lowerer: &StructuredBodyLowerer<'_, '_>,
            block: BlockRef,
            target: BlockRef,
            boundary: BlockRef,
            boundary_is_loop_escape: bool,
            visiting: &mut BTreeSet<BlockRef>,
            memo: &mut BTreeMap<BlockRef, bool>,
        ) -> bool {
            if block == target {
                return true;
            }
            if block == boundary {
                return boundary_is_loop_escape;
            }
            if !lowerer.lowering.cfg.reachable_blocks.contains(&block) {
                return false;
            }
            if block == lowerer.lowering.cfg.exit_block || lowerer.block_is_terminal_exit(block) {
                return true;
            }
            if let Some(result) = memo.get(&block).copied() {
                return result;
            }
            if !visiting.insert(block) {
                return false;
            }

            let result = lowerer.lowering.cfg.succs[block.index()]
                .iter()
                .all(|edge_ref| {
                    let successor = lowerer.lowering.cfg.edges[edge_ref.index()].to;
                    visit(
                        lowerer,
                        successor,
                        target,
                        boundary,
                        boundary_is_loop_escape,
                        visiting,
                        memo,
                    )
                });
            visiting.remove(&block);
            memo.insert(block, result);
            result
        }

        visit(
            self,
            entry,
            target,
            boundary,
            boundary_is_loop_escape,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }

    fn lower_shared_continuation_branch(
        &mut self,
        shared: SharedContinuationBranch,
        plan: &StructuredBranchPlan,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        for block in &plan.consumed_blocks {
            self.visited.insert(*block);
        }

        let gated_block = self.lower_region(
            shared.gated_entry,
            Some(shared.shared_entry),
            target_overrides,
        )?;
        let mut cond = if shared.negate_cond {
            plan.cond.clone().negate()
        } else {
            plan.cond.clone()
        };
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));
        stmts.push(branch_stmt(cond, gated_block, None));
        Some(Some(shared.shared_entry))
    }

    fn try_lower_terminal_else_guard_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let stop = stop?;
        let plan = self.build_plain_branch_plan(block)?;
        let merge = plan.merge?;
        if plan.else_entry.is_some()
            || plan.consumed_headers.len() != 1
            || !self.block_is_terminal_exit(merge)
            || !self.can_reach_avoiding_block(plan.then_entry, stop, merge)
        {
            return None;
        }

        // 形如 `if not a then return x end; if not b then return x end; ...`
        // 的 guard 链在 CFG 里常共享同一个 terminal return block。普通 if/else lowering
        // 会试图多次 visit 这个 block；这里把 terminal return 克隆进每个 guard 分支，
        // 语义上每条路径仍只执行一次 return，同时不会让共享 terminal 阻塞后续 guard。
        let terminal_block = self.lower_terminal_exit_block_clone(merge, target_overrides)?;
        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.insert(merge);
        let mut cond = plan.cond.negate();
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));
        stmts.push(branch_stmt(cond, terminal_block, None));
        Some(Some(plan.then_entry))
    }

    pub(super) fn lower_terminal_exit_block_clone(
        &self,
        block: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if !self.terminal_exit_block_is_clone_safe(block) {
            return None;
        }
        let mut stmts = self.lower_block_prefix(block, false, target_overrides)?;
        let (instr_ref, instr) = self.block_terminator(block)?;
        let empty_labels = BTreeMap::new();
        let mut lowered =
            lower_control_instr(self.lowering, block, instr_ref, instr, &empty_labels);
        apply_loop_rewrites(&mut lowered, target_overrides);
        if let Some(entry_expr_overrides) = self.block_entry_expr_overrides(block) {
            for stmt in &mut lowered {
                rewrite_stmt_exprs(stmt, entry_expr_overrides);
            }
        }
        stmts.extend(lowered);
        Some(HirBlock { stmts })
    }
}
