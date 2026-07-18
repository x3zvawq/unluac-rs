//! 这个文件承载 structured body lowering 里的分支恢复细节。
//!
//! `body/mod.rs` 里既有 region 主循环，也有各种 branch/value-merge/loop-control 的细分
//! 恢复逻辑。把后者单独拆出来，是为了让“主流程如何行走 block”与“某个分支具体怎么
//! 降”分开维护；后面继续打磨 shared continuation、break/continue 或 terminal guard
//! 语义时，不需要在一个超大文件里来回跳转。
//!
//! 例子：`BranchCandidate { header, then, else, merge }` →
//! `HirStmt::If { cond, then_block, else_block }`。所有路径覆盖判断统一交给
//! `path_checks`；本文件不自行维护递归遍历或回环判定。

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

        let checkpoint = self.checkpoint_state(stmts.len());
        if let Some(next) = self.try_lower_single_pass_fence_break(block, stmts, target_overrides) {
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
        if let Some(next) = self.try_lower_loop_backedge_else_branch(block, stmts, target_overrides)
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
        let mut plan = short_plan.or_else(|| self.build_plain_branch_plan(block))?;
        if let Some(tail) = self.current_loop_shared_tail(&plan, stop) {
            plan.merge = Some(tail);
        }

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
        let mut branch_stop = self.branch_stop_for_region(
            block,
            plan.then_entry,
            plan.else_entry,
            plan.merge,
            stop,
            &plan.consumed_blocks,
        );
        if let Some(downstream) = self.if_then_downstream_merge_stop(&plan, branch_stop, stop) {
            branch_stop = Some(downstream);
        }
        let mut branch_value_candidates: Vec<&BranchValueMergeCandidate> = Vec::new();
        for header in &plan.consumed_headers {
            let region_candidate =
                branch_stop.and_then(|merge| self.branch_value_merge_for_region(*header, merge));
            for candidate in [
                region_candidate,
                self.branch_value_merge_for_header(*header),
            ]
            .into_iter()
            .flatten()
            {
                if branch_value_candidates.iter().any(|seen| {
                    seen.merge == candidate.merge
                        && seen
                            .values
                            .iter()
                            .map(|value| value.phi_id)
                            .eq(candidate.values.iter().map(|value| value.phi_id))
                }) {
                    continue;
                }
                branch_value_candidates.push(candidate);
            }
        }
        let branch_target_overrides = (!branch_value_candidates.is_empty()).then(|| {
            let mut overrides = target_overrides.clone();
            for candidate in &branch_value_candidates {
                overrides = self.branch_value_target_overrides(candidate, &overrides);
            }
            overrides
        });
        if let Some(branch_target_overrides) = branch_target_overrides.as_ref() {
            if !self.install_branch_def_targets(target_overrides, branch_target_overrides) {
                return None;
            }
            for candidate in &branch_value_candidates {
                stmts.extend(self.branch_value_preserved_entry_stmts(
                    candidate,
                    branch_target_overrides,
                    target_overrides,
                ));
            }
        }
        let arm_target_overrides = branch_target_overrides.as_ref().unwrap_or(target_overrides);
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
        let then_block =
            self.lower_branch_arm_region(block, plan.then_entry, then_stop, arm_target_overrides)?;
        let else_block = match effective_else_entry {
            Some(else_entry) => Some(self.lower_branch_arm_region(
                block,
                else_entry,
                else_stop,
                arm_target_overrides,
            )?),
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
        for candidate in &branch_value_candidates {
            let branch_value_overrides = branch_target_overrides
                .clone()
                .unwrap_or_else(|| self.branch_value_target_overrides(candidate, target_overrides));
            self.install_branch_value_merge_overrides(candidate, &branch_value_overrides);
        }

        // 当普通分支路径处理了一个 header，而该 header 同时拥有 SC 值合流候选
        // 时（SC 由于 BVM 共存而退让到了这里），需要把 header 加入
        // merge_allowed_blocks。这样 merge block 的 lower_phi_materialization
        // 才能在 SC 恢复时识别 header 内的 temp 为"安全可引用"，正确恢复
        // SC phi 的值表达式。
        if let Some(sc) = self.value_merge_candidate_by_header(block)
            && let ShortCircuitExit::ValueMerge(sc_merge) = sc.exit
            && branch_stop == Some(sc_merge)
        {
            self.merge_allowed_blocks.insert(sc_merge, block);
        }

        match branch_stop {
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next)
                if self
                    .active_loops
                    .last()
                    .is_some_and(|loop_context| loop_context.header == next) =>
            {
                Some(None)
            }
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
            || self.branch_candidate_for_header(merge).is_some()
            || self.has_loop_header(merge)
            || self.block_is_terminal_exit(merge)
        {
            return None;
        }
        let downstream = self.lowering.cfg.unique_reachable_successor(merge)?;
        // if-then 的缺席 else 会先经过 merge；但只有 then 臂能绕过 merge 直接到达
        // downstream 时，merge 才是在语义上独占的隐式 else 块。若 then 臂必须经过
        // merge，merge 就是两条路径共享的 tail，不能被提前放进 else 臂。
        let repeat_condition_is_downstream = self.can_emit_continue_stmt()
            && self.active_loops.last().is_some_and(|loop_context| {
                loop_context.continue_target == Some(downstream)
                    && self
                        .loop_candidate(loop_context.candidate_id)
                        .is_some_and(|candidate| candidate.kind_hint == LoopKindHint::RepeatLike)
            });
        (self.can_reach_avoiding_block(plan.then_entry, downstream, merge)
            && (!repeat_condition_is_downstream
                || !self.can_reach_avoiding_block(plan.then_entry, merge, downstream)))
        .then_some(downstream)
    }

    fn current_loop_shared_tail(
        &self,
        plan: &StructuredBranchPlan,
        stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let loop_context = self.active_loops.last()?;
        let continue_target = loop_context.continue_target?;
        let boundary = plan.merge?;
        let else_entry = plan.else_entry?;
        let region = self
            .branch_regions_by_header
            .get(plan.consumed_headers.first()?)?;
        if stop != Some(continue_target) || !self.block_is_active_loop_escape(boundary) {
            return None;
        }
        let direct_tails = self.lowering.cfg.preds[continue_target.index()]
            .iter()
            .map(|edge| self.lowering.cfg.edges[edge.index()].from);
        let nested_loop_preheaders = self
            .lowering
            .structure
            .loop_candidates
            .iter()
            .filter_map(|candidate| candidate.preheader);
        direct_tails
            .chain(nested_loop_preheaders)
            .filter(|tail| self.branch_region_contains(region, *tail))
            .filter(|tail| {
                *tail != plan.then_entry
                    && *tail != else_entry
                    && self.branch_candidate_for_header(*tail).is_none()
                    && !self.has_loop_header(*tail)
                    && self.region_predecessor_count(*tail, region) >= 2
                    && self.shared_tail_reaches_loop_continue(*tail, continue_target, loop_context)
                    && [plan.then_entry, else_entry].into_iter().any(|entry| {
                        self.entry_has_continue_owner_before_tail(
                            entry,
                            *tail,
                            boundary,
                            continue_target,
                            loop_context,
                        )
                    })
                    && self.branch_arm_reaches_target_or_boundary_or_terminate(
                        plan.then_entry,
                        *tail,
                        boundary,
                    )
                    && self.branch_arm_reaches_target_or_boundary_or_terminate(
                        else_entry, *tail, boundary,
                    )
            })
            .min()
    }

    fn shared_tail_reaches_loop_continue(
        &self,
        tail: BlockRef,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        self.lowering.cfg.unique_reachable_successor(tail) == Some(continue_target)
            || self
                .loop_candidate_from_preheader(tail)
                .is_some_and(|nested| {
                    !nested.exits.is_empty()
                        && nested.exits.iter().all(|exit| *exit == continue_target)
                        && nested
                            .blocks
                            .iter()
                            .all(|block| self.active_loop_contains(loop_context, *block))
                })
    }

    fn entry_has_continue_owner_before_tail(
        &self,
        entry: BlockRef,
        tail: BlockRef,
        boundary: BlockRef,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        let plain_merge_can_be_continue = self.loop_continue_target_is_empty(continue_target)
            || self
                .loop_candidate(loop_context.candidate_id)
                .is_some_and(|candidate| {
                    matches!(
                        candidate.kind_hint,
                        LoopKindHint::GenericForLike | LoopKindHint::RepeatLike
                    )
                });
        self.try_build_short_circuit_plan(entry, Some(tail))
            .flatten()
            .is_some_and(|plan| {
                self.short_circuit_continue_arm(&plan, continue_target, loop_context)
                    .is_some()
            })
            || (plain_merge_can_be_continue
                && self
                    .branch_candidate_for_header(entry)
                    .is_some_and(|branch| {
                        branch.else_entry.is_none()
                            && branch.merge == Some(continue_target)
                            && self.branch_arm_reaches_target_or_boundary_or_terminate(
                                branch.then_entry,
                                tail,
                                boundary,
                            )
                    }))
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
        if plan.else_entry.is_none()
            && self
                .branch_candidate_for_header(merge)
                .is_some_and(|candidate| {
                    candidate.else_entry.is_none()
                        && candidate.then_entry == stop
                        && candidate.merge.is_some_and(|break_exit| {
                            self.block_is_terminal_exit(break_exit)
                                || self.active_loops.last().is_some_and(|loop_context| {
                                    break_exit == loop_context.post_loop
                                        || Some(break_exit) == loop_context.downstream_post_loop
                                })
                        })
                })
            && self.branch_arm_reaches_stop_or_loop_escape(merge, stop, stop)
        {
            // 多后继 merge 若是“正常臂到 stop、另一臂 break”的结构 header，
            // 必须作为隐式 else 完整降低，不能跳过后续 break owner。
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
        if let Some((stop, continue_target)) = stop.zip(
            self.active_loops
                .last()
                .and_then(|loop_context| loop_context.continue_target),
        ) && stop != continue_target
        {
            let non_continue_entry = if plan.then_entry == continue_target {
                Some(else_entry)
            } else if else_entry == continue_target {
                Some(plan.then_entry)
            } else {
                None
            };
            if non_continue_entry
                .is_some_and(|entry| self.can_reach_avoiding_block(entry, stop, continue_target))
            {
                // early continue 会跳过调用方持有的近端 tail；不能把另一臂
                // 一直降到 loop condition，否则会提前消费这个 tail。
                return None;
            }
        }
        if self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target.is_none()
                && loop_context.post_loop == merge
                && stop.is_some_and(|stop| {
                    self.branch_regions_by_header
                        .get(&plan.consumed_headers[0])
                        .is_some_and(|region| self.branch_region_contains(region, stop))
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
            .any(|header| self.branch_value_merge_for_header(*header).is_some())
        {
            return None;
        }

        let merge_is_explicit = plan.merge.is_some();
        let then_is_shared = else_entry != merge
            && plan.then_entry != merge
            && (merge_is_explicit || self.preheader_loop_exits_to(else_entry, plan.then_entry))
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
            && (merge_is_explicit || self.preheader_loop_exits_to(plan.then_entry, else_entry))
            && self.entry_reaches_shared_continuation(plan.then_entry, else_entry, merge);
        else_is_shared.then_some(SharedContinuationBranch {
            gated_entry: plan.then_entry,
            shared_entry: else_entry,
            negate_cond: false,
        })
    }

    fn preheader_loop_exits_to(&self, preheader: BlockRef, target: BlockRef) -> bool {
        self.loop_candidate_from_preheader(preheader)
            .is_some_and(|candidate| {
                candidate.exits.iter().any(|exit| {
                    *exit == target || self.normalized_post_loop_successor(*exit) == Some(target)
                })
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
                .any(|header| self.branch_value_merge_for_header(*header).is_some())
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
        let Some((_, candidate)) = self.unique_loop_candidate_matching(header, |candidate| {
            candidate.kind_hint == LoopKindHint::GenericForLike
                && candidate.preheader == Some(entry)
        }) else {
            return false;
        };

        candidate.exits.iter().all(|exit| {
            !self.can_reach(*exit, shared)
                && self.branch_arm_reaches_shared_continuation_or_terminate(
                    *exit,
                    shared,
                    self.lowering.cfg.exit_block,
                )
        })
    }

    pub(super) fn loop_candidate_from_preheader(
        &self,
        preheader: BlockRef,
    ) -> Option<&'b LoopCandidate> {
        let header = match self.block_terminator(preheader) {
            Some((_instr_ref, LowInstr::NumericForInit(init))) => {
                self.lowering.cfg.instr_to_block[init.body_target.index()]
            }
            _ => self.lowering.cfg.unique_reachable_successor(preheader)?,
        };
        self.unique_loop_candidate_matching(header, |candidate| {
            candidate.preheader == Some(preheader)
        })
        .map(|(_, candidate)| candidate)
    }

    fn entry_reaches_shared_continuation(
        &self,
        entry: BlockRef,
        shared: BlockRef,
        boundary: BlockRef,
    ) -> bool {
        if self
            .active_loops
            .last()
            .and_then(|loop_context| loop_context.continue_target)
            .is_some_and(|continue_target| {
                shared != continue_target
                    && !self.can_reach_avoiding_block(entry, shared, continue_target)
            })
        {
            return false;
        }
        // shared tail 只要求非逃逸路径到达；active loop 的 break/continue 臂已有独立 owner。
        self.branch_arm_reaches_target_or_loop_escape_before_boundary(
            entry,
            shared,
            Some(boundary),
        )
            || self.branch_candidate_for_header(entry).is_some_and(|candidate| {
                candidate.else_entry.is_none()
                    && candidate.then_entry == shared
                    && candidate.merge == Some(boundary)
                    && self.block_is_active_loop_escape(boundary)
            })
            || (self.active_loops.last().is_some_and(|loop_context| {
                loop_context.continue_target == Some(boundary)
                    || (self.block_is_active_loop_escape(boundary)
                        && loop_context.continue_target.is_some_and(|continue_target| {
                            self.try_build_short_circuit_plan(entry, Some(shared))
                                .flatten()
                                .is_some_and(|plan| {
                                    self.short_circuit_continue_arm(
                                        &plan,
                                        continue_target,
                                        loop_context,
                                    )
                                    .is_some()
                                })
                        }))
            }) && self.branch_arm_reaches_stop_or_loop_escape(entry, shared, boundary))
            // repeat 的条件位于 body 尾部；一条源码 arm 可以先完整执行内层 loop，
            // 再选择进入本轮共享 tail 或直接 break。这里消费内层 loop 的显式 exits，
            // while/for 则继续沿用普通 shared-continuation 证明，避免跨过它们各自的
            // header/iterator owner 去扩大分支 region。
            || (self.active_loops.last().is_some_and(|loop_context| {
                self.loop_candidate(loop_context.candidate_id)
                    .is_some_and(|candidate| {
                        candidate.kind_hint == LoopKindHint::RepeatLike
                            && self.can_reach_avoiding_block(
                                entry,
                                shared,
                                loop_context.header,
                            )
                    })
            }) && self.has_loop_header(entry)
                && self.block_is_active_loop_escape(boundary)
                && self.branch_arm_reaches_stop_or_loop_escape(entry, shared, boundary))
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
        let candidate = self.branch_candidate_for_header(block)?;
        let region = self.branch_regions_by_header.get(&block).copied()?;
        if let Some(fence) = &region.single_pass_fence {
            return self.lower_single_pass_fence(block, region, fence, stmts, target_overrides);
        }
        let merge = candidate.merge?;
        // 除了直接被当作 branch 的 repeat header，LuaJIT 还会把“内层 repeat true
        // fence + 外层 retry loop”压成同一个 Unknown natural-loop header。只有该
        // Unknown owner 已经处于 active lowering，且 fence merge 仍在循环体内时，
        // 才复用它已经建立的 state/value owner；不能从普通 branch 猜一层新循环。
        let (loop_candidate_id, loop_candidate) = self.innermost_loop_candidate(block)?;
        let active_unknown_owner = self.active_loops.last().is_some_and(|loop_context| {
            loop_context.candidate_id == loop_candidate_id
                && loop_context.header == block
                && loop_candidate.kind_hint == LoopKindHint::Unknown
                && self.active_loop_contains(loop_context, merge)
                && merge != loop_context.post_loop
                && Some(merge) != loop_context.downstream_post_loop
        });
        if loop_candidate.kind_hint != LoopKindHint::RepeatLike && !active_unknown_owner {
            return None;
        }
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

        let loop_context = ActiveLoopContext {
            candidate_id: loop_candidate_id,
            header: block,
            loop_blocks: BTreeSet::new(),
            branch_region_header: Some(region.header),
            post_loop: merge,
            downstream_post_loop: None,
            continue_target: None,
            body_stop: Some(tail),
            continue_sources: BTreeSet::new(),
            continue_entries: BTreeSet::new(),
            break_exits: BTreeMap::new(),
            goto_exits: BTreeSet::new(),
            state_slots: Vec::new(),
            post_loop_break: None,
        };

        self.active_loops.push(loop_context);
        let body_result = self.lower_region_with_suppressed_loop(
            block,
            Some(tail),
            target_overrides,
            Some(loop_candidate_id),
        );
        self.active_loops.pop();
        let mut body = body_result?.stmts;
        let tail_preds = BTreeSet::from([tail]);
        let tail_target_overrides = self
            .branch_value_merge_for_header(block)
            .map(|candidate| {
                self.branch_value_target_overrides_for_preds(
                    candidate,
                    &tail_preds,
                    target_overrides,
                )
            })
            .unwrap_or_else(|| target_overrides.clone());
        body.extend(self.lower_block_prefix(tail, false, &tail_target_overrides)?);
        self.visited.insert(tail);
        stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock { stmts: body },
            cond: HirExpr::Boolean(true),
        })));
        Some(Some(merge))
    }

    fn lower_single_pass_fence(
        &mut self,
        block: BlockRef,
        region: &BranchRegionFact,
        fence: &SinglePassFenceFact,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        if self
            .active_single_pass_fences
            .last()
            .is_some_and(|active| active.header == block)
        {
            return None;
        }

        self.active_single_pass_fences.push(ActiveSinglePassFence {
            header: block,
            tail: region.merge,
            exit: fence.exit,
            escape_edges: fence.escape_edges.clone(),
        });
        let body_result = self.lower_region(block, Some(region.merge), target_overrides);
        self.active_single_pass_fences.pop();
        let mut body = body_result?.stmts;

        let mut tail_target_overrides = target_overrides.clone();
        tail_target_overrides.extend(
            self.overrides
                .def_targets()
                .iter()
                .map(|(temp, target)| (*temp, target.clone())),
        );
        let tail_preds = BTreeSet::from([region.merge]);
        if let Some(candidate) = self.branch_value_merge_for_header(block) {
            tail_target_overrides = self.branch_value_target_overrides_for_preds(
                candidate,
                &tail_preds,
                &tail_target_overrides,
            );
        }
        body.extend(self.lower_block_prefix(region.merge, false, &tail_target_overrides)?);
        self.visited.insert(region.merge);
        stmts.push(HirStmt::Repeat(Box::new(HirRepeat {
            body: HirBlock { stmts: body },
            cond: HirExpr::Boolean(true),
        })));
        Some(Some(fence.exit))
    }

    fn try_lower_single_pass_fence_break(
        &mut self,
        block: BlockRef,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let fence = self.active_single_pass_fences.last()?.clone();
        let (then_edge, else_edge) = self.lowering.cfg.branch_edges(block)?;
        let (break_edge, next_edge) = match (
            fence.escape_edges.contains(&then_edge),
            fence.escape_edges.contains(&else_edge),
        ) {
            (true, false) => (then_edge, else_edge),
            (false, true) => (else_edge, then_edge),
            _ => return None,
        };
        let break_entry = self.lowering.cfg.edges[break_edge.index()].to;
        let next_entry = self.lowering.cfg.edges[next_edge.index()].to;
        if next_entry != fence.tail
            && self.lowering.cfg.unique_reachable_successor(next_entry) != Some(fence.tail)
        {
            return None;
        }

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        if break_entry != fence.exit {
            if !self
                .lower_block_prefix(break_entry, false, target_overrides)?
                .is_empty()
            {
                return None;
            }
            self.visited.insert(break_entry);
        }
        self.visited.insert(block);

        if let Some(candidate) = self.branch_value_merge_for_header(block) {
            let branch_target_overrides =
                self.branch_value_target_overrides(candidate, target_overrides);
            if !self.install_branch_def_targets(target_overrides, &branch_target_overrides) {
                return None;
            }
            stmts.extend(self.branch_value_preserved_entry_stmts(
                candidate,
                &branch_target_overrides,
                target_overrides,
            ));
            self.install_branch_value_merge_overrides(candidate, &branch_target_overrides);
        }

        let mut break_cond = self.lower_branch_cond_for_target(block, break_entry)?;
        rewrite_expr_temps(&mut break_cond, &temp_expr_overrides(target_overrides));
        stmts.push(branch_stmt(
            break_cond,
            HirBlock {
                stmts: vec![HirStmt::Break],
            },
            None,
        ));
        Some(Some(next_entry))
    }

    fn install_branch_def_targets(
        &mut self,
        inherited: &BTreeMap<TempId, HirLValue>,
        branch_targets: &BTreeMap<TempId, HirLValue>,
    ) -> bool {
        branch_targets
            .iter()
            .filter(|(temp, target)| inherited.get(temp) != Some(*target))
            .all(|(temp, target)| self.overrides.insert_def_target(*temp, target.clone()))
    }

    fn single_pass_repeat_tail(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
    ) -> Option<BlockRef> {
        let merge = candidate.merge?;
        let region = self.branch_regions_by_header.get(&block).copied()?;
        self.lowering.cfg.preds[merge.index()]
            .iter()
            .map(|edge| self.lowering.cfg.edges[edge.index()].from)
            .filter(|tail| self.branch_region_contains(region, *tail))
            .filter(|tail| {
                *tail != block
                    && *tail != merge
                    && !self.required_labels.contains(tail)
                    && self.branch_candidate_for_header(*tail).is_none()
                    && !self.has_loop_header(*tail)
                    && self.linear_tail_target(*tail) == Some(merge)
                    && self.region_predecessor_count(*tail, region) >= 2
                    && self.branch_arm_reaches_target_or_boundary_or_terminate(
                        candidate.then_entry,
                        *tail,
                        merge,
                    )
                    && candidate.else_entry.is_none_or(|else_entry| {
                        self.branch_arm_reaches_target_or_boundary_or_terminate(
                            else_entry, *tail, merge,
                        )
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

    fn region_predecessor_count(&self, block: BlockRef, region: &BranchRegionFact) -> usize {
        self.lowering.cfg.preds[block.index()]
            .iter()
            .filter(|edge_ref| {
                self.branch_region_contains(region, self.lowering.cfg.edges[edge_ref.index()].from)
            })
            .count()
    }

    fn block_has_unstructured_continue_requirement(&self, block: BlockRef) -> bool {
        self.lowering
            .structure
            .goto_requirements
            .iter()
            .any(|requirement| {
                self.lowering.cfg.edges[requirement.edge.index()].from == block
                    && requirement.reason == GotoReason::UnstructuredContinueLike
            })
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
        self.install_proven_target_phi_overrides(shared.shared_entry, target_overrides);
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

    pub(in crate::hir::analyze::structure) fn lower_terminal_exit_block_clone(
        &self,
        block: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if !self.terminal_exit_block_can_clone(block, target_overrides) {
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
