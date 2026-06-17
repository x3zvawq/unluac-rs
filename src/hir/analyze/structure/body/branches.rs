//! 这个文件承载 structured body lowering 里的分支恢复细节。
//!
//! `body.rs` 里既有 region 主循环，也有各种 branch/value-merge/loop-control 的细分
//! 恢复逻辑。把后者单独拆出来，是为了让“主流程如何行走 block”与“某个分支具体怎么
//! 降”分开维护；后面继续打磨 branch merge 或 continue/break 语义时，不需要在一个
//! 超大文件里来回跳转。
//!
//! 当一个 header 同时拥有 SC (ShortCircuit) 值合流候选和 BranchValueMerge
//! 候选时，SC 只处理一个 result_reg 的 phi，而 BVM 认领了其余 phi。SC 系列
//! 快捷路径（conditional_reassign / statement_value_merge / value_merge）消费
//! 整个分支结构后，BVM 的 phi 就会因无人物化而丢失。为此：
//! - value_merge / conditional_reassign 路径在检测到 BVM 共存时退让给普通分支，
//!   让 BVM 通过 target_overrides 处理自身 phi，SC phi 则在 merge block 恢复。
//! - statement_value_merge 路径在 SC 表达式生成后，以 SC 树结构为骨架为 BVM
//!   phi 构建 Decision 表达式。
//!
//! 例子：SC 覆盖 r4 → `x and (y and 2 or 3) or 6`，BVM 覆盖 r3 →
//! 普通分支路径产出 `if x then ... end` 中的条件赋值。

use super::*;

use crate::cfg::DefId;

#[derive(Debug, Clone, Copy)]
struct SharedContinuationBranch {
    gated_entry: BlockRef,
    shared_entry: BlockRef,
    negate_cond: bool,
}

type StatementValueMergeOutput<'c> = (&'c ShortCircuitCandidate, TempId);

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

    pub(super) fn can_reach_avoiding_block(
        &self,
        from: BlockRef,
        to: BlockRef,
        avoided: BlockRef,
    ) -> bool {
        if from == avoided || to == avoided {
            return false;
        }
        let mut allowed_blocks = self.lowering.cfg.reachable_blocks.clone();
        allowed_blocks.remove(&avoided);
        self.lowering
            .cfg
            .can_reach_within(from, to, &allowed_blocks)
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
        if self.lowering.cfg.can_reach(entry, shared) {
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
            !self.lowering.cfg.can_reach(*exit, shared)
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

    fn try_lower_branch_exit_value_assignment(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let stop = stop?;
        if target_overrides.is_empty() {
            return None;
        }

        let short = self
            .lowering
            .structure
            .short_circuit_candidates
            .iter()
            .find(|candidate| {
                candidate.header == block
                    && candidate.reducible
                    && matches!(candidate.exit, ShortCircuitExit::BranchExit { .. })
            })?;
        let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
            return None;
        };

        let (value_leaf, negate_cond) = if falsy == stop {
            (truthy, false)
        } else if truthy == stop {
            (falsy, true)
        } else {
            return None;
        };
        if short.blocks.contains(&value_leaf)
            || self.branch_by_header.contains_key(&value_leaf)
            || self.loop_by_header.contains_key(&value_leaf)
        {
            return None;
        }

        let value_stmts = self.lower_block_prefix(value_leaf, false, target_overrides)?;
        if !branch_exit_value_assignment_leaf_stmts_are_safe(&value_stmts, target_overrides) {
            return None;
        }

        let allowed_blocks = BTreeSet::from([block]);
        let decision = build_branch_decision_expr_mixed_eval(
            self.lowering,
            short,
            short.entry,
            &allowed_blocks,
        )?;
        let mut cond = finalize_condition_decision_expr(decision);
        let condition_expr_overrides =
            self.branch_exit_condition_expr_overrides(short, target_overrides)?;
        rewrite_expr_temps(&mut cond, &condition_expr_overrides);
        if expr_references_forbidden_candidate_temps(self.lowering, short, &cond, &allowed_blocks) {
            return None;
        }
        if negate_cond {
            cond = cond.negate();
        }
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.extend(short.blocks.iter().copied());
        self.visited.insert(value_leaf);
        stmts.push(branch_stmt(cond, HirBlock { stmts: value_stmts }, None));
        Some(Some(stop))
    }

    fn branch_exit_condition_expr_overrides(
        &self,
        short: &ShortCircuitCandidate,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<BTreeMap<TempId, HirExpr>> {
        let mut expr_overrides = BTreeMap::new();
        for block in &short.blocks {
            let prefix = self.lower_block_prefix(*block, true, target_overrides)?;
            branch_exit_condition_prefix_expr_overrides(&prefix, &mut expr_overrides)?;
        }
        Some(expr_overrides)
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
        if !self.block_is_terminal_exit(block) {
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

    fn try_lower_conditional_reassign_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        // merge 恰好就是当前 region 的 stop 时，后面不会再真正进入 merge block。
        // 这类情况下如果继续走“先跳过分支、再靠 merge 点物化 phi”的快捷路径，
        // loop-carried/branch-carried 的写回就会直接丢掉。这里宁可退回普通 branch
        // lowering，让两臂里的赋值在当前结构里显式发生，也不把边界语义悄悄吞掉。
        if Some(merge) == stop {
            return None;
        }

        // 与 try_lower_value_merge_branch 同理：SC 系列快捷路径只处理一个
        // result_reg，BVM 认领的其他 phi 会因分支结构被消费而孤立。
        if let Some(bvm) = self.branch_value_merges_by_header.get(&block)
            && bvm
                .values
                .iter()
                .any(|v| Some(v.phi_id) != short.result_phi_id)
        {
            return None;
        }

        let plan = build_conditional_reassign_plan(self.lowering, block)?;

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        // try_lower_statement_value_merge_branch 处的同类守卫：条件重赋值同样把
        // phi temp 直接内联进语句，跳过了 apply_loop_rewrites，当 entry_defs
        // 被 loop state 接管时，写入会被遗漏。
        if value_merge_defs_are_overridden(self.lowering, short, target_overrides) {
            return None;
        }

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.overrides.suppress_phi(plan.phi_id);

        stmts.push(assign_stmt(
            vec![HirLValue::Temp(plan.target_temp)],
            vec![plan.init_value],
        ));
        stmts.push(branch_stmt(
            plan.cond,
            HirBlock {
                stmts: vec![assign_stmt(
                    vec![HirLValue::Temp(plan.target_temp)],
                    vec![plan.assigned_value],
                )],
            },
            None,
        ));

        Some(Some(plan.merge))
    }

    fn try_lower_statement_value_merge_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        // merge == stop 时仍可消费 value-merge 的分支块；merge block 自己的 prefix
        // 由外层 region（例如 numeric-for 的 continue pad）统一降低。
        let allowed_blocks = BTreeSet::from([block]);
        if recover_short_value_merge_expr_with_allowed_blocks(self.lowering, short, &allowed_blocks)
            .is_some()
        {
            return None;
        }

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        let outputs = self.statement_value_merge_outputs(short)?;
        let mut short_stmts = self.lower_block_prefix(block, true, target_overrides)?;
        short_stmts.extend(
            self.lower_value_merge_node(short, short.entry, &outputs, true, target_overrides)?
                .stmts,
        );

        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        for (output_short, _) in &outputs {
            self.overrides.suppress_phi(output_short.result_phi_id?);
        }
        stmts.extend(short_stmts);

        // SC 值合流只处理了 result_phi 对应的一个寄存器。如果同一 header 下还有
        // BranchValueMerge 认领的其他 phi，它们的分支结构已被 SC 消费——正常
        // 分支路径不会再运行。这里利用 SC 的树结构，为每个孤立的 BVM phi 构建
        // 平行的 Decision 表达式，避免这些 phi 因无人物化而丢失。
        if let Some(bvm) = self.branch_value_merges_by_header.get(&block) {
            for value in &bvm.values {
                if Some(value.phi_id) == short.result_phi_id {
                    continue;
                }
                if let Some(decision_expr) =
                    self.build_secondary_value_merge_decision(short, value.reg)
                {
                    let bvm_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
                    let mut stmt =
                        assign_stmt(vec![HirLValue::Temp(bvm_temp)], vec![decision_expr]);
                    apply_loop_rewrites(std::slice::from_mut(&mut stmt), target_overrides);
                    stmts.push(stmt);
                    self.overrides.suppress_phi(value.phi_id);
                }
            }
        }

        Some(Some(merge))
    }

    fn statement_value_merge_outputs(
        &self,
        short: &'b ShortCircuitCandidate,
    ) -> Option<Vec<StatementValueMergeOutput<'b>>> {
        let mut outputs = Vec::new();
        for candidate in &self.lowering.structure.short_circuit_candidates {
            if !same_statement_value_merge_tree(short, candidate) {
                continue;
            }
            let temp = *self
                .lowering
                .bindings
                .phi_temps
                .get(candidate.result_phi_id?.index())?;
            outputs.push((candidate, temp));
        }
        (!outputs.is_empty()).then_some(outputs)
    }

    fn try_lower_value_merge_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let short = value_merge_candidate_by_header(self.lowering, block)?;
        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            return None;
        };
        // 注意：merge == stop 时仍然允许值合流消费分支结构块。调用方的循环会在
        // current == stop 时自然 break，不会再尝试进入 merge block。
        // merge block 的 block_prefix（含值合流 phi 物化）由外层调用方显式处理，
        // 例如 numeric-for body 会在 region 返回后单独 lower continue_block 的 prefix。

        // SC 值合流只处理一个 result_reg。如果同一 header 下 BranchValueMerge
        // 还认领了其他 phi，SC 消费分支结构后那些 phi 就无人物化。此时退让给
        // 普通分支路径：BVM 通过 target_overrides 处理自己的 phi，SC 的 phi 则
        // 在 merge block 的 lower_phi_materialization 中恢复。
        if let Some(bvm) = self.branch_value_merges_by_header.get(&block)
            && bvm
                .values
                .iter()
                .any(|v| Some(v.phi_id) != short.result_phi_id)
        {
            return None;
        }

        let allowed_blocks = BTreeSet::from([block]);
        let recovery = recover_short_value_merge_expr_recovery_with_allowed_blocks(
            self.lowering,
            short,
            &allowed_blocks,
        )?;

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        if recovery.consumes_header_subject() {
            self.overrides
                .suppress_instrs(consumed_value_merge_subject_instrs(self.lowering, block));
        }
        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        self.visited.extend(value_merge_skipped_blocks(short));
        self.merge_allowed_blocks
            .entry(merge)
            .or_default()
            .insert(block);
        Some(Some(merge))
    }

    fn try_lower_loop_break_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        // 多出口 loop 里最常见、也最值得先吃掉的形状是“主体继续跑，另一臂经 cleanup pad
        // 直接离开循环”。这里不把这类 pad 留给 fallback，而是在 HIR 里直接恢复成 break，
        // 这样后面的 AST/readability 就不用再对着 `close + jump` 反推源码意图。
        let loop_context = self.active_loops.last()?.clone();
        let candidate = *self.branch_by_header.get(&block)?;
        let break_exit = candidate.merge.filter(|merge| {
            loop_context.break_exits.contains_key(merge)
                || *merge == loop_context.post_loop
                || Some(*merge) == loop_context.downstream_post_loop
        })?;
        // 当前 region 已经给出更近的结构边界时，break 快捷路径不能跨过它去消费
        // loop 的 post block；否则共享 tail 会被提前塞进某个分支臂，外层结构就无法
        // 再把 tail 作为单一 continuation 恢复出来。
        if let Some(stop) = stop
            && stop != break_exit
            && loop_context.continue_target != Some(stop)
            && self
                .branch_regions_by_header
                .get(&block)
                .is_some_and(|region| region.structured_blocks.contains(&stop))
        {
            return None;
        }
        if self.block_exits_outer_active_loop(break_exit) {
            return None;
        }
        let pad_stmts = match candidate.else_entry {
            Some(else_entry)
                if else_entry != break_exit
                    && Some(else_entry) != loop_context.downstream_post_loop =>
            {
                let is_direct_jump = self.block_terminator(else_entry).is_some_and(|(_, instr)| {
                    if let LowInstr::Jump(jump) = instr {
                        let target = self.lowering.cfg.instr_to_block[jump.target.index()];
                        target == break_exit || Some(target) == loop_context.downstream_post_loop
                    } else {
                        false
                    }
                });
                if !is_direct_jump {
                    return None;
                }
                let pad_stmts = self.lower_block_prefix(else_entry, false, target_overrides)?;
                self.visited.insert(else_entry);
                pad_stmts
            }
            _ => Vec::new(),
        };
        let break_block = if break_exit == loop_context.post_loop
            || Some(break_exit) == loop_context.downstream_post_loop
        {
            // 当 break 路径上存在中间块（如 `found = {i,j}; break`），需要提取
            // 中间块的指令前缀到 break 之前，避免丢失赋值等副作用。若 else 臂
            // 不是这种单块线性 break pad，上面的校验会退让给普通分支 lowering。
            let mut stmts = pad_stmts;
            stmts.push(HirStmt::Break);
            HirBlock { stmts }
        } else {
            loop_context.break_exits[&break_exit].block.clone()
        };
        // break 臂之外的那一臂，很多时候只是继续执行当前 loop body，最后再回到
        // continue target。如果这里一口气把它降到 break pad 的出口，repeat/for 的
        // loop tail 就会被一起吞进去，随后整片 region 只能 fallback。这里优先把
        // 非 break 臂截到当前 loop 的 continue target；只有确实没有这条稳定回路时，
        // 才继续沿用 break exit 作为边界。
        let body_stop = loop_context
            .continue_target
            .filter(|target| {
                *target != break_exit
                    && (candidate.then_entry == *target
                        || self.lowering.cfg.can_reach(candidate.then_entry, *target))
            })
            .or(Some(break_exit));
        let then_block = self.lower_region(candidate.then_entry, body_stop, target_overrides)?;
        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        if break_exit != loop_context.post_loop
            && Some(break_exit) != loop_context.downstream_post_loop
        {
            self.visited.insert(break_exit);
        }

        if body_stop == Some(break_exit)
            && break_block.stmts.last() == Some(&HirStmt::Break)
            && then_block.stmts == break_block.stmts[..break_block.stmts.len() - 1]
        {
            stmts.extend(then_block.stmts);
            stmts.push(branch_stmt(
                cond.negate(),
                HirBlock {
                    stmts: vec![HirStmt::Break],
                },
                None,
            ));
            return Some(None);
        }

        if then_block.stmts.is_empty() {
            stmts.push(branch_stmt(cond.negate(), break_block, None));
        } else {
            stmts.push(branch_stmt(cond, then_block, Some(break_block)));
        }

        match body_stop {
            Some(next) if next == break_exit => Some(None),
            Some(next) if next == self.lowering.cfg.exit_block => Some(None),
            Some(next) => Some(Some(next)),
            None => Some(None),
        }
    }

    fn try_lower_loop_terminal_else_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let loop_context = self.active_loops.last()?.clone();
        let stop = stop?;
        if loop_context.continue_target != Some(stop) {
            return None;
        }
        let candidate = *self.branch_by_header.get(&block)?;
        let merge = candidate.merge?;
        if candidate.else_entry.is_some()
            || merge == stop
            || self.branch_value_merges_by_header.contains_key(&block)
            || !self.can_reach_avoiding_block(candidate.then_entry, stop, merge)
            || !self.branch_arm_terminates_before_stop(merge, stop)
        {
            return None;
        }

        let then_target_overrides =
            self.branch_entry_target_overrides(block, Some(candidate.then_entry), target_overrides);
        let then_block =
            self.lower_region(candidate.then_entry, Some(stop), &then_target_overrides)?;
        let else_block = self.lower_region(merge, Some(stop), target_overrides)?;
        let mut cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);
        stmts.push(branch_stmt(cond, then_block, Some(else_block)));
        Some(Some(stop))
    }

    fn cross_structure_escape_target(&self, block: BlockRef) -> Option<BlockRef> {
        let loop_context = self.active_loops.last()?;
        let candidate = self.branch_by_header.get(&block).copied()?;
        let merge = candidate.merge?;
        let continue_target = loop_context.continue_target?;
        if self.block_exits_outer_active_loop(merge)
            && (candidate.then_entry == continue_target
                || self
                    .lowering
                    .cfg
                    .can_reach(candidate.then_entry, continue_target))
        {
            return Some(merge);
        }

        // 这类形状常见于 `if cond then goto after_outer_loop end`：
        // 分支的一臂仍然沿当前 loop 继续跑，另一臂却直接跳到当前 loop 之外更远的 merge。
        // 如果这里继续把它硬恢复成普通 `if-then`，缺席的那一臂会被误当成
        // “自然回到当前 region 的 stop”，最终把跨层 `goto` 偷偷降成错误的 loop fallthrough。
        //
        // 对这种跨层退出，当前 structured HIR 没有等价的 `break/continue` 语义可承载；
        // 与其在局部生成半真半假的结构，不如让整片 proto 退回显式 label/goto 形态，
        // 由更保守但语义直观的 fallback 接手。
        if candidate.else_entry.is_some()
            || merge == loop_context.post_loop
            || Some(merge) == loop_context.downstream_post_loop
            || loop_context.break_exits.contains_key(&merge)
            || self.block_is_terminal_exit(merge)
        {
            return None;
        }

        let loop_candidate = self.loop_by_header.get(&loop_context.header).copied()?;
        if loop_candidate.blocks.contains(&merge) {
            return None;
        }

        (candidate.then_entry == continue_target
            || self
                .lowering
                .cfg
                .can_reach(candidate.then_entry, continue_target))
        .then_some(merge)
    }

    fn lower_cross_structure_escape_branch(
        &mut self,
        block: BlockRef,
        escape_target: BlockRef,
        _stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        let loop_context = self.active_loops.last()?.clone();
        let continue_target = loop_context.continue_target?;
        let candidate = *self.branch_by_header.get(&block)?;

        let mut keep_cond = self.lower_candidate_cond(block, candidate)?;
        rewrite_expr_temps(&mut keep_cond, &temp_expr_overrides(target_overrides));

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        let escape_block = self.lower_escape_edge(block, escape_target, target_overrides)?;
        let continue_block = if candidate.then_entry == continue_target {
            HirBlock::default()
        } else {
            self.lower_region(
                candidate.then_entry,
                Some(continue_target),
                target_overrides,
            )?
        };
        let continue_else = (!continue_block.stmts.is_empty()).then_some(continue_block);
        stmts.push(branch_stmt(keep_cond.negate(), escape_block, continue_else));

        Some(Some(continue_target))
    }

    fn try_lower_loop_continue_branch(
        &mut self,
        block: BlockRef,
        stop: Option<BlockRef>,
        stmts: &mut Vec<HirStmt>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Option<BlockRef>> {
        // continue-like requirement 既可能来自未来 dialect 的显式 continue，也可能只是
        // 当前循环内部一条“提前回到 continue target”的控制边。这里只在它确实是当前
        // active loop 的本地语义时才吸收；否则宁可保持 fallback，也不把跨结构跳转误判成 continue。
        let loop_context = self.active_loops.last()?.clone();
        let continue_target = loop_context.continue_target?;
        let continue_target_is_empty = self.loop_continue_target_is_empty(continue_target);
        let can_fallthrough_to_non_empty_continue = self
            .loop_by_header
            .get(&loop_context.header)
            .is_some_and(|candidate| {
                matches!(
                    candidate.kind_hint,
                    LoopKindHint::NumericForLike
                        | LoopKindHint::GenericForLike
                        | LoopKindHint::Unknown
                )
            });
        if !continue_target_is_empty && !can_fallthrough_to_non_empty_continue {
            return None;
        }
        if let Some(short_plan) = self.try_build_short_circuit_plan(block, stop).flatten() {
            let short_plan_has_continue_edge = short_plan.then_entry == continue_target
                || short_plan.else_entry == Some(continue_target);
            if !short_plan_has_continue_edge {
                return None;
            }
        }
        let branch_points_to_continue =
            self.branch_by_header.get(&block).is_some_and(|candidate| {
                candidate.then_entry == continue_target
                    || candidate.else_entry == Some(continue_target)
                    || candidate.merge == Some(continue_target)
            });
        if !loop_context.continue_sources.contains(&block) && !branch_points_to_continue {
            return None;
        }

        let candidate = *self.branch_by_header.get(&block)?;
        if candidate.then_entry != continue_target
            && candidate.else_entry != Some(continue_target)
            && candidate.merge != Some(continue_target)
        {
            return None;
        }
        if candidate.merge == Some(continue_target)
            && candidate.else_entry.is_some()
            && candidate.then_entry != continue_target
            && candidate.else_entry != Some(continue_target)
        {
            // 显式 if/else 的两条臂都先执行自己的 body，再共同落到当前 loop latch 时，
            // 这不是源码层的 early-continue，而是普通分支的自然收束。交给普通 branch
            // lowering 才能把剩余 loop body 保留在 else 臂里；否则 Lua 5.1 目标会被
            // 平白制造出 `continue`/`goto`。
            return None;
        }
        if self
            .non_continue_entry_for_continue_candidate(candidate, continue_target)
            .is_some_and(|entry| self.entry_is_direct_loop_break(entry, &loop_context))
        {
            return None;
        }
        let mut continue_cond = self.lower_branch_cond_for_target(block, continue_target)?;
        rewrite_expr_temps(&mut continue_cond, &temp_expr_overrides(target_overrides));
        let prefer_natural_fallthrough = self.prefer_natural_fallthrough_over_continue(
            block,
            candidate,
            continue_target,
            &loop_context,
        );
        if !continue_target_is_empty
            && !prefer_natural_fallthrough
            && candidate.merge != Some(continue_target)
        {
            return None;
        }
        let then_target_overrides =
            self.branch_entry_target_overrides(block, Some(candidate.then_entry), target_overrides);

        stmts.extend(self.lower_block_prefix(block, true, target_overrides)?);
        self.visited.insert(block);

        if let Some(break_exit) = candidate
            .merge
            .filter(|merge| loop_context.break_exits.contains_key(merge))
        {
            self.visited
                .extend(loop_context.break_exits[&break_exit].blocks.iter().copied());
            stmts.push(branch_stmt(
                continue_cond.negate(),
                loop_context.break_exits[&break_exit].block.clone(),
                None,
            ));
            return Some(None);
        }

        if let Some(else_entry) = candidate.else_entry {
            let non_continue_entry = if candidate.then_entry == continue_target {
                else_entry
            } else {
                candidate.then_entry
            };
            if let Some(break_block) = loop_context.break_exits.get(&non_continue_entry) {
                self.visited.extend(break_block.blocks.iter().copied());
                // 当前 branch 本身如果没有“主动提前跳到 continue target”的证据，
                // 那它更像 loop tail 上的“否则 break”判定：继续这一臂只是自然回到
                // 下一轮，不应该硬提升成显式 `continue`。否则像 Lua 5.1 这种没有
                // `continue` / `goto` 的 target dialect 会被我们平白制造出无法落地的语义。
                if prefer_natural_fallthrough {
                    stmts.push(branch_stmt(
                        continue_cond.negate(),
                        break_block.block.clone(),
                        None,
                    ));
                    return Some(None);
                }
                let continue_block = self.explicit_continue_block()?;
                let stmt = if candidate.then_entry == continue_target {
                    branch_stmt(
                        continue_cond,
                        continue_block,
                        Some(break_block.block.clone()),
                    )
                } else {
                    branch_stmt(
                        continue_cond.negate(),
                        break_block.block.clone(),
                        Some(continue_block),
                    )
                };
                stmts.push(stmt);
                return Some(None);
            }

            if prefer_natural_fallthrough {
                let non_continue_target_overrides = self.branch_entry_target_overrides(
                    block,
                    Some(non_continue_entry),
                    target_overrides,
                );
                let non_continue_block = self.lower_region(
                    non_continue_entry,
                    Some(continue_target),
                    &non_continue_target_overrides,
                )?;
                stmts.push(branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    None,
                ));
                return if !continue_target_is_empty && continue_target == loop_context.header {
                    Some(None)
                } else {
                    Some(Some(continue_target))
                };
            }

            let continue_block = self.explicit_continue_block()?;
            let branch_stop = self.branch_stop_for_region(
                block,
                candidate.then_entry,
                candidate.else_entry,
                candidate.merge,
                stop,
            );
            let non_continue_target_overrides = self.branch_entry_target_overrides(
                block,
                Some(non_continue_entry),
                target_overrides,
            );
            let non_continue_block = self.lower_region(
                non_continue_entry,
                branch_stop,
                &non_continue_target_overrides,
            )?;
            let stmt = if candidate.then_entry == continue_target {
                branch_stmt(continue_cond, continue_block, Some(non_continue_block))
            } else {
                branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    Some(continue_block),
                )
            };
            stmts.push(stmt);
            return match branch_stop {
                Some(next) if next == self.lowering.cfg.exit_block => Some(None),
                Some(next) => Some(Some(next)),
                None => Some(None),
            };
        }

        if candidate.then_entry == continue_target {
            // `if cond then continue end` 这类分支在 CFG 里会表现成“显式 continue 臂 +
            // 隐式 merge 臂”。这里把 merge 臂显式降成 else block，避免 loop body 因为
            // “只有 then、没有 else” 被迫整片 fallback。
            let non_continue_entry = candidate.merge?;
            if self.prefer_natural_fallthrough_over_continue(
                block,
                candidate,
                continue_target,
                &loop_context,
            ) {
                let branch_stop = if continue_target_is_empty {
                    stop
                } else {
                    Some(continue_target)
                };
                let non_continue_block =
                    self.lower_region(non_continue_entry, branch_stop, target_overrides)?;
                stmts.push(branch_stmt(
                    continue_cond.negate(),
                    non_continue_block,
                    None,
                ));
                return Some(None);
            }
            let non_continue_block =
                self.lower_region(non_continue_entry, stop, target_overrides)?;
            let continue_block = self.explicit_continue_block()?;
            stmts.push(branch_stmt(
                continue_cond,
                continue_block,
                Some(non_continue_block),
            ));
            return Some(None);
        }

        if candidate.merge == Some(continue_target) {
            // `if cond then body end` 这类 loop-tail guard 在 CFG 里会表现成
            // “显式一臂 + 隐式 merge”，而 merge 正好就是当前 loop 的 continue target。
            // 这种形状本质上是“条件满足时执行 body，否则自然落回 loop latch”，
            // 并不需要显式 `continue`。如果这里仍然强行提升成 `if ... then continue else ... end`，
            // Lua 5.1 这类没有 `continue` / `goto` 的 dialect 就会被我们凭空制造出
            // 无法落地的语义。
            // 这里虽然 merge 臂本身只是自然落回 continue target，但 header 上若已经有
            // branch-value merge，就仍然需要把“执行 body 的那一臂”接回共享状态槽位。
            // 否则 arm 内新算出来的 carried 值只会停留在 branch-local temp 上，等不到
            // continue target 就已经丢掉了写回。
            let non_continue_block = self.lower_region(
                candidate.then_entry,
                Some(continue_target),
                &then_target_overrides,
            )?;
            stmts.push(branch_stmt(
                continue_cond.negate(),
                non_continue_block,
                None,
            ));
            return Some(Some(continue_target));
        }

        let merge = candidate.merge.or(stop)?;
        let continue_block = self.explicit_continue_block()?;
        stmts.push(branch_stmt(continue_cond, continue_block, None));
        if merge == self.lowering.cfg.exit_block
            || (!continue_target_is_empty && continue_target == loop_context.header)
        {
            Some(None)
        } else {
            Some(Some(merge))
        }
    }

    fn prefer_natural_fallthrough_over_continue(
        &self,
        block: BlockRef,
        candidate: &BranchCandidate,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        if candidate.merge == Some(continue_target) {
            return false;
        }
        let Some(non_continue_entry) =
            self.non_continue_entry_for_continue_candidate(candidate, continue_target)
        else {
            return false;
        };
        // 当 structure 层的 goto 分析没有把该 block 标记为 continue source 时，
        // 说明这条指向 continue_target 的边完全可以被结构化 branch 自然吸收
        // （比如 `if cond then body end` 的隐式落回到循环头），不需要提升为显式
        // continue。只有 goto 分析确认了 unstructured continue-like 的 block 才
        // 需要后续的 terminal-exit / break-funnel 判定。
        if !loop_context.continue_sources.contains(&block) {
            return true;
        }
        // 只有当非 continue 臂本身就是 terminal exit，且从 CFG 上根本到不了当前
        // continue target 时，才能确定它是“提前结束本轮/本函数”的 guard 分支。
        // 像 repeat 里的 break funnel 虽然最终也可能不回到 continue target，但它本身
        // 仍然是一个需要继续展开的控制块，不能在这里过早压平成 guard-return。
        if matches!(
            self.block_terminator(non_continue_entry),
            Some((_instr_ref, LowInstr::Return(_) | LowInstr::TailCall(_)))
        ) && !self
            .lowering
            .cfg
            .can_reach(non_continue_entry, continue_target)
        {
            return true;
        }

        self.entry_is_break_funnel_to_continue(
            non_continue_entry,
            continue_target,
            loop_context,
            &mut BTreeSet::new(),
        )
    }

    fn non_continue_entry_for_continue_candidate(
        &self,
        candidate: &BranchCandidate,
        continue_target: BlockRef,
    ) -> Option<BlockRef> {
        if candidate.then_entry == continue_target {
            candidate.else_entry.or(candidate.merge)
        } else if candidate.else_entry == Some(continue_target) {
            Some(candidate.then_entry)
        } else {
            None
        }
    }

    fn entry_is_break_funnel_to_continue(
        &self,
        entry: BlockRef,
        continue_target: BlockRef,
        loop_context: &ActiveLoopContext,
        visited: &mut BTreeSet<BlockRef>,
    ) -> bool {
        if !visited.insert(entry) {
            return false;
        }
        if self.entry_is_direct_loop_break(entry, loop_context) {
            return true;
        }

        let Some(candidate) = self.branch_by_header.get(&entry).copied() else {
            return false;
        };
        let Some(non_continue_entry) =
            self.non_continue_entry_for_continue_candidate(candidate, continue_target)
        else {
            return false;
        };

        self.entry_is_break_funnel_to_continue(
            non_continue_entry,
            continue_target,
            loop_context,
            visited,
        )
    }

    fn entry_is_direct_loop_break(
        &self,
        entry: BlockRef,
        loop_context: &ActiveLoopContext,
    ) -> bool {
        loop_context.break_exits.contains_key(&entry)
            || entry == loop_context.post_loop
            || Some(entry) == loop_context.downstream_post_loop
    }

    fn lower_value_merge_node(
        &self,
        short: &ShortCircuitCandidate,
        node_ref: ShortCircuitNodeRef,
        outputs: &[StatementValueMergeOutput<'_>],
        prefix_emitted: bool,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        let node = short.nodes.get(node_ref.index())?;
        let mut stmts = Vec::new();

        if !prefix_emitted {
            stmts.extend(self.lower_block_prefix(node.header, true, target_overrides)?);
        }

        let mut cond = lower_short_circuit_subject(self.lowering, node.header)?;
        rewrite_expr_temps(&mut cond, &temp_expr_overrides(target_overrides));
        let truthy = self.lower_value_merge_target(
            short,
            node.header,
            &node.truthy,
            outputs,
            target_overrides,
        )?;
        let falsy = self.lower_value_merge_target(
            short,
            node.header,
            &node.falsy,
            outputs,
            target_overrides,
        )?;
        stmts.push(branch_stmt(cond, truthy, Some(falsy)));

        Some(HirBlock { stmts })
    }

    fn branch_entry_target_overrides(
        &self,
        header: BlockRef,
        entry: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let Some(entry) = entry else {
            return target_overrides.clone();
        };
        let Some(candidate) = self.branch_by_header.get(&header).copied() else {
            return target_overrides.clone();
        };

        if entry == candidate.then_entry {
            return self.branch_value_then_target_overrides(header, target_overrides);
        }
        if Some(entry) == candidate.else_entry {
            return self.branch_value_else_target_overrides(header, target_overrides);
        }

        target_overrides.clone()
    }

    fn lower_value_merge_target(
        &self,
        short: &ShortCircuitCandidate,
        current_header: BlockRef,
        target: &ShortCircuitTarget,
        outputs: &[StatementValueMergeOutput<'_>],
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        match target {
            ShortCircuitTarget::Node(next_ref) => {
                self.lower_value_merge_node(short, *next_ref, outputs, false, target_overrides)
            }
            ShortCircuitTarget::Value(block) => {
                self.lower_value_merge_leaf(current_header, *block, outputs, target_overrides)
            }
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
        }
    }

    fn lower_value_merge_leaf(
        &self,
        current_header: BlockRef,
        block: BlockRef,
        outputs: &[StatementValueMergeOutput<'_>],
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        let mut stmts = if block == current_header {
            Vec::new()
        } else {
            self.lower_block_prefix(block, false, target_overrides)?
        };
        for (short, target_temp) in outputs {
            let value = if block == current_header
                && header_subject_is_value_carrier(self.lowering, current_header, short.result_reg)
            {
                // Truthiness 测试在 result_reg 上：subject 运行时值即保留值。
                lower_short_circuit_subject(self.lowering, block)?
            } else {
                lower_materialized_value_leaf_expr(self.lowering, short, block)?
            };
            let mut stmt = assign_stmt(vec![HirLValue::Temp(*target_temp)], vec![value]);
            apply_loop_rewrites(std::slice::from_mut(&mut stmt), target_overrides);
            stmts.push(stmt);
        }

        Some(HirBlock { stmts })
    }

    /// 以 SC 的树结构为骨架，对一个不由 SC 覆盖的寄存器构建 Decision 表达式。
    ///
    /// 在每个叶子节点处读取该寄存器的 block 出口值，用与 SC 相同的分支条件
    /// 串联成一棵嵌套决策树。例子：SC 树为 `x and (y and 2 or 3) or 6` 只
    /// 覆盖 r4；对于 r3（叶子值 #2→1, #3→4, #4→5），这里会产出
    /// `Decision(x ? Decision(y ? 1 : 4) : 5)` 赋值到 r3 的 phi temp。
    fn build_secondary_value_merge_decision(
        &self,
        short: &ShortCircuitCandidate,
        reg: Reg,
    ) -> Option<HirExpr> {
        let mut nodes = Vec::new();
        self.build_secondary_decision_node(short, short.entry, reg, &mut nodes)?;
        Some(HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes,
        })))
    }

    fn build_secondary_decision_node(
        &self,
        short: &ShortCircuitCandidate,
        node_ref: ShortCircuitNodeRef,
        reg: Reg,
        nodes: &mut Vec<HirDecisionNode>,
    ) -> Option<HirDecisionNodeRef> {
        let node = short.nodes.get(node_ref.index())?;
        let my_ref = HirDecisionNodeRef(nodes.len());
        // 先占位，后续填充 test/truthy/falsy
        nodes.push(HirDecisionNode {
            id: my_ref,
            test: HirExpr::Nil,
            truthy: HirDecisionTarget::CurrentValue,
            falsy: HirDecisionTarget::CurrentValue,
        });

        let cond = lower_short_circuit_subject(self.lowering, node.header)?;
        let truthy = self.build_secondary_decision_target(short, &node.truthy, reg, nodes)?;
        let falsy = self.build_secondary_decision_target(short, &node.falsy, reg, nodes)?;

        nodes[my_ref.index()].test = cond;
        nodes[my_ref.index()].truthy = truthy;
        nodes[my_ref.index()].falsy = falsy;
        Some(my_ref)
    }

    fn build_secondary_decision_target(
        &self,
        short: &ShortCircuitCandidate,
        target: &ShortCircuitTarget,
        reg: Reg,
        nodes: &mut Vec<HirDecisionNode>,
    ) -> Option<HirDecisionTarget> {
        match target {
            ShortCircuitTarget::Node(next_ref) => {
                let node_ref = self.build_secondary_decision_node(short, *next_ref, reg, nodes)?;
                Some(HirDecisionTarget::Node(node_ref))
            }
            ShortCircuitTarget::Value(block) => {
                let value = expr_for_reg_at_block_exit(self.lowering, *block, reg);
                Some(HirDecisionTarget::Expr(value))
            }
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
        }
    }

    fn install_stop_boundary_value_merge_override(
        &mut self,
        header: BlockRef,
        branch_stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        let Some(merge) = branch_stop else {
            return;
        };
        let Some(short) = value_merge_candidate_by_header(self.lowering, header) else {
            return;
        };
        let ShortCircuitExit::ValueMerge(short_merge) = short.exit else {
            return;
        };
        if short_merge != merge {
            return;
        }

        let Some(phi_id) = short.result_phi_id else {
            return;
        };
        let Some(reg) = short.result_reg else {
            return;
        };
        let Some(expr) = shared_target_expr_from_overrides(self.lowering, short, target_overrides)
        else {
            return;
        };

        self.replace_phi_with_entry_expr(merge, phi_id, reg, expr);
    }
}

/// 条件重赋值路径直接把值合流压平成单个 temp 的赋值序列，无法像
/// statement value-merge 那样逐个叶子传递 target_overrides；当候选 defs
/// 已被外层 state/BVM 接管时，需要退回普通 branch lowering。
fn value_merge_defs_are_overridden(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> bool {
    if target_overrides.is_empty() {
        return false;
    }
    let is_overridden = |def: &DefId| {
        lowering
            .bindings
            .fixed_temps
            .get(def.index())
            .is_some_and(|temp| target_overrides.contains_key(temp))
    };
    short.entry_defs.iter().any(is_overridden)
        || short
            .value_incomings
            .iter()
            .any(|inc| inc.defs.iter().any(is_overridden))
}

fn same_statement_value_merge_tree(
    base: &ShortCircuitCandidate,
    candidate: &ShortCircuitCandidate,
) -> bool {
    if !base.reducible
        || !candidate.reducible
        || base.header != candidate.header
        || base.blocks != candidate.blocks
        || base.entry != candidate.entry
        || base.nodes.len() != candidate.nodes.len()
        || base.result_phi_id.is_none()
        || candidate.result_phi_id.is_none()
        || base.result_reg.is_none()
        || candidate.result_reg.is_none()
    {
        return false;
    }
    let (ShortCircuitExit::ValueMerge(base_merge), ShortCircuitExit::ValueMerge(candidate_merge)) =
        (&base.exit, &candidate.exit)
    else {
        return false;
    };
    if base_merge != candidate_merge {
        return false;
    }

    base.nodes
        .iter()
        .zip(&candidate.nodes)
        .all(|(base, candidate)| {
            base.id == candidate.id
                && base.header == candidate.header
                && base.truthy == candidate.truthy
                && base.falsy == candidate.falsy
        })
}

fn branch_exit_value_assignment_leaf_stmts_are_safe(
    stmts: &[HirStmt],
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> bool {
    let [HirStmt::Assign(assign)] = stmts else {
        return false;
    };
    let [target] = assign.targets.as_slice() else {
        return false;
    };
    let [value] = assign.values.as_slice() else {
        return false;
    };
    if !branch_exit_value_assignment_leaf_value_is_safe(value) {
        return false;
    }

    target_overrides
        .values()
        .any(|override_target| override_target == target)
}

fn branch_exit_value_assignment_leaf_value_is_safe(value: &HirExpr) -> bool {
    matches!(
        value,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
    )
}

fn branch_exit_condition_prefix_expr_overrides(
    stmts: &[HirStmt],
    expr_overrides: &mut BTreeMap<TempId, HirExpr>,
) -> Option<()> {
    for stmt in stmts {
        let HirStmt::Assign(assign) = stmt else {
            return None;
        };
        let [HirLValue::Temp(target)] = assign.targets.as_slice() else {
            return None;
        };
        let [value] = assign.values.as_slice() else {
            return None;
        };
        if !branch_exit_condition_prefix_expr_is_safe(value) {
            continue;
        }
        let mut value = value.clone();
        rewrite_expr_temps(&mut value, expr_overrides);
        expr_overrides.insert(*target, value);
    }
    Some(())
}

fn branch_exit_condition_prefix_expr_is_safe(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::TableAccess(access) => {
            branch_exit_condition_prefix_expr_is_safe(&access.base)
                && branch_exit_condition_prefix_expr_is_safe(&access.key)
        }
        HirExpr::Unary(unary) => branch_exit_condition_prefix_expr_is_safe(&unary.expr),
        HirExpr::Binary(binary) => {
            branch_exit_condition_prefix_expr_is_safe(&binary.lhs)
                && branch_exit_condition_prefix_expr_is_safe(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            branch_exit_condition_prefix_expr_is_safe(&logical.lhs)
                && branch_exit_condition_prefix_expr_is_safe(&logical.rhs)
        }
        HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Decision(_)
        | HirExpr::Unresolved(_)
        | HirExpr::Complex { .. } => false,
    }
}
