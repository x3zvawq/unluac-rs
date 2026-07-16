//! 这个文件承载 branch arm/region stop 的选择策略。
//!
//! branch lowering 在真正降低 then/else region 前，需要决定整个 branch 的外层 stop、
//! 单条 arm 的局部 stop，以及是否存在 shared continuation。这里只消费 `BranchRegionFact`
//! 和 `path_checks.rs` 已提供的可达性谓词；它不降低 block，也不重新构造 branch plan。
//!
//! 输入形状：`if/elseif` 的 then/else entry、merge 与外层 region stop。
//! 输出形状：then/else lowering 应使用的 stop block。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn branch_stop_for_region(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        merge: Option<BlockRef>,
        stop: Option<BlockRef>,
        consumed_blocks: &[BlockRef],
    ) -> Option<BlockRef> {
        if stop.is_none() {
            return merge.or_else(|| {
                self.branch_shared_continuation_stop(block, then_entry, else_entry, merge, None)
            });
        }
        let Some(stop) = stop else {
            return merge;
        };
        if let Some(loop_continuation) = self.loop_body_shared_continuation_stop(
            block,
            then_entry,
            else_entry,
            stop,
            consumed_blocks,
        ) {
            return Some(loop_continuation);
        }
        // if-then 没有显式 else 时，缺席的 else 路径本身就是落到 merge。
        // 即使 merge 是 terminal exit，也必须把它留作分支之后的共享 continuation；
        // 否则 then 臂会先消费 terminal merge，随后缺席 else 再次进入同一块而重入失败。
        if let Some(merge) = merge
            && merge != stop
            && else_entry.is_some()
            && self.block_is_terminal_exit(merge)
        {
            return if self.terminal_exit_block_is_clone_boundary(merge) {
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
                self.can_reach(then_entry, *candidate)
                    && self.can_reach(else_entry, *candidate)
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
            && (self.can_reach(region_stop, candidate) || !self.can_reach(candidate, region_stop))
        {
            return false;
        }

        let boundary = region_stop.unwrap_or(self.lowering.cfg.exit_block);
        self.branch_arm_reaches_shared_continuation_or_terminate(then_entry, candidate, boundary)
            && self.branch_arm_reaches_shared_continuation_or_terminate(
                else_entry, candidate, boundary,
            )
    }

    fn loop_body_shared_continuation_stop(
        &self,
        block: BlockRef,
        then_entry: BlockRef,
        else_entry: Option<BlockRef>,
        stop: BlockRef,
        consumed_blocks: &[BlockRef],
    ) -> Option<BlockRef> {
        // while 体内的 if/elseif 链经常有两类出口：一类是 break，另一类先汇合到
        // “本轮收尾”块（例如 i = i + 1）再回到 header。StructureFacts 的分支 merge
        // 会被 break 出口拉到 loop 外，此时若直接把分支臂降到 header，两条臂会重复
        // 消费同一个收尾块。这里只在所有非 escape 路径都能到达同一个回 header 块时，
        // 把该块作为当前分支的局部 stop，让它由外层 loop body 统一消费一次。
        let loop_context = self.active_loops.last()?;
        if loop_context.header != stop
            && loop_context.continue_target != Some(stop)
            && loop_context.body_stop != Some(stop)
        {
            return None;
        }
        let region = self.branch_regions_by_header.get(&block)?;
        let active_candidate = self.loop_candidate(loop_context.candidate_id)?;
        let active_header_has_numeric_for_owner = self.target.caps.continue_stmt
            && active_candidate.kind_hint == LoopKindHint::WhileLike
            && self
                .loop_candidates_for_header(active_candidate.header)
                .any(|(_, candidate)| {
                    candidate.kind_hint == LoopKindHint::NumericForLike
                        && candidate.preheader.is_some()
                });
        if active_header_has_numeric_for_owner && let Some(else_entry) = else_entry {
            for nested in &self.lowering.structure.loop_candidates {
                let Some(candidate) = nested.preheader else {
                    continue;
                };
                if nested.kind_hint != LoopKindHint::NumericForLike
                    || nested.header == active_candidate.header
                    || !nested.blocks.is_subset(&active_candidate.body_scope_blocks)
                    || !region.structured_blocks.contains(&candidate)
                    || consumed_blocks.contains(&candidate)
                    || candidate == block
                    || candidate == stop
                    || candidate == then_entry
                    || candidate == else_entry
                    || !self.branch_arm_reaches_loop_continuation_or_escape(
                        candidate,
                        stop,
                        loop_context.header,
                    )
                {
                    continue;
                }
                if self.nested_numeric_for_preheader_is_shared_continuation(
                    then_entry, else_entry, candidate, stop,
                ) {
                    return Some(candidate);
                }
            }
        }
        let nested_loop_owned_blocks = self
            .lowering
            .structure
            .loop_candidates
            .iter()
            .filter(|nested| {
                nested.header != loop_context.header
                    && nested.blocks.is_subset(&active_candidate.body_scope_blocks)
            })
            .flat_map(|nested| {
                nested.blocks.iter().copied().filter(|block| {
                    else_entry.is_none()
                        || (*block != nested.header && Some(*block) != nested.preheader)
                })
            })
            .collect::<BTreeSet<_>>();
        let stop_predecessor_has_continue_owner = |from: BlockRef| {
            loop_context.continue_sources.contains(&from)
                || self
                    .branch_candidate_for_header(from)
                    .is_some_and(|branch| {
                        branch.else_entry.is_none()
                            && branch.merge == Some(stop)
                            && self.branch_arm_reaches_target_before_boundary(
                                branch.then_entry,
                                region.merge,
                                stop,
                            )
                    })
        };
        let stop_predecessors_have_expected_owners = || {
            let mut has_continue_owner = false;
            self.lowering.cfg.preds[stop.index()]
                .iter()
                .all(|edge_ref| {
                    let from = self.lowering.cfg.edges[edge_ref.index()].from;
                    let has_owner = stop_predecessor_has_continue_owner(from);
                    has_continue_owner |= has_owner;
                    from == region.merge || has_owner
                })
                && has_continue_owner
        };
        if self.can_emit_continue_stmt()
            && active_candidate.kind_hint == LoopKindHint::RepeatLike
            && else_entry.is_none()
            && region.merge != block
            && region.merge != then_entry
            && region.merge != stop
            && !consumed_blocks.contains(&region.merge)
            && !nested_loop_owned_blocks.contains(&region.merge)
            && (self.lowering.cfg.unique_reachable_successor(region.merge) == Some(stop)
                || self.branch_arm_reaches_loop_continuation_or_escape(
                    region.merge,
                    stop,
                    loop_context.header,
                ))
            && self.branch_arm_reaches_target_or_boundary_or_terminate(
                then_entry,
                region.merge,
                stop,
            )
            && stop_predecessors_have_expected_owners()
        {
            return Some(region.merge);
        }
        let reaches_in_current_iteration = |entry, candidate| {
            active_candidate.kind_hint != LoopKindHint::RepeatLike
                || self.can_reach_avoiding_block(entry, candidate, loop_context.header)
        };
        let implicit_else_entry = else_entry.unwrap_or(region.merge);
        let mut fallback_continuation = None;
        for candidate in region
            .structured_blocks
            .iter()
            .copied()
            .filter(|candidate| *candidate != block)
            .filter(|candidate| !consumed_blocks.contains(candidate))
            .filter(|candidate| *candidate != stop)
            .filter(|candidate| *candidate != then_entry && Some(*candidate) != else_entry)
            .filter(|candidate| !nested_loop_owned_blocks.contains(candidate))
            .filter(|candidate| {
                self.lowering.cfg.unique_reachable_successor(*candidate) == Some(stop)
                    || self.branch_arm_reaches_loop_continuation_or_escape(
                        *candidate,
                        stop,
                        loop_context.header,
                    )
            })
        {
            if reaches_in_current_iteration(then_entry, candidate)
                && self.branch_arm_reaches_loop_continuation_or_escape(then_entry, candidate, stop)
                && (implicit_else_entry == candidate
                    || (reaches_in_current_iteration(implicit_else_entry, candidate)
                        && self.branch_arm_reaches_loop_continuation_or_escape(
                            implicit_else_entry,
                            candidate,
                            stop,
                        )))
            {
                return Some(candidate);
            }
            if fallback_continuation.is_none()
                && let Some(else_entry) = else_entry
                && self
                    .branch_candidate_for_header(candidate)
                    .is_some_and(|branch| branch.merge == Some(stop))
                && self.can_reach_avoiding_block(then_entry, candidate, stop)
                && self.can_reach_avoiding_block(else_entry, candidate, stop)
                && self.branch_arm_reaches_stop_or_loop_escape(then_entry, candidate, stop)
                && self.branch_arm_reaches_stop_or_loop_escape(else_entry, candidate, stop)
            {
                fallback_continuation = Some(candidate);
            }
        }

        // early continue 可以让一条路径跳过 tail；只用 Structure 明确给出
        // `tail branch -> stop` owner 的双臂分支补充常规严格证明。
        let else_entry = else_entry?;
        let continuation = fallback_continuation?;
        self.promoted_early_continue_nested_tail(
            continuation,
            then_entry,
            else_entry,
            stop,
            loop_context,
            active_candidate,
        )
        .or(Some(continuation))
    }

    fn promoted_early_continue_nested_tail(
        &self,
        continuation: BlockRef,
        then_entry: BlockRef,
        else_entry: BlockRef,
        stop: BlockRef,
        loop_context: &ActiveLoopContext,
        active_candidate: &LoopCandidate,
    ) -> Option<BlockRef> {
        let tail_branch = self.branch_candidate_for_header(continuation)?;
        if tail_branch.else_entry.is_some() {
            return None;
        }
        let shared_tail = match self.multi_node_short_circuit_non_continue_exit(
            continuation,
            stop,
            &active_candidate.body_scope_blocks,
        ) {
            Ok(Some(exit)) => exit,
            Ok(None) => tail_branch.then_entry,
            Err(()) => return None,
        };
        let shared_tail = if self
            .nested_loop_owner_for_entry(active_candidate, shared_tail)
            .is_some()
        {
            shared_tail
        } else if self.branch_candidate_for_header(shared_tail).is_none()
            && !self.has_loop_header(shared_tail)
        {
            let successor = self.lowering.cfg.unique_reachable_successor(shared_tail)?;
            self.nested_loop_owner_for_entry(active_candidate, successor)?;
            successor
        } else {
            return None;
        };
        let mut current_iteration = active_candidate.body_scope_blocks.clone();
        current_iteration.remove(&loop_context.header);
        current_iteration.remove(&stop);
        let predecessors = self.lowering.cfg.preds[shared_tail.index()]
            .iter()
            .map(|edge| self.lowering.cfg.edges[edge.index()].from)
            .collect::<BTreeSet<_>>();
        let then_reachable = self
            .lowering
            .cfg
            .reachable_targets_within(then_entry, &current_iteration);
        let else_reachable = self
            .lowering
            .cfg
            .reachable_targets_within(else_entry, &current_iteration);
        let distinct_arm_predecessors =
            has_distinct_arm_predecessors(&predecessors, &then_reachable, &else_reachable);
        (distinct_arm_predecessors
            && self.branch_arm_reaches_target_or_loop_escape_before_boundary(
                then_entry,
                shared_tail,
                Some(loop_context.header),
            )
            && self.branch_arm_reaches_target_or_loop_escape_before_boundary(
                else_entry,
                shared_tail,
                Some(loop_context.header),
            ))
        .then_some(shared_tail)
    }

    fn nested_numeric_for_preheader_is_shared_continuation(
        &self,
        then_entry: BlockRef,
        else_entry: BlockRef,
        candidate: BlockRef,
        continue_target: BlockRef,
    ) -> bool {
        let predecessors = self.lowering.cfg.preds[candidate.index()]
            .iter()
            .map(|edge| self.lowering.cfg.edges[edge.index()].from)
            .collect::<BTreeSet<_>>();
        let mut current_iteration = self.lowering.cfg.reachable_blocks.clone();
        current_iteration.remove(&continue_target);
        let mut then_reachable = self
            .lowering
            .cfg
            .reachable_targets_within(then_entry, &current_iteration);
        let mut else_reachable = self
            .lowering
            .cfg
            .reachable_targets_within(else_entry, &current_iteration);
        then_reachable.remove(&continue_target);
        else_reachable.remove(&continue_target);
        let has_distinct_arm_predecessors =
            has_distinct_arm_predecessors(&predecessors, &then_reachable, &else_reachable);

        has_distinct_arm_predecessors
            && then_reachable.contains(&candidate)
            && else_reachable.contains(&candidate)
            && self.branch_arm_reaches_target_or_loop_escape_before_boundary(
                then_entry, candidate, None,
            )
            && self.branch_arm_reaches_target_or_loop_escape_before_boundary(
                else_entry, candidate, None,
            )
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
                .loop_candidates_for_header(merge)
                .any(|(_, candidate)| candidate.preheader == Some(entry))
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
}

fn has_distinct_arm_predecessors(
    predecessors: &BTreeSet<BlockRef>,
    then_reachable: &BTreeSet<BlockRef>,
    else_reachable: &BTreeSet<BlockRef>,
) -> bool {
    predecessors
        .intersection(then_reachable)
        .next()
        .zip(predecessors.intersection(else_reachable).next())
        .is_some_and(|(then_pred, else_pred)| {
            then_pred != else_pred
                || predecessors.iter().any(|pred| {
                    pred != then_pred
                        && (then_reachable.contains(pred) || else_reachable.contains(pred))
                })
        })
}
