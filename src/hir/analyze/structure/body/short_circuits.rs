//! 这个文件承载 structured body lowering 里的 branch short-circuit plan 构建。
//!
//! Structure 层已经识别出短路候选；本文件只把这些候选转换成
//! `StructuredBranchPlan`，并处理可嵌套短路、透明 jump pad、退化 guard 和被短路吞掉
//! 的 header prefix 重写。它不负责普通 region 遍历，也不生成最终 AST sugar。
//!
//! 输入形状：`A or B` 的多个 branch header 共享 truthy/falsy 出口。
//! 输出形状：`StructuredBranchPlan { cond: A or B, then_entry, else_entry, ... }`。

use std::collections::{BTreeMap, BTreeSet};

use super::super::rewrites::expr_has_temp_ref_in;
use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(in crate::hir::analyze::structure) fn try_build_short_circuit_plan(
        &self,
        header: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<Option<StructuredBranchPlan>> {
        for short in self
            .lowering
            .structure
            .short_circuit_candidates
            .iter()
            .filter(|candidate| candidate.header == header)
        {
            let Some(plan) = build_branch_short_circuit_plan_for_candidate(self.lowering, short)
            else {
                continue;
            };
            if let Some(plan) = self.finish_branch_short_circuit_plan(header, stop, plan)? {
                return Some(Some(plan));
            }
        }
        Some(None)
    }

    fn finish_branch_short_circuit_plan(
        &self,
        header: BlockRef,
        stop: Option<BlockRef>,
        plan: BranchShortCircuitPlan,
    ) -> Option<Option<StructuredBranchPlan>> {
        let BranchShortCircuitPlan {
            mut cond,
            mut truthy,
            mut falsy,
            mut consumed_headers,
        } = plan;
        if self.block_exits_outer_active_loop(truthy) || self.block_exits_outer_active_loop(falsy) {
            return Some(None);
        }
        let continue_break_merge = self.short_circuit_continue_break_merge(truthy, falsy);
        if let Some(stop) = stop
            && continue_break_merge.is_none()
            && self.active_loops.last().is_some_and(|loop_context| {
                loop_context.continue_target == Some(stop)
                    && !self.loop_continue_target_is_empty(stop)
            })
        {
            let body_entry = if truthy == stop { falsy } else { truthy };
            let can_falsy_stop = self.can_short_circuit_to_non_empty_continue(body_entry, stop);
            let preserves_nested_consumed_header = falsy == stop
                && !can_falsy_stop
                && self.plain_branch_fallback_revisits_consumed_header(
                    header,
                    stop,
                    &consumed_headers,
                );
            if truthy == stop && can_falsy_stop {
                cond = cond.negate();
                std::mem::swap(&mut truthy, &mut falsy);
            }
            if truthy == stop
                || consumed_headers.contains(&stop)
                || (falsy == stop && !can_falsy_stop && !preserves_nested_consumed_header)
            {
                return Some(None);
            }
        }

        // 当短路的 truthy 出口是一个退化分支（两条 CFG 边都指向同一个后继 == falsy）时，
        // 该 block 是 `(sc_cond) and guard then end` 中空体守卫的残留。
        // 直接把守卫条件折叠进 SC 条件，避免它作为 body 被 lower_linear_block 丢弃。
        // guard 自带副作用前缀时，后续重写会拒绝吸收，因此回滚点必须位于试探之前。
        let fallback_cond = cond.clone();
        let fallback_truthy = truthy;
        let fallback_falsy = falsy;
        let fallback_consumed_headers = consumed_headers.clone();
        self.absorb_degenerate_guards(&mut cond, &mut truthy, falsy, stop, &mut consumed_headers);
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
        if stop.is_some_and(|stop| consumed_headers.contains(&stop)) {
            return Some(None);
        }
        // 单节点 short-circuit 和普通 branch 在结构信息上是重叠的。
        // 这里如果已经有 plain branch candidate，就优先走普通 branch 恢复：
        // short-circuit 那条 `can_reach(truthy, falsy)` 启发式在 loop 图里会把
        // “经过回边才重新绕到另一臂”的路径也算进去，进而把简单的
        // `if cond then break end` / `if cond then ... end` 误折成错误的 then/merge。
        // 多节点 short-circuit 仍然保留，因为那类结构 plain branch 本来就表达不全。
        if consumed_headers.len() == 1 && self.branch_candidate_for_header(header).is_some() {
            return Some(None);
        }

        if let Some(candidate) = self.branch_candidate_for_header(header)
            && candidate.else_entry.is_none()
            && let Some(merge) = candidate.merge
            && (truthy == merge || falsy == merge)
            && let Some(then_entry) = (truthy == merge)
                .then_some(falsy)
                .or_else(|| (falsy == merge).then_some(truthy))
            && self.short_circuit_preserves_plain_if_then_merge(
                header,
                then_entry,
                merge,
                stop,
                &consumed_headers,
            )
        {
            if truthy == merge {
                cond = cond.negate();
            }
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry,
                else_entry: None,
                merge: Some(merge),
                consumed_headers,
                consumed_blocks,
            }));
        }

        let current_continue_break_merge = self.short_circuit_continue_break_merge(truthy, falsy);
        if continue_break_merge.is_some() || current_continue_break_merge.is_some() {
            let Some(merge) = current_continue_break_merge else {
                return Some(None);
            };
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: Some(falsy),
                merge: Some(merge),
                consumed_headers,
                consumed_blocks,
            }));
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
        // repeat body 的短路失败出口可以是当前 loop 的立即 break，而成功出口继续执行
        // 本轮 body。全图后支配会把 post-loop 误看成自然 fallthrough；这里保留显式
        // else，交给 loop break owner 区分“立即退出”和“先到 condition”。
        if self.active_loops.last().is_some_and(|loop_context| {
            falsy == loop_context.post_loop
                && (loop_context
                    .continue_target
                    .is_some_and(|continue_target| stop == Some(continue_target))
                    || (loop_context.continue_target.is_none()
                        && stop == Some(loop_context.post_loop)))
        }) {
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
        let truthy_flows_to_falsy = self.can_reach(truthy, falsy)
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

        // 当 SC 的 falsy 出口本身是无返回值的隐式 `return`，并且 then 入口能
        // 经由内部控制流到达同一个终结块时（典型形状：then 内部还有 `if X then return end`
        // 的早返回守卫，与 SC 失败路径共用函数尾部的隐式 return），按 IfElse 处理会
        // 让 then 在 lower 时先 visit 掉这个共享终结块，导致随后 lower else 失败、整段
        // proto 退化成 goto-label fallback。这里把这种形状显式降级成 IfThen，merge 留空：
        // 终结块由 then 内部的早返回路径自然消费，SC falsy 边落到外层 region 的自然末尾，
        // 语义上正好对齐 `if cond then ... <early return inside> ... end` 加函数末尾隐式 return。
        // 显式返回值或 return 前缀不能省略，否则 falsy 路径会丢失可见结果或副作用。
        // 如果这条“可达”必须先经过当前 region 的 stop（如 numeric-for 的 FORLOOP latch），
        // 那就是经由下一轮循环绕回来的可达性，不能据此省略当前分支的 terminal else 臂。
        if self.block_is_empty_return(falsy)
            && stop.is_none_or(|stop| self.can_reach_avoiding_block(truthy, falsy, stop))
            && self.can_reach(truthy, falsy)
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

        if let Some(loop_header) = self.active_loops.last().and_then(|loop_context| {
            consumed_headers
                .last()
                .and_then(|header| self.branch_candidate_for_header(*header))
                .and_then(|candidate| candidate.merge)
                .filter(|merge| *merge == loop_context.header)
        }) {
            // 无出口循环没有共同后支配点；Structure 已证明短路链末端的两臂都以
            // 当前 loop header 为本轮合流边界。保留该 merge，branch lowering 会在
            // 两臂自然回到 header 后结束本轮，不会重复降低循环头。
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: Some(falsy),
                merge: Some(loop_header),
                consumed_headers,
                consumed_blocks,
            }));
        }

        // terminal guard 会把全图最近共同后支配点推到函数出口，但同一 header 的
        // branch-value owner 仍可能证明两条非终止路径在本轮先汇入一个局部 continuation。
        // 该 merge 必须留给外层 region 单次消费；否则两条 SC arm 都会降到 loop stop，
        // 后降的 arm 会重入带 phi 的共享 tail，并让完整 proto lowering 失败。
        if let Some(merge) = self.branch_value_shared_continuation(header, truthy, falsy, stop) {
            let consumed_blocks =
                self.branch_short_circuit_consumed_blocks(&consumed_headers, truthy, falsy, stop);
            return Some(Some(StructuredBranchPlan {
                cond,
                then_entry: truthy,
                else_entry: Some(falsy),
                merge: Some(merge),
                consumed_headers,
                consumed_blocks,
            }));
        }

        let Some(merge) = self
            .lowering
            .graph_facts
            .nearest_common_postdom(truthy, falsy)
        else {
            return Some(None);
        };

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

    fn branch_value_shared_continuation(
        &self,
        header: BlockRef,
        truthy: BlockRef,
        falsy: BlockRef,
        stop: Option<BlockRef>,
    ) -> Option<BlockRef> {
        let merge = self.branch_value_merge_for_header(header)?.merge;
        if Some(merge) == stop || merge == truthy || merge == falsy {
            return None;
        }
        let boundary = stop.unwrap_or(self.lowering.cfg.exit_block);
        (self.branch_arm_reaches_shared_continuation_or_terminate(truthy, merge, boundary)
            && self.branch_arm_reaches_shared_continuation_or_terminate(falsy, merge, boundary))
        .then_some(merge)
    }

    fn short_circuit_preserves_plain_if_then_merge(
        &self,
        header: BlockRef,
        then_entry: BlockRef,
        merge: BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &[BlockRef],
    ) -> bool {
        let Some(loop_context) = self.active_loops.last() else {
            return false;
        };
        let Some(continue_target) = loop_context.continue_target else {
            return false;
        };
        let tail_keeps_merge = consumed_headers
            .last()
            .and_then(|header| self.branch_candidate_for_header(*header))
            .is_some_and(|candidate| {
                candidate.else_entry.is_none() && candidate.merge == Some(merge)
            });
        (continue_target == then_entry && self.block_prefix_has_non_condition_effects(then_entry))
            || (tail_keeps_merge
                && stop == Some(continue_target)
                && then_entry != continue_target
                && self.can_reach_avoiding_block(then_entry, merge, continue_target)
                && self.can_reach_avoiding_block(merge, continue_target, header))
    }

    fn plain_branch_fallback_revisits_consumed_header(
        &self,
        header: BlockRef,
        stop: BlockRef,
        consumed_headers: &[BlockRef],
    ) -> bool {
        if consumed_headers.len() <= 1 {
            return false;
        }
        let Some(candidate) = self.branch_candidate_for_header(header) else {
            return false;
        };
        if candidate.merge != Some(stop) {
            return false;
        }
        let Some(else_entry) = candidate.else_entry else {
            return false;
        };
        let nested_headers = &consumed_headers[1..];
        // 非空 continue target 上，若回退到 plain if/else 会先消费一条 direct arm
        // header，再从另一臂重新进入同一个 consumed header，而该 header 仍是 branch
        // owner，则 `visited` 只能把整片 region 打回失败。这里仅保留这种已证明的
        // “当前 SC owner 是唯一完整覆盖” 形状，不放宽到更深层的模糊可达性。
        let direct_arm_revisited = |entry: BlockRef, sibling: BlockRef| {
            nested_headers.contains(&entry)
                && self.branch_candidate_for_header(entry).is_some()
                && self.can_reach_avoiding_block(sibling, entry, stop)
        };
        direct_arm_revisited(candidate.then_entry, else_entry)
            || direct_arm_revisited(else_entry, candidate.then_entry)
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
            || self.branch_candidate_for_header(block).is_some()
            || self.has_loop_header(block)
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
        let Some(next) =
            self.nestable_branch_short_circuit_plan(*truthy, *falsy, stop, consumed_headers)
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
        let Some(next) =
            self.nestable_branch_short_circuit_plan(*falsy, *truthy, stop, consumed_headers)
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
        sibling_exit: BlockRef,
        stop: Option<BlockRef>,
        consumed_headers: &[BlockRef],
    ) -> Option<BranchShortCircuitPlan> {
        if Some(header) == stop
            || self.block_is_active_loop_control_header(header)
            || consumed_headers.contains(&header)
        {
            return None;
        }
        if self.has_loop_header(header) {
            return None;
        }
        let plan_is_nestable = |next: &BranchShortCircuitPlan| {
            !next
                .consumed_headers
                .iter()
                .any(|header| Some(*header) == stop || consumed_headers.contains(header))
                && !self.short_circuit_consumed_headers_have_escaping_prefix_defs(
                    &next.consumed_headers,
                )
        };
        // 候选顺序只保证稳定，不代表出口优先级；错出口不能遮蔽后续同 header 候选。
        let plan_matches_sibling = |next: &BranchShortCircuitPlan| {
            next.truthy == sibling_exit || next.falsy == sibling_exit
        };
        for plan in self
            .lowering
            .structure
            .short_circuit_candidates
            .iter()
            .filter(|candidate| candidate.header == header)
            .filter_map(|short| build_branch_short_circuit_plan_for_candidate(self.lowering, short))
        {
            if plan_matches_sibling(&plan) && plan_is_nestable(&plan) {
                return Some(plan);
            }
        }
        self.nestable_plain_branch_plan(header)
            .filter(plan_matches_sibling)
            .filter(plan_is_nestable)
    }

    fn block_is_active_loop_control_header(&self, header: BlockRef) -> bool {
        self.active_loops.last().is_some_and(|loop_context| {
            loop_context.continue_target == Some(header)
                || self
                    .branch_candidate_for_header(header)
                    .is_some_and(|branch| {
                        // one-arm guard 才能用“显式臂回环、缺席臂退出”证明自身就是
                        // loop control；双臂分支还可能是更宽短路条件的末端节点。
                        branch.else_entry.is_none()
                            && branch.merge == Some(loop_context.post_loop)
                            && self.can_reach_avoiding_block(
                                branch.then_entry,
                                loop_context.header,
                                loop_context.post_loop,
                            )
                    })
        })
    }

    fn short_circuit_continue_break_merge(
        &self,
        truthy: BlockRef,
        falsy: BlockRef,
    ) -> Option<BlockRef> {
        let loop_context = self.active_loops.last()?;
        let continue_target = loop_context.continue_target?;
        ((truthy == continue_target && falsy == loop_context.post_loop)
            || (falsy == continue_target && truthy == loop_context.post_loop))
            .then_some(loop_context.post_loop)
    }

    pub(super) fn multi_node_short_circuit_non_continue_exit(
        &self,
        header: BlockRef,
        continue_target: BlockRef,
        active_blocks: &BTreeSet<BlockRef>,
    ) -> Result<Option<BlockRef>, ()> {
        let mut non_continue = None;
        for short in &self.lowering.structure.short_circuit_candidates {
            if short.header != header || !short.reducible || short.nodes.len() <= 1 {
                continue;
            }
            let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
                continue;
            };
            let exit = match (truthy == continue_target, falsy == continue_target) {
                (true, false) => falsy,
                (false, true) => truthy,
                (false, false) => continue,
                (true, true) => return Err(()),
            };
            if short.blocks.contains(&continue_target)
                || !short.blocks.is_subset(active_blocks)
                || non_continue.is_some_and(|known| known != exit)
            {
                return Err(());
            }
            non_continue = Some(exit);
        }
        Ok(non_continue)
    }

    // 普通 branch 只有在作为短路链的下一个出口时才被临时当作两出口计划。
    // 真正消费前还会由 rewrite_short_circuit_skipped_header_prefixes 校验其 prefix
    // 能否安全内联进条件，避免把带副作用或不可表达的前置语句静默吞掉。
    fn nestable_plain_branch_plan(&self, header: BlockRef) -> Option<BranchShortCircuitPlan> {
        let candidate = self.branch_candidate_for_header(header)?;
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

    pub(in crate::hir::analyze::structure) fn rewrite_short_circuit_skipped_header_prefixes(
        &self,
        header: BlockRef,
        consumed_headers: &[BlockRef],
        cond: &mut HirExpr,
    ) -> bool {
        let target_overrides = BTreeMap::new();
        let mut expr_overrides = BTreeMap::new();
        let mut unresolved_prefix_temps = BTreeSet::new();
        for consumed in consumed_headers
            .iter()
            .copied()
            .filter(|consumed| *consumed != header)
        {
            if self.block_prefix_has_non_condition_effects(consumed) {
                return false;
            }
            let Some(prefix) = self.lower_block_prefix(consumed, true, &target_overrides) else {
                return false;
            };
            if prefix.is_empty() {
                continue;
            }

            let (block_overrides, all_prefix_temps) =
                self.block_prefix_temp_expr_overrides(consumed);
            for stmt in prefix {
                let HirStmt::Assign(assign) = stmt else {
                    return false;
                };
                if assign.targets.len() != assign.values.expr_len() {
                    return false;
                }
                for target in assign.targets {
                    let HirLValue::Temp(temp) = target else {
                        return false;
                    };
                    unresolved_prefix_temps.insert(temp);
                }
            }
            unresolved_prefix_temps.extend(all_prefix_temps);
            for temp in block_overrides.keys() {
                unresolved_prefix_temps.remove(temp);
            }
            expr_overrides.extend(block_overrides);
        }

        rewrite_expr_temps(cond, &expr_overrides);
        !expr_has_temp_ref_in(cond, &unresolved_prefix_temps)
    }

    fn short_circuit_consumed_headers_have_escaping_prefix_defs(
        &self,
        consumed_headers: &[BlockRef],
    ) -> bool {
        let consumed_headers = consumed_headers.iter().copied().collect::<BTreeSet<_>>();
        consumed_headers.iter().copied().any(|header| {
            self.short_circuit_consumed_header_has_escaping_prefix_defs(header, &consumed_headers)
        })
    }

    fn short_circuit_consumed_header_has_escaping_prefix_defs(
        &self,
        header: BlockRef,
        consumed_headers: &BTreeSet<BlockRef>,
    ) -> bool {
        let Some(prefix_indices) = self.block_prefix_instr_indices(header, false) else {
            return false;
        };
        for instr_index in prefix_indices {
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                if self.lowering.dataflow.def_has_use_outside(
                    self.lowering.cfg,
                    *def,
                    consumed_headers,
                ) {
                    return true;
                }
            }
        }
        false
    }

    fn can_short_circuit_to_non_empty_continue(
        &self,
        body_entry: BlockRef,
        continue_target: BlockRef,
    ) -> bool {
        let Some(loop_context) = self.active_loops.last() else {
            return false;
        };
        let Some(candidate) = self.loop_candidate(loop_context.candidate_id) else {
            return false;
        };
        if matches!(
            candidate.kind_hint,
            LoopKindHint::GenericForLike | LoopKindHint::Unknown
        ) {
            return true;
        }

        // repeat 的 continue target 同时承载循环条件，不能把任意短路出口当成
        // “自然继续”。另一臂的所有路径都必须在本轮回到条件块或退出 active repeat；
        // 不能依赖 nested loop 的形状，因为优化器可能已经把固定轮数循环完全展开。
        // for/repeat 的源码 body 可能先经过普通 branch prefix，再进入没有独立
        // preheader 的 nested loop；natural core 不包含这些提前退出路径。
        let body_has_loop_owner = candidate.body_scope_blocks.contains(&body_entry);
        candidate.kind_hint == LoopKindHint::RepeatLike
            && body_has_loop_owner
            && self.branch_arm_reaches_stop_or_loop_escape(
                body_entry,
                continue_target,
                loop_context.post_loop,
            )
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
}
