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
        if self.short_circuit_consumed_headers_have_escaping_prefix_defs(&next.consumed_headers) {
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
                for use_site in &self.lowering.dataflow.def_uses[def.index()] {
                    let use_block = self.lowering.cfg.instr_to_block[use_site.instr.index()];
                    if !consumed_headers.contains(&use_block) {
                        return true;
                    }
                }
            }
        }
        false
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
}
