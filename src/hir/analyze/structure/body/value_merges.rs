//! 这个文件承载 structured body lowering 里的 short-circuit value merge 专项恢复。
//!
//! 普通 branch lowering 负责把 `BranchCandidate` 降成 `if/else`。本文件只处理
//! SC (ShortCircuit) 值合流在 HIR 层可以直接收敛的几条快捷路径：条件重赋值、
//! statement value-merge、以及纯 value-merge 跳过分支块。它消费 StructureFacts 中
//! 已经识别出的 short-circuit / BranchValueMerge 候选，不重新推断 CFG 语义。
//!
//! 当一个 header 同时拥有 SC 值合流候选和 BranchValueMerge 候选时，SC 只处理一个
//! result_reg 的 phi，而 BVM 认领其余 phi。这里的策略是：
//! - value_merge / conditional_reassign 路径遇到额外 BVM phi 时退让给普通分支；
//! - statement_value_merge 路径只在 SC 独占该合流时使用；同一区域已有 BVM 时交给
//!   普通分支路径统一写回，避免 SC 先消费一部分 phi 后让 BVM 的剩余输出失去同一
//!   条分支里的槽位上下文。
//!
//! 输入形状：SC 覆盖 r4 → `x and (y and 2 or 3) or 6`，BVM 覆盖 r3。
//! 输出形状：普通分支路径在同一 `if` 中同时写回 r3/r4，不把两个 phi 拆成独立结构。

use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::hir::analyze::short_circuit::{
    DecisionEdge, build_decision_expr, same_value_merge_shape,
};
use crate::structure::DefId;

type StatementValueMergeOutput<'c> = (&'c ShortCircuitCandidate, HirLValue);

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn try_lower_conditional_reassign_branch(
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

        if short
            .value_incomings
            .iter()
            .any(|incoming| incoming.latest_local_def.is_none())
        {
            return None;
        }

        // 与 try_lower_value_merge_branch 同理：SC 系列快捷路径只处理一个
        // result_reg，BVM 认领的其他 phi 会因分支结构被消费而孤立。
        if let Some(bvm) = self.branch_value_merge_for_header(block)
            && bvm
                .values
                .iter()
                .any(|v| Some(v.phi_id) != short.result_phi_id)
        {
            return None;
        }

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }

        // try_lower_statement_value_merge_branch 处的同类守卫：条件重赋值同样把
        // phi temp 直接内联进语句，跳过了 apply_loop_rewrites，当 entry value
        // 被 loop state 接管时，写入会被遗漏。
        if value_merge_defs_are_overridden(self.lowering, short, target_overrides) {
            return None;
        }
        if self.statement_value_merge_would_duplicate_nontrivial_leaf(short, target_overrides) {
            return None;
        }

        let mut plan = build_conditional_reassign_plan(self.lowering, block)?;
        if merge_has_other_live_phi(self.lowering, plan.merge, plan.phi_id) {
            return None;
        }
        self.rewrite_value_merge_entry_exprs(short, &mut plan.init_value);
        self.rewrite_value_merge_entry_exprs(short, &mut plan.cond);
        self.rewrite_value_merge_entry_exprs(short, &mut plan.assigned_value);

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

    pub(super) fn try_lower_statement_value_merge_branch(
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
        let would_duplicate_nontrivial_leaf =
            self.statement_value_merge_would_duplicate_nontrivial_leaf(short, target_overrides);
        let can_defer_to_branch_value_merge =
            self.statement_value_merge_can_defer_to_branch_value_merge(short);
        if can_defer_to_branch_value_merge {
            return None;
        }
        let should_use_statement_value_merge = would_duplicate_nontrivial_leaf;
        if recover_short_value_merge_expr_with_allowed_blocks(self.lowering, short, &allowed_blocks)
            .is_some()
            && !should_use_statement_value_merge
        {
            return None;
        }

        if let Some(stop) = stop
            && stop != merge
            && short.blocks.contains(&stop)
        {
            return None;
        }
        let outputs = self.statement_value_merge_outputs(short, target_overrides)?;
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
        if let Some(bvm) = self.branch_value_merge_for_header(block) {
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
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<Vec<StatementValueMergeOutput<'b>>> {
        let mut outputs = Vec::new();
        for candidate in &self.lowering.structure.short_circuit_candidates {
            if !same_statement_value_merge_tree(short, candidate) {
                continue;
            }
            let phi_id = candidate.result_phi_id?;
            let temp = *self.lowering.bindings.phi_temps.get(phi_id.index())?;
            let target = target_overrides
                .get(&temp)
                .cloned()
                .unwrap_or(HirLValue::Temp(temp));
            outputs.push((candidate, target));
        }
        (!outputs.is_empty()).then_some(outputs)
    }

    fn statement_value_merge_would_duplicate_nontrivial_leaf(
        &self,
        short: &ShortCircuitCandidate,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> bool {
        let mut leaf_counts = BTreeMap::<BlockRef, usize>::new();
        for node in &short.nodes {
            for target in [&node.truthy, &node.falsy] {
                if let ShortCircuitTarget::Value(block) = target {
                    *leaf_counts.entry(*block).or_default() += 1;
                }
            }
        }

        leaf_counts
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .any(|(block, _)| {
                self.lower_block_prefix(block, false, target_overrides)
                    .is_none_or(|stmts| !value_merge_leaf_is_simple_clone(&stmts))
            })
    }

    fn statement_value_merge_can_defer_to_branch_value_merge(
        &self,
        short: &ShortCircuitCandidate,
    ) -> bool {
        let Some(result_phi_id) = short.result_phi_id else {
            return false;
        };

        short.nodes.iter().any(|node| {
            self.branch_value_merge_for_header(node.header)
                .is_some_and(|bvm| {
                    bvm.values.len() > 1
                        && bvm.values.iter().any(|value| value.phi_id == result_phi_id)
                })
        })
    }

    pub(super) fn try_lower_value_merge_branch(
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
        if let Some(bvm) = self.branch_value_merge_for_header(block)
            && bvm
                .values
                .iter()
                .any(|v| Some(v.phi_id) != short.result_phi_id)
        {
            return None;
        }

        // 该快捷路径只消费分支块并等待 merge phi 稍后物化；若叶子 def 已由 loop
        // state 接管，merge phi 会被抑制，必须退回普通分支让两臂直接写入 owner。
        if value_merge_defs_are_overridden(self.lowering, short, target_overrides) {
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
        self.merge_allowed_blocks.insert(merge, block);
        Some(Some(merge))
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
        self.rewrite_expr_at_block_entry(node.header, &mut cond);
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

    pub(super) fn branch_entry_target_overrides(
        &self,
        header: BlockRef,
        entry: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let Some(entry) = entry else {
            return target_overrides.clone();
        };
        let Some(candidate) = self.branch_candidate_for_header(header) else {
            return target_overrides.clone();
        };
        let Some(value_merge) = self.branch_value_merge_for_header(header) else {
            return target_overrides.clone();
        };

        if entry == candidate.then_entry {
            return self.branch_value_then_target_overrides(value_merge, target_overrides);
        }
        if Some(entry) == candidate.else_entry {
            return self.branch_value_else_target_overrides(value_merge, target_overrides);
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
        for (short, target) in outputs {
            let mut value = if block == current_header
                && header_subject_is_value_carrier(self.lowering, current_header, short.result_reg)
            {
                // 只有直接测试 result_reg 的 truthiness 时，subject 才是当前 leaf 值。
                // 其它寄存器的 guard 只是在控制是否保留旧值，不能把 guard 本身当作结果。
                lower_short_circuit_subject(self.lowering, block)?
            } else {
                lower_materialized_value_leaf_expr(self.lowering, short, block)?
            };
            self.rewrite_expr_at_block_entry(block, &mut value);
            let mut stmt = assign_stmt(vec![target.clone()], vec![value]);
            apply_loop_rewrites(std::slice::from_mut(&mut stmt), target_overrides);
            if let HirStmt::Assign(assign) = &stmt
                && assign.targets.len() == 1
                && assign.values.expr_len() == 1
                && assign.values.tail.is_none()
                && lvalue_as_expr(&assign.targets[0]).as_ref() == assign.values.fixed.first()
            {
                continue;
            }
            stmts.push(stmt);
        }

        Some(HirBlock { stmts })
    }

    fn rewrite_value_merge_entry_exprs(&self, short: &ShortCircuitCandidate, expr: &mut HirExpr) {
        let blocks = short
            .nodes
            .iter()
            .map(|node| node.header)
            .chain(short.value_incomings.iter().map(|incoming| incoming.pred))
            .collect::<BTreeSet<_>>();
        for block in blocks {
            self.rewrite_expr_at_block_entry(block, expr);
        }
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
        let decision = build_decision_expr(
            self.lowering,
            short,
            short.entry,
            lower_short_circuit_subject,
            |_, target| match target {
                ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
                ShortCircuitTarget::Value(block) => Some(DecisionEdge::Leaf(
                    HirDecisionTarget::Expr(expr_for_reg_at_block_exit(self.lowering, *block, reg)),
                )),
                ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
            },
        )?;
        Some(HirExpr::Decision(Box::new(decision)))
    }

    pub(super) fn install_stop_boundary_value_merge_override(
        &mut self,
        header: BlockRef,
        branch_stop: Option<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        let Some(merge) = branch_stop else {
            return;
        };
        self.install_proven_target_phi_overrides(merge, target_overrides);
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

    pub(super) fn install_proven_target_phi_overrides(
        &mut self,
        merge: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        if target_overrides.is_empty() {
            return;
        }
        let replacements = self
            .lowering
            .dataflow
            .phi_candidates_in_block(merge)
            .iter()
            .filter(|phi| !self.overrides.phi_is_suppressed_for_block(merge, phi.id))
            .filter_map(|phi| {
                let defs = || {
                    phi.incoming
                        .iter()
                        .flat_map(|incoming| self.lowering.dataflow.leaf_defs(incoming.value))
                };
                let target = shared_lvalue_for_defs(
                    &self.lowering.bindings.fixed_temps,
                    defs(),
                    target_overrides,
                )
                .or_else(|| {
                    let target = self.active_loop_state_target(phi.reg)?;
                    defs()
                        .all(|def| {
                            let temp = self.lowering.bindings.fixed_temps[def.index()];
                            target_overrides
                                .get(&temp)
                                .cloned()
                                .unwrap_or(HirLValue::Temp(temp))
                                == target
                        })
                        .then_some(target)
                })?;
                Some((phi.id, phi.reg, lvalue_as_expr(&target)?))
            })
            .collect::<Vec<_>>();
        for (phi_id, reg, expr) in replacements {
            self.replace_phi_with_entry_expr(merge, phi_id, reg, expr);
        }
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
    short
        .entry_value
        .into_iter()
        .flat_map(|value| lowering.dataflow.leaf_defs(value))
        .any(|def| is_overridden(&def))
        || short
            .value_incomings
            .iter()
            .flat_map(|incoming| lowering.dataflow.leaf_defs(incoming.value))
            .any(|def| is_overridden(&def))
}

fn merge_has_other_live_phi(
    lowering: &ProtoLowering<'_>,
    merge: BlockRef,
    consumed_phi_id: PhiId,
) -> bool {
    lowering
        .dataflow
        .phi_candidates_in_block(merge)
        .iter()
        .any(|phi| phi.id != consumed_phi_id && !lowering.structure.phi_is_dead(phi.id))
}

fn same_statement_value_merge_tree(
    base: &ShortCircuitCandidate,
    candidate: &ShortCircuitCandidate,
) -> bool {
    base.reducible
        && candidate.reducible
        && base.result_phi_id.is_some()
        && candidate.result_phi_id.is_some()
        && base.result_reg.is_some()
        && candidate.result_reg.is_some()
        && same_value_merge_shape(base, candidate)
}

fn value_merge_leaf_is_simple_clone(stmts: &[HirStmt]) -> bool {
    let [stmt] = stmts else {
        return stmts.is_empty();
    };
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    assign
        .values
        .iter()
        .all(value_merge_leaf_expr_is_simple_clone)
}

fn value_merge_leaf_expr_is_simple_clone(expr: &HirExpr) -> bool {
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
        HirExpr::Unary(unary) => value_merge_leaf_expr_is_simple_clone(&unary.expr),
        HirExpr::Binary(binary) => {
            value_merge_leaf_expr_is_simple_clone(&binary.lhs)
                && value_merge_leaf_expr_is_simple_clone(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            value_merge_leaf_expr_is_simple_clone(&logical.lhs)
                && value_merge_leaf_expr_is_simple_clone(&logical.rhs)
        }
        HirExpr::TableAccess(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. } => false,
    }
}
