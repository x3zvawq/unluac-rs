//! 这个文件集中处理普通 branch merge 值在 HIR 里的消费。
//!
//! 这个 pass 只消费 StructureFacts 已经整理好的 branch-arm defs，不再回头拆
//! `phi.incoming`。它负责决定这些 merge 值应该被翻成 entry override、共享 alias，
//! 还是保守物化成 `Decision`；如果某一臂只是“沿用当前值”，也会在普通 branch
//! lowering 里补上必要的 entry seed，避免把 preserved arm 错降成“未初始化”。
//!
//! 例子：
//! - `if c then x = a else x = b end` 若两臂都能稳定 inline，会恢复成 entry override
//!   或 `Decision(a, b)`
//! - 如果两臂最终其实都写回同一个 lvalue，则这里会收成共享 alias，而不会再保留一层 phi

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::DefId;
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirLValue,
    TempId,
};

use super::rewrites::lvalue_as_expr;
use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn branch_value_preserved_entry_stmts(
        &self,
        header: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Vec<HirStmt> {
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return Vec::new();
        };

        let mut targets = Vec::new();
        let mut values = Vec::new();

        for value in &candidate.values {
            if !branch_value_needs_preserved_entry_seed(value) {
                continue;
            }

            let target = self.branch_value_arm_target(value, target_overrides);
            let init = self.branch_value_preserved_entry_expr(header, value.reg, target_overrides);
            if lvalue_as_expr(&target)
                .as_ref()
                .is_some_and(|target_expr| *target_expr == init)
            {
                continue;
            }

            targets.push(target);
            values.push(init);
        }

        if targets.is_empty() {
            Vec::new()
        } else {
            vec![assign_stmt(targets, values)]
        }
    }

    fn branch_value_arm_target(
        &self,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> HirLValue {
        let phi_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
        if let Some(target) = target_overrides.get(&phi_temp) {
            return target.clone();
        }
        if let Some(target) = self.shared_branch_target_lvalue(value, target_overrides) {
            return target;
        }

        HirLValue::Temp(phi_temp)
    }

    fn branch_value_target_overrides_for_preds(
        &self,
        header: BlockRef,
        preds: &std::collections::BTreeSet<BlockRef>,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let mut overrides = target_overrides.clone();
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return overrides;
        };

        for value in &candidate.values {
            let target = self.branch_value_arm_target(value, target_overrides);
            let mut arm_defs = BTreeSet::new();
            if !value.then_arm.preds.is_disjoint(preds) {
                arm_defs.extend(value.then_arm.non_header_defs.iter().copied());
                install_def_target_overrides(
                    &self.lowering.bindings.fixed_temps,
                    value.then_arm.non_header_defs.iter().copied(),
                    &target,
                    &mut overrides,
                );
            }
            if !value.else_arm.preds.is_disjoint(preds) {
                arm_defs.extend(value.else_arm.non_header_defs.iter().copied());
                install_def_target_overrides(
                    &self.lowering.bindings.fixed_temps,
                    value.else_arm.non_header_defs.iter().copied(),
                    &target,
                    &mut overrides,
                );
            }
            // 当 BVM 的 arm defs 中有一部分被内层短路候选吸收时，短路产出的 phi temp
            // 是这些 defs 在 HIR 层面的唯一代表——原始 def 的 fixed_temp 不再出现在
            // 赋值语句中。此时外层 BVM 的 target override 必须覆盖到这个 phi temp，
            // 否则内层短路的物化结果会写入一个"无人读取"的 temp 而丢失。
            if !arm_defs.is_empty() {
                install_short_circuit_phi_overrides(
                    self.lowering,
                    header,
                    &arm_defs,
                    &target,
                    &mut overrides,
                );
            }
        }

        overrides
    }

    pub(super) fn branch_value_then_target_overrides(
        &self,
        header: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return target_overrides.clone();
        };

        let mut preds = BTreeSet::new();
        for value in &candidate.values {
            preds.extend(value.then_arm.preds.iter().copied());
        }

        self.branch_value_target_overrides_for_preds(header, &preds, target_overrides)
    }

    pub(super) fn branch_value_else_target_overrides(
        &self,
        header: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return target_overrides.clone();
        };

        let mut preds = BTreeSet::new();
        for value in &candidate.values {
            preds.extend(value.else_arm.preds.iter().copied());
        }

        self.branch_value_target_overrides_for_preds(header, &preds, target_overrides)
    }

    pub(super) fn branch_value_target_overrides(
        &self,
        header: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> BTreeMap<TempId, HirLValue> {
        let mut overrides = self.branch_value_then_target_overrides(header, target_overrides);
        overrides.extend(self.branch_value_else_target_overrides(header, target_overrides));
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return overrides;
        };

        for value in &candidate.values {
            let Some(shared_target) = self.shared_branch_target_lvalue(value, target_overrides)
            else {
                continue;
            };
            let phi_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
            overrides.insert(phi_temp, shared_target);
        }
        overrides
    }

    pub(super) fn install_branch_value_merge_overrides(
        &mut self,
        header: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) {
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return;
        };

        for value in &candidate.values {
            let Some(override_value) =
                self.branch_value_override_expr(header, value, target_overrides)
            else {
                continue;
            };

            match override_value {
                BranchValueOverride::Alias(expr) => {
                    self.replace_phi_with_entry_expr(candidate.merge, value.phi_id, value.reg, expr)
                }
                BranchValueOverride::Snapshot(expr) => self
                    .replace_phi_with_entry_expr_if_local_use(
                        candidate.merge,
                        value.phi_id,
                        value.reg,
                        expr,
                    ),
            }
        }
    }

    fn branch_value_override_expr(
        &self,
        header: BlockRef,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<BranchValueOverride> {
        self.shared_branch_target_expr(value, target_overrides)
            .map(BranchValueOverride::Alias)
            .or_else(|| {
                self.branch_value_decision_expr(header, value, target_overrides)
                    .map(BranchValueOverride::Snapshot)
            })
    }

    fn shared_branch_target_lvalue(
        &self,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirLValue> {
        shared_lvalue_for_defs(
            &self.lowering.bindings.fixed_temps,
            branch_value_non_header_defs(value),
            target_overrides,
        )
    }

    fn shared_branch_target_expr(
        &self,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        shared_expr_for_defs(
            &self.lowering.bindings.fixed_temps,
            branch_value_non_header_defs(value),
            target_overrides,
        )
    }

    fn branch_value_decision_expr(
        &self,
        header: BlockRef,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let candidate = *self.branch_by_header.get(&header)?;
        let mut cond = self.lower_candidate_cond(header, candidate)?;
        let mut then_expr = self.uniform_dup_safe_arm_expr(&value.then_arm)?;
        let mut else_expr = self.uniform_dup_safe_arm_expr(&value.else_arm)?;
        let expr_overrides = temp_expr_overrides(target_overrides);
        rewrite_expr_temps(&mut cond, &expr_overrides);
        rewrite_expr_temps(&mut then_expr, &expr_overrides);
        rewrite_expr_temps(&mut else_expr, &expr_overrides);

        if then_expr == else_expr {
            return Some(then_expr);
        }

        Some(HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: cond,
                truthy: HirDecisionTarget::Expr(then_expr),
                falsy: HirDecisionTarget::Expr(else_expr),
            }],
        })))
    }

    fn branch_value_preserved_entry_expr(
        &self,
        header: BlockRef,
        reg: Reg,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> HirExpr {
        // 某一臂只是在“沿用进入分支前的当前值”时，shared target 需要先吃到一份 seed；
        // 否则后面只改写“写新值”的那一臂，merge 后继续读取的状态槽位就会悬空成 nil。
        if !self.block_redefines_reg(header, reg)
            && let Some(expr) = self.overrides.carried_entry_expr(header, reg)
        {
            return expr.clone();
        }

        let mut expr = expr_for_reg_at_block_exit(self.lowering, header, reg);
        rewrite_expr_temps(&mut expr, &temp_expr_overrides(target_overrides));
        expr
    }

    fn uniform_dup_safe_arm_expr(&self, arm: &BranchValueMergeArm) -> Option<HirExpr> {
        let mut arm_expr = None;

        for def in &arm.defs {
            let expr = expr_for_dup_safe_fixed_def(self.lowering, *def)?;
            if arm_expr
                .as_ref()
                .is_some_and(|known_expr: &HirExpr| *known_expr != expr)
            {
                return None;
            }
            arm_expr = Some(expr);
        }

        arm_expr
    }
}

fn branch_value_needs_preserved_entry_seed(value: &BranchValueMergeValue) -> bool {
    (branch_value_arm_preserves_current(&value.then_arm)
        && !value.else_arm.non_header_defs.is_empty())
        || (branch_value_arm_preserves_current(&value.else_arm)
            && !value.then_arm.non_header_defs.is_empty())
}

fn branch_value_arm_preserves_current(arm: &BranchValueMergeArm) -> bool {
    arm.non_header_defs.is_empty()
}

fn branch_value_non_header_defs(value: &BranchValueMergeValue) -> impl Iterator<Item = DefId> + '_ {
    value
        .then_arm
        .non_header_defs
        .iter()
        .copied()
        .chain(value.else_arm.non_header_defs.iter().copied())
}

enum BranchValueOverride {
    Alias(HirExpr),
    Snapshot(HirExpr),
}

/// 当外层 BVM 的 arm defs 被内层短路候选吸收后，短路的 phi temp 是这些 defs
/// 在 HIR 层面的唯一写入点。如果外层 BVM 的 target override 没有覆盖到这个
/// phi temp，物化结果就会写入一个"无人读取"的孤儿 temp，后续被 dead_temps 清除
/// 导致值丢失。
///
/// 这里检查所有 value-merge 型短路候选：只要其 value_incoming defs 与当前 BVM arm
/// 的 defs 有交集 **且** 短路的 header 被 BVM 的 header 严格支配（即短路确实嵌套
/// 在 BVM 的分支体内部），就把该短路的 phi temp 也加入 override 映射。不做支配检查
/// 会误伤那些"只是与 BVM 共享相同 reaching defs 但结构上位于 BVM 之前"的短路，
/// 导致其 phi temp 被错误重定向。
fn install_short_circuit_phi_overrides(
    lowering: &ProtoLowering<'_>,
    bvm_header: BlockRef,
    arm_defs: &BTreeSet<DefId>,
    target: &HirLValue,
    overrides: &mut BTreeMap<TempId, HirLValue>,
) {
    let dom_tree = &lowering.graph_facts.dominator_tree;
    for short in &lowering.structure.short_circuit_candidates {
        if !short.reducible {
            continue;
        }
        let ShortCircuitExit::ValueMerge(_) = short.exit else {
            continue;
        };
        let Some(phi_id) = short.result_phi_id else {
            continue;
        };
        // 短路必须嵌套在 BVM 的分支体内部——其 header 应被 BVM header 严格支配。
        // 如果不做这个检查，位于 BVM 之前（上游）且共享相同 reaching defs 的短路
        // 会被误匹配，其 phi temp 会被错误重定向到 BVM 的 target。
        if short.header == bvm_header || !dom_tree.dominates(bvm_header, short.header) {
            continue;
        }
        let has_overlap = short
            .value_incomings
            .iter()
            .any(|vi| vi.defs.iter().any(|d| arm_defs.contains(d)));
        if !has_overlap {
            continue;
        }
        let Some(phi_temp) = lowering.bindings.phi_temps.get(phi_id.index()).copied() else {
            continue;
        };
        overrides.insert(phi_temp, target.clone());
    }
}
