//! 这个文件集中处理普通 branch merge 值在 HIR 里的消费。
//!
//! 这个 pass 只消费 StructureFacts 已经整理好的 branch-arm defs，不再回头拆
//! `phi.incoming`。它负责决定这些 merge 值应该被翻成 entry override、共享 alias，
//! 还是保守物化成 `Decision`。
//!
//! 例子：
//! - `if c then x = a else x = b end` 若两臂都能稳定 inline，会恢复成 entry override
//!   或 `Decision(a, b)`
//! - 如果两臂最终其实都写回同一个 lvalue，则这里会收成共享 alias，而不会再保留一层 phi

use std::collections::BTreeMap;

use crate::cfg::DefId;
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirLValue,
    TempId,
};

use super::rewrites::lvalue_as_expr;
use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
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
            if !value.then_arm.preds.is_disjoint(preds) {
                self.install_branch_arm_target_overrides(
                    &value.then_arm.non_header_defs,
                    &target,
                    &mut overrides,
                );
            }
            if !value.else_arm.preds.is_disjoint(preds) {
                self.install_branch_arm_target_overrides(
                    &value.else_arm.non_header_defs,
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
        let mut shared_target = None;

        for def in branch_value_non_header_defs(value) {
            let temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
            let target = target_overrides.get(&temp)?;
            let _ = lvalue_as_expr(target)?;
            if shared_target
                .as_ref()
                .is_some_and(|known_target: &HirLValue| *known_target != *target)
            {
                return None;
            }
            shared_target = Some(target.clone());
        }

        shared_target
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

    fn install_branch_arm_target_overrides(
        &self,
        defs: &std::collections::BTreeSet<DefId>,
        target: &HirLValue,
        overrides: &mut BTreeMap<TempId, HirLValue>,
    ) {
        for def in defs {
            let Some(def_temp) = self.lowering.bindings.fixed_temps.get(def.index()) else {
                continue;
            };
            overrides.insert(*def_temp, target.clone());
        }
    }
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
