//! 这个文件集中处理普通 branch merge 值在 HIR 里的消费。
//!
//! `StructureFacts` 已经把“哪个 phi 属于哪个结构化 if/else”的关系显式化了，这里
//! 只负责把这些候选翻成 HIR 入口覆盖或稳定物化。这样剩下的 `temp inline / decision`
//! 简化仍然只是后处理，而不是让 HIR 再去偷偷重算 branch+phi 关系。

use std::collections::BTreeMap;

use crate::cfg::{PhiCandidate, PhiId, SsaValue};
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirLValue,
    TempId,
};

use super::rewrites::lvalue_as_expr;
use super::*;

impl<'a, 'b> StructuredBodyLowerer<'a, 'b> {
    pub(super) fn branch_value_needs_arm_target_overrides(&self, header: BlockRef) -> bool {
        let Some(candidate) = self.branch_value_merges_by_header.get(&header).copied() else {
            return false;
        };
        let Some(branch) = self.branch_by_header.get(&header).copied() else {
            return false;
        };
        let Some(else_entry) = branch.else_entry else {
            return false;
        };

        candidate.values.iter().any(|value| {
            value.then_preds.len() != 1
                || value.else_preds.len() != 1
                || !value.then_preds.contains(&branch.then_entry)
                || !value.else_preds.contains(&else_entry)
        })
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
            let Some(phi) = self
                .lowering
                .dataflow
                .phi_candidates
                .get(value.phi_id.index())
            else {
                continue;
            };
            let phi_temp = self.lowering.bindings.phi_temps[value.phi_id.index()];
            let target = target_overrides
                .get(&phi_temp)
                .cloned()
                .unwrap_or(HirLValue::Temp(phi_temp));
            for incoming in phi
                .incoming
                .iter()
                .filter(|incoming| preds.contains(&incoming.pred))
            {
                for def in &incoming.defs {
                    let Some(def_temp) = self.lowering.bindings.fixed_temps.get(def.index()) else {
                        continue;
                    };
                    overrides.insert(*def_temp, target.clone());
                }
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
            preds.extend(value.then_preds.iter().copied());
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
            preds.extend(value.else_preds.iter().copied());
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
                    self.suppressed_phis.insert(value.phi_id);
                    self.entry_overrides
                        .entry(candidate.merge)
                        .or_default()
                        .insert(value.reg, expr);
                }
                BranchValueOverride::Snapshot(expr) => {
                    if self.phi_used_only_in_block(value.phi_id, candidate.merge) {
                        self.suppressed_phis.insert(value.phi_id);
                        self.entry_overrides
                            .entry(candidate.merge)
                            .or_default()
                            .insert(value.reg, expr);
                    } else {
                        self.phi_overrides
                            .entry(candidate.merge)
                            .or_default()
                            .insert(value.phi_id, expr);
                    }
                }
            }
        }
    }

    fn phi_used_only_in_block(&self, phi_id: PhiId, block: BlockRef) -> bool {
        let mut saw_use = false;

        for (instr_index, use_values) in self.lowering.dataflow.use_values.iter().enumerate() {
            let used_here = use_values
                .fixed
                .values()
                .any(|values| values.contains(&SsaValue::Phi(phi_id)));
            if !used_here {
                continue;
            }

            saw_use = true;
            if self.lowering.cfg.instr_to_block[instr_index] != block {
                return false;
            }
        }

        saw_use
    }

    fn branch_value_override_expr(
        &self,
        header: BlockRef,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<BranchValueOverride> {
        let phi = self
            .lowering
            .dataflow
            .phi_candidates
            .get(value.phi_id.index())?;

        self.shared_branch_target_expr(phi, target_overrides)
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
        let phi = self
            .lowering
            .dataflow
            .phi_candidates
            .get(value.phi_id.index())?;
        let mut shared_target = None;

        for incoming in &phi.incoming {
            for def in &incoming.defs {
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
        }

        shared_target
    }

    fn shared_branch_target_expr(
        &self,
        phi: &PhiCandidate,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let mut shared_expr = None;

        for incoming in &phi.incoming {
            for def in &incoming.defs {
                let temp = *self.lowering.bindings.fixed_temps.get(def.index())?;
                let lvalue = target_overrides.get(&temp)?;
                let expr = lvalue_as_expr(lvalue)?;
                if shared_expr
                    .as_ref()
                    .is_some_and(|known_expr: &HirExpr| *known_expr != expr)
                {
                    return None;
                }
                shared_expr = Some(expr);
            }
        }

        shared_expr
    }

    fn branch_value_decision_expr(
        &self,
        header: BlockRef,
        value: &BranchValueMergeValue,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirExpr> {
        let candidate = *self.branch_by_header.get(&header)?;
        let mut cond = self.lower_candidate_cond(header, candidate)?;
        let mut then_expr = self.uniform_dup_safe_arm_expr(value, &value.then_preds)?;
        let mut else_expr = self.uniform_dup_safe_arm_expr(value, &value.else_preds)?;
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

    fn uniform_dup_safe_arm_expr(
        &self,
        value: &BranchValueMergeValue,
        preds: &std::collections::BTreeSet<BlockRef>,
    ) -> Option<HirExpr> {
        let phi = self
            .lowering
            .dataflow
            .phi_candidates
            .get(value.phi_id.index())?;
        let mut arm_expr = None;

        for incoming in phi
            .incoming
            .iter()
            .filter(|incoming| preds.contains(&incoming.pred))
        {
            for def in &incoming.defs {
                let expr = expr_for_dup_safe_fixed_def(self.lowering, *def)?;
                if arm_expr
                    .as_ref()
                    .is_some_and(|known_expr: &HirExpr| *known_expr != expr)
                {
                    return None;
                }
                arm_expr = Some(expr);
            }
        }

        arm_expr
    }
}

enum BranchValueOverride {
    Alias(HirExpr),
    Snapshot(HirExpr),
}
