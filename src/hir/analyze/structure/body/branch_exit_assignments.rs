//! 这个文件承载 branch-exit value assignment 的快捷恢复。
//!
//! 短路条件有时会把某个 truthy/falsy 出口编译成单独 value leaf，并在 region stop
//! 另一侧继续共享控制流。这里只处理“出口 leaf 是安全单赋值，且目标正是当前
//! branch-value override 目标”的形状，把它恢复成条件包裹的赋值语句。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn try_lower_branch_exit_value_assignment(
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
