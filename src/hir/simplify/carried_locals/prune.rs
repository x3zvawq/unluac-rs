//! carried-local 收敛后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除本次改写可以证明制造出来的
//! 单目标 `x = x`、空 assign、直接 binding 的整句 `x, y = x, y`，以及精确相邻的
//! `a = b; b = a` 无操作回写。它不拆分多目标赋值，因为其中的单个 `x = x` 仍可能
//! 恢复其它 RHS 求值前的快照；也不重新判断 carried 状态是否可合并，避免把 preserved
//! current-value 这类仍有语义的分支快照误删。

use std::collections::BTreeSet;

use crate::hir::common::{HirAssign, HirBlock, HirExpr, HirLValue, HirStmt};

use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::{
    CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue, single_binding_copy,
};

pub(super) struct RedundantSelfAssignPrunePass {
    prunable_bindings: BTreeSet<CarryBinding>,
}

impl RedundantSelfAssignPrunePass {
    pub(super) fn for_bindings(bindings: impl IntoIterator<Item = CarryBinding>) -> Self {
        Self {
            prunable_bindings: collect_prunable_bindings(bindings),
        }
    }
}

impl HirRewritePass for RedundantSelfAssignPrunePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
        block.stmts.len() != original_len
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        prune_redundant_self_assign_stmt(stmt, &self.prunable_bindings)
    }
}

pub(super) fn prune_empty_assign_stmts(block: &mut HirBlock) -> bool {
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
    block.stmts.len() != original_len
}

pub(super) fn prune_redundant_copy_stmts(block: &mut HirBlock) -> bool {
    let original = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::<HirStmt>::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        let copy = single_binding_copy(&stmt);
        let redundant_parallel = matches!(
            &stmt,
            HirStmt::Assign(assign) if redundant_parallel_self_copy(assign)
        );
        if copy.is_some_and(|(target, source)| target == source)
            || redundant_parallel
            || rewritten
                .last()
                .and_then(single_binding_copy)
                .zip(copy)
                .is_some_and(|((first_target, first_source), (target, source))| {
                    first_target != first_source && first_target == source && first_source == target
                })
        {
            changed = true;
        } else {
            rewritten.push(stmt);
        }
    }

    block.stmts = rewritten;
    changed
}

fn redundant_parallel_self_copy(assign: &HirAssign) -> bool {
    if assign.values.tail.is_some()
        || assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
    {
        return false;
    }
    let mut targets = BTreeSet::new();
    assign
        .targets
        .iter()
        .zip(&assign.values.fixed)
        .all(|(target, value)| {
            let Some(target) = carry_binding_from_lvalue(target) else {
                return false;
            };
            let Some(value) = carry_binding_from_expr(value) else {
                return false;
            };
            target == value && targets.insert(target)
        })
}

pub(super) fn prune_redundant_self_assigns_in_stmts(
    stmts: &mut [HirStmt],
    prunable_bindings: BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut pass = RedundantSelfAssignPrunePass { prunable_bindings };
    rewrite_stmts(stmts, &mut pass)
}

pub(super) fn collect_prunable_bindings(
    bindings: impl IntoIterator<Item = CarryBinding>,
) -> BTreeSet<CarryBinding> {
    bindings.into_iter().collect()
}

fn prune_redundant_self_assign_stmt(
    stmt: &mut HirStmt,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([target], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    if !matches_redundant_self_assign_pair(target, value, prunable_bindings) {
        return false;
    }

    assign.targets.clear();
    assign.values.fixed.clear();
    true
}

fn matches_redundant_self_assign_pair(
    target: &HirLValue,
    value: &HirExpr,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    redundant_self_assign_binding(target, value)
        .is_some_and(|binding| prunable_bindings.contains(&binding))
}

fn redundant_self_assign_binding(target: &HirLValue, value: &HirExpr) -> Option<CarryBinding> {
    match (target, value) {
        (HirLValue::Param(target), HirExpr::ParamRef(value)) if target == value => {
            Some(CarryBinding::Param(*target))
        }
        (HirLValue::Temp(target), HirExpr::TempRef(value)) if target == value => {
            Some(CarryBinding::Temp(*target))
        }
        (HirLValue::Local(target), HirExpr::LocalRef(value)) if target == value => {
            Some(CarryBinding::Local(*target))
        }
        _ => None,
    }
}

fn is_empty_assign_stmt(stmt: &HirStmt) -> bool {
    matches!(stmt, HirStmt::Assign(assign) if assign.targets.is_empty())
}
