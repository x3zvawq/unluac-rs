//! carried-local 改写后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除本次改写可以证明制造出来的
//! `x = x` 组件和空 assign。它不重新判断 carried 状态是否可合并，避免把 preserved
//! current-value 这类仍有语义的分支快照误删。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt};

use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::CarryBinding;

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
        prune_redundant_self_assign_components_in_stmt(stmt, &self.prunable_bindings)
    }
}

pub(super) fn prune_empty_assign_stmts(block: &mut HirBlock) -> bool {
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
    block.stmts.len() != original_len
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

pub(super) fn prune_boundary_snapshot_self_assigns(
    block: &mut HirBlock,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut changed = false;

    for index in 0..block.stmts.len() {
        let top_level_boundary_snapshot = matches!(
            block.stmts.get(index + 1),
            Some(HirStmt::Goto(_) | HirStmt::Label(_))
        );
        let falls_through_to_label = matches!(block.stmts.get(index + 1), Some(HirStmt::Label(_)));

        match &mut block.stmts[index] {
            stmt @ HirStmt::Assign(_) if top_level_boundary_snapshot => {
                changed |= prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings);
            }
            HirStmt::If(if_stmt) => {
                changed |= prune_edge_snapshot_self_assigns(
                    &mut if_stmt.then_block,
                    falls_through_to_label,
                    prunable_bindings,
                );
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= prune_edge_snapshot_self_assigns(
                        else_block,
                        falls_through_to_label,
                        prunable_bindings,
                    );
                }
            }
            _ => {}
        }
    }

    changed |= prune_empty_assign_stmts(block);
    changed
}

fn prune_edge_snapshot_self_assigns(
    block: &mut HirBlock,
    allow_fallthrough_to_label: bool,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut changed = match block.stmts.as_mut_slice() {
        [stmt @ HirStmt::Assign(_), HirStmt::Goto(_)] => {
            prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings)
        }
        [stmt @ HirStmt::Assign(_)] if allow_fallthrough_to_label => {
            prune_redundant_self_assign_components_in_stmt(stmt, prunable_bindings)
        }
        _ => false,
    };
    changed |= prune_empty_assign_stmts(block);
    changed
}

fn prune_redundant_self_assign_components_in_stmt(
    stmt: &mut HirStmt,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    if assign.targets.len() != assign.values.len() {
        return false;
    }

    let mut rewritten = Vec::with_capacity(assign.targets.len());
    for (target, value) in assign
        .targets
        .iter()
        .cloned()
        .zip(assign.values.iter().cloned())
    {
        if !matches_redundant_self_assign_pair(&target, &value, prunable_bindings) {
            rewritten.push((target, value));
        }
    }

    if rewritten.len() == assign.targets.len() {
        return false;
    }

    assign.targets = rewritten.iter().map(|(target, _)| target.clone()).collect();
    assign.values = rewritten.into_iter().map(|(_, value)| value).collect();
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
