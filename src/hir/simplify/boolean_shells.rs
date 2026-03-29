//! 这个文件负责清理已经失去职责的值物化分支壳。
//!
//! 它依赖更前面的 HIR 决策已经把“真正承载语义的 merge 值”恢复成直接表达式；
//! 走到这里时，某些 `if cond then t=true else t=false end` 只剩下机械性的值物化。
//! 这里专门删除这一类纯值壳，或者把它们折回单条赋值，避免把真正承担控制语义的
//! `if/else` 结构误删掉。
//!
//! 它不会越权去重新判断 branch/loop 是否应该结构化，也不会替前层补决策。
//! 这里唯一关心的是：当前 `if` 是否已经退化成“无副作用的布尔值搬运壳”。
//!
//! 例子：
//! - 输入：`if cond then t = true else t = false end`
//! - 输出：`t = cond or false`
//! - 如果 `t` 后面已经没人再读，且 `cond/true/false` 都无副作用，则整段壳会被删除

use std::collections::BTreeMap;

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirLogicalExpr, HirProto, HirStmt,
    HirUnaryExpr, HirUnaryOpKind, LocalId, TempId,
};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_boolean_materialization_shells_in_proto(proto: &mut HirProto) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let mut dead_shell_pass = DeadBooleanShellPass {
        use_counts: &use_counts,
    };
    let mut collapse_shell_pass = CollapseBooleanShellPass;
    rewrite_proto(proto, &mut dead_shell_pass) | rewrite_proto(proto, &mut collapse_shell_pass)
}

struct DeadBooleanShellPass<'a> {
    use_counts: &'a BTreeMap<TempId, usize>,
}

impl HirRewritePass for DeadBooleanShellPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        remove_dead_materialization_shells_from_block(block, self.use_counts)
    }
}

fn remove_dead_materialization_shells_from_block(
    block: &mut HirBlock,
    use_counts: &BTreeMap<TempId, usize>,
) -> bool {
    let mut index = 0;
    let mut changed = false;
    while index < block.stmts.len() {
        if removable_dead_materialization_shell(&block.stmts[index], use_counts) {
            block.stmts.remove(index);
            changed = true;
            continue;
        }
        index += 1;
    }

    changed
}

struct CollapseBooleanShellPass;

impl HirRewritePass for CollapseBooleanShellPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_live_boolean_materialization_shells_in_block(block)
    }
}

fn collapse_live_boolean_materialization_shells_in_block(block: &mut HirBlock) -> bool {
    let mut index = 0;
    let mut changed = false;
    while index < block.stmts.len() {
        let Some((target, value)) =
            collapsible_live_boolean_materialization_shell(&block.stmts[index])
        else {
            index += 1;
            continue;
        };

        if index > 0
            && let HirLValue::Local(local) = &target
            && empty_single_local_decl_binding(&block.stmts[index - 1]) == Some(*local)
        {
            block.stmts[index - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![*local],
                values: vec![value],
            }));
            block.stmts.remove(index);
            changed = true;
            index = index.saturating_sub(1);
            continue;
        }

        block.stmts[index] = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: vec![value],
        }));
        changed = true;
        index += 1;
    }

    changed
}

fn collapsible_live_boolean_materialization_shell(stmt: &HirStmt) -> Option<(HirLValue, HirExpr)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return None;
    };

    let (then_target, then_value) = pure_assign_pattern(&if_stmt.then_block)?;
    let (else_target, else_value) = pure_assign_pattern(else_block)?;
    if then_target != else_target {
        return None;
    }

    match (then_value, else_value) {
        (HirExpr::Boolean(true), HirExpr::Boolean(false)) => Some((
            then_target.clone(),
            booleanized_truthiness_expr(if_stmt.cond.clone()),
        )),
        (HirExpr::Boolean(false), HirExpr::Boolean(true)) => Some((
            then_target.clone(),
            HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::Not,
                expr: if_stmt.cond.clone(),
            })),
        )),
        _ => None,
    }
}

fn removable_dead_materialization_shell(
    stmt: &HirStmt,
    use_counts: &BTreeMap<TempId, usize>,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    if !expr_is_side_effect_free(&if_stmt.cond) {
        return false;
    }

    let Some((then_target, then_value)) = pure_assign_pattern(&if_stmt.then_block) else {
        return false;
    };
    let Some((else_target, else_value)) = pure_assign_pattern(else_block) else {
        return false;
    };
    let (HirLValue::Temp(then_temp), HirLValue::Temp(else_temp)) = (then_target, else_target)
    else {
        return false;
    };

    if use_counts.get(then_temp).copied().unwrap_or(0) != 0
        || use_counts.get(else_temp).copied().unwrap_or(0) != 0
    {
        return false;
    }

    expr_is_side_effect_free(then_value) && expr_is_side_effect_free(else_value)
}

fn pure_assign_pattern(block: &HirBlock) -> Option<(&HirLValue, &HirExpr)> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };

    Some((target, value))
}

fn empty_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    if !local_decl.values.is_empty() {
        return None;
    }
    Some(*binding)
}

fn booleanized_truthiness_expr(cond: HirExpr) -> HirExpr {
    if expr_is_boolean_valued(&cond) {
        cond
    } else {
        HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: cond,
                rhs: HirExpr::Boolean(true),
            })),
            rhs: HirExpr::Boolean(false),
        }))
    }
}

fn expr_is_boolean_valued(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Boolean(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => true,
        HirExpr::Binary(binary) => matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Eq
                | crate::hir::common::HirBinaryOpKind::Lt
                | crate::hir::common::HirBinaryOpKind::Le
        ),
        _ => false,
    }
}

fn collect_temp_use_counts(proto: &HirProto) -> BTreeMap<TempId, usize> {
    let mut collector = TempUseCollector::default();
    visit_proto(proto, &mut collector);
    collector.use_counts
}

#[derive(Default)]
struct TempUseCollector {
    use_counts: BTreeMap<TempId, usize>,
}

impl HirVisitor for TempUseCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            *self.use_counts.entry(*temp).or_default() += 1;
        }
    }
}

fn expr_is_side_effect_free(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::Unary(unary) => expr_is_side_effect_free(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_side_effect_free(&binary.lhs) && expr_is_side_effect_free(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_side_effect_free(&logical.lhs) && expr_is_side_effect_free(&logical.rhs)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().all(|node| {
            expr_is_side_effect_free(&node.test)
                && decision_target_is_side_effect_free(&node.truthy)
                && decision_target_is_side_effect_free(&node.falsy)
        }),
        HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_is_side_effect_free(target: &crate::hir::common::HirDecisionTarget) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => true,
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_is_side_effect_free(expr),
    }
}

#[cfg(test)]
mod tests;
