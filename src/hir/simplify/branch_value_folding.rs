//! 提升后处理：把 `local X; if cond then X=a else X=b end` 收回值表达式。
//!
//! 当 `locals` pass 刚刚把一个 temp 提升成 local 后，经常会出现
//! "先空声明，后分支赋值"的形状。这个子模块在提升出口处扫描这种形状，
//! 尝试把它折叠成 `local X = cond and a or b` 一类的值表达式。
//!
//! 这里的规则和原 `branch_value_exprs` pass 完全一致，只是执行时机从独立的 Normal
//! pass 前移到 `locals` 提升完成的收尾阶段，避免跨 pass 多轮迭代。
//!
//! 例子：
//! - 输入：`local l0; if cond then l0 = "a" else l0 = "b" end`
//! - 输出：`local l0 = cond and "a" or "b"`

use super::visit::HirVisitor;
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirIf,
    HirLValue, HirLocalDecl, HirStmt, LocalId,
};

/// 扫描 block 中的 `local X; if cond then X=a else X=b end` 形状，
/// 尝试把它收回 `local X = cond and a or b` 一类的值表达式。
pub(super) fn fold_branch_value_locals_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;
    let mut index = 1;

    while index < stmts.len() {
        let Some((binding, value)) =
            collapsible_branch_value_local(&stmts[index - 1], &stmts[index])
        else {
            index += 1;
            continue;
        };

        stmts[index - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![binding],
            values: vec![value],
        }));
        stmts.remove(index);
        changed = true;
    }

    changed
}

fn collapsible_branch_value_local(
    local_decl_stmt: &HirStmt,
    if_stmt: &HirStmt,
) -> Option<(LocalId, HirExpr)> {
    let binding = empty_single_local_decl_binding(local_decl_stmt)?;
    let if_stmt = single_binding_value_if(if_stmt, binding)?;
    let value = branch_value_expr(binding, if_stmt)?;
    Some((binding, value))
}

fn branch_value_expr(binding: LocalId, if_stmt: &HirIf) -> Option<HirExpr> {
    let (truthy, falsy) = branch_assign_values(if_stmt, binding)?;
    if expr_mentions_local(&if_stmt.cond, binding)
        || expr_mentions_local(truthy, binding)
        || expr_mentions_local(falsy, binding)
    {
        return None;
    }

    let decision = HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![HirDecisionNode {
            id: HirDecisionNodeRef(0),
            test: if_stmt.cond.clone(),
            truthy: HirDecisionTarget::Expr(truthy.clone()),
            falsy: HirDecisionTarget::Expr(falsy.clone()),
        }],
    };
    let value = crate::hir::decision::finalize_value_decision_expr(decision);
    (!matches!(value, HirExpr::Decision(_))).then_some(value)
}

fn branch_assign_values(if_stmt: &HirIf, binding: LocalId) -> Option<(&HirExpr, &HirExpr)> {
    let [HirStmt::Assign(then_assign)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref()?;
    let [HirStmt::Assign(else_assign)] = else_block.stmts.as_slice() else {
        return None;
    };
    let [then_target] = then_assign.targets.as_slice() else {
        return None;
    };
    let [then_value] = then_assign.values.as_slice() else {
        return None;
    };
    let [else_target] = else_assign.targets.as_slice() else {
        return None;
    };
    let [else_value] = else_assign.values.as_slice() else {
        return None;
    };
    if !matches_local_lvalue(then_target, binding) || !matches_local_lvalue(else_target, binding) {
        return None;
    }
    Some((then_value, else_value))
}

fn single_binding_value_if(stmt: &HirStmt, binding: LocalId) -> Option<&HirIf> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let _ = branch_assign_values(if_stmt, binding)?;
    Some(if_stmt)
}

pub(super) fn empty_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

pub(super) fn matches_local_lvalue(target: &HirLValue, binding: LocalId) -> bool {
    matches!(target, HirLValue::Local(local) if *local == binding)
}

fn expr_mentions_local(expr: &HirExpr, binding: LocalId) -> bool {
    let mut visitor = LocalMentionVisitor {
        binding,
        mentioned: false,
    };
    super::visit::visit_expr(expr, &mut visitor);
    visitor.mentioned
}

struct LocalMentionVisitor {
    binding: LocalId,
    mentioned: bool,
}

impl HirVisitor for LocalMentionVisitor {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::LocalRef(local) if *local == self.binding);
    }
}
