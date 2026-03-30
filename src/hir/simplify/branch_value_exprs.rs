//! 这个文件负责把“空 local 声明 + branch 内赋候选值”的机械壳收回成单条值表达式。
//!
//! 某些 branch value merge 在结构层没有短路 DAG owner，只能先保守落成：
//! - `local sign`
//! - `if cond then sign = "neg" else sign = "pos" end`
//!
//! 这时真正的语义已经不是“控制流”，而是“给同一个 local 选一个值”。这里会把这种窄形状
//! 重新交回 HIR 自己的 `Decision -> Expr` 共享逻辑，让它统一决定是否能安全折回
//! `cond and truthy or falsy` 一类值表达式，而不是继续把源码值壳留到 AST/readability。
//!
//! 它不会越权去猜 method sugar，也不会把任意 `if-else` 都压成逻辑表达式；只有当：
//! - 前一条语句是空的单 local 声明
//! - `if` 的两臂都只给这个 local 赋一个值
//! - 条件和两臂值里都不再读取这个 local
//! - 共享 `Decision` collapse 明确证明能折回普通表达式
//!   才会改写。
//!
//! 例子：
//! - 输入：`local sign; if cond then sign = "neg" else sign = "pos" end`
//! - 输出：`local sign = cond and "neg" or "pos"`

use crate::hir::common::{
    HirBlock, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
    HirIf, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId,
};

use super::visit::{self, HirVisitor};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn collapse_branch_value_locals_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut BranchValueExprPass)
}

struct BranchValueExprPass;

impl HirRewritePass for BranchValueExprPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_branch_value_locals_in_block(block)
    }
}

fn collapse_branch_value_locals_in_block(block: &mut HirBlock) -> bool {
    let mut changed = false;
    let mut index = 1;

    while index < block.stmts.len() {
        let Some((binding, value)) =
            collapsible_branch_value_local(&block.stmts[index - 1], &block.stmts[index])
        else {
            index += 1;
            continue;
        };

        block.stmts[index - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![binding],
            values: vec![value],
        }));
        block.stmts.remove(index);
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
    if !matches_local_binding(then_target, binding) || !matches_local_binding(else_target, binding)
    {
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

fn empty_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

fn matches_local_binding(target: &HirLValue, binding: LocalId) -> bool {
    matches!(target, HirLValue::Local(local) if *local == binding)
}

fn expr_mentions_local(expr: &HirExpr, binding: LocalId) -> bool {
    let mut visitor = LocalMentionVisitor {
        binding,
        mentioned: false,
    };
    visit::visit_expr(expr, &mut visitor);
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

#[cfg(test)]
mod tests;
