//! 提升后处理：把 `local X; if cond then X=a else X=b end` 收回值表达式。
//!
//! 当 `locals` pass 刚刚把一个 temp 提升成 local 后，经常会出现
//! "先空声明，后分支赋值"的形状。这个子模块在提升出口处扫描这种形状，
//! 尝试把它折叠成 `local X = cond and a or b` 一类的值表达式。
//!
//! 这里的规则和原 `branch_value_exprs` pass 完全一致，只是执行时机从独立的 Normal
//! pass 前移到 `locals` 提升完成的收尾阶段，避免跨 pass 多轮迭代。
//!
//! 除了平铺的两臂形状以外，结构恢复阶段经常因为短路条件被翻译成多层嵌套 `if`
//! 而把同一个 binding 的赋值散落在树形 if/else 的所有叶子上。这里通过 `try_collapse_block_to_value`
//! 递归地把"每条路径都只是给 binding 赋一个值"的子树折回单条 Decision 表达式，
//! 让后续 `decision::collapse_value_decision_expr` + `logical-simplify` 还原成扁平的 and/or 链。
//! 以及短路链常见的"`local LX = expr; if LX then X = LX else REST`"形态也会被识别成 `expr or REST`。
//!
//! 例子：
//! - 输入：`local l0; if cond then l0 = "a" else l0 = "b" end`
//! - 输出：`local l0 = cond and "a" or "b"`
//! - 输入：`local l0; if c1 then if c2 then l0 = a else l0 = b end else l0 = c end`
//! - 输出：`local l0 = c1 and (c2 and a or b) or c`

use super::visit::HirVisitor;
use crate::hir::common::{
    HirAssign, HirBlock, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget,
    HirExpr, HirIf, HirLValue, HirLocalDecl, HirStmt, LocalId,
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
    let HirStmt::If(if_stmt) = if_stmt else {
        return None;
    };
    let value = branch_value_expr(binding, if_stmt)?;
    Some((binding, value))
}

fn branch_value_expr(binding: LocalId, if_stmt: &HirIf) -> Option<HirExpr> {
    let truthy = try_collapse_block_to_value(&if_stmt.then_block, binding)?;
    let else_block = if_stmt.else_block.as_ref()?;
    let falsy = try_collapse_block_to_value(else_block, binding)?;
    if expr_mentions_local(&if_stmt.cond, binding)
        || expr_mentions_local(&truthy, binding)
        || expr_mentions_local(&falsy, binding)
    {
        return None;
    }
    finalize_branch_value(&if_stmt.cond, truthy, falsy)
}

fn finalize_branch_value(cond: &HirExpr, truthy: HirExpr, falsy: HirExpr) -> Option<HirExpr> {
    let decision = HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![HirDecisionNode {
            id: HirDecisionNodeRef(0),
            test: cond.clone(),
            truthy: HirDecisionTarget::Expr(truthy),
            falsy: HirDecisionTarget::Expr(falsy),
        }],
    };
    let value = crate::hir::decision::finalize_value_decision_expr(decision);
    (!matches!(value, HirExpr::Decision(_))).then_some(value)
}

/// 递归地尝试把一个 block 折叠成"对 `binding` 唯一赋值"的值表达式。
///
/// 支持三种形态：
/// 1. 单条 `assign binding = expr`；
/// 2. 单条 `if cond then THEN else ELSE end`，THEN/ELSE 各自递归满足；
/// 3. `local LX = v; if LX then assign binding = LX else REST` —— 等价于 `v or REST_value`，
///    `LX` 在 if 之外不可见，因此可以把它消解成 `v or REST_value`。
fn try_collapse_block_to_value(block: &HirBlock, binding: LocalId) -> Option<HirExpr> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign)] => single_assign_value(assign, binding).cloned(),
        [HirStmt::If(if_stmt)] => branch_value_expr(binding, if_stmt),
        [HirStmt::LocalDecl(decl), HirStmt::If(if_stmt)] => {
            collapse_temp_guard_pattern(decl, if_stmt, binding)
        }
        _ => None,
    }
}

fn single_assign_value(assign: &HirAssign, binding: LocalId) -> Option<&HirExpr> {
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    matches_local_lvalue(target, binding).then_some(value)
}

/// 处理 `local LX = v; if LX then assign binding = LX else REST end` 这一短路守卫形态。
///
/// 该形态来自结构恢复阶段把 `binding = v or RESTV` 这种短路赋值展开成"先把 `v` 物化到
/// 新 temp `LX`，再用 `LX` 做条件判断"的中间形态。如果 `LX` 在这之外没有被引用过，
/// 就可以重新折回 `binding = v or RESTV`，避免给最终输出留下毫无意义的物化壳。
fn collapse_temp_guard_pattern(
    decl: &HirLocalDecl,
    if_stmt: &HirIf,
    binding: LocalId,
) -> Option<HirExpr> {
    let [lx] = decl.bindings.as_slice() else {
        return None;
    };
    let [lx_value] = decl.values.as_slice() else {
        return None;
    };
    let lx = *lx;

    // cond 必须就是 `LocalRef(lx)`
    let HirExpr::LocalRef(cond_local) = &if_stmt.cond else {
        return None;
    };
    if *cond_local != lx {
        return None;
    }

    // then 分支必须就是 `assign binding = LocalRef(lx)`
    let [HirStmt::Assign(then_assign)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    let then_value = single_assign_value(then_assign, binding)?;
    let HirExpr::LocalRef(then_local) = then_value else {
        return None;
    };
    if *then_local != lx {
        return None;
    }

    let else_block = if_stmt.else_block.as_ref()?;
    if expr_mentions_local(lx_value, lx)
        || expr_mentions_local(lx_value, binding)
        || block_mentions_local(else_block, lx)
    {
        return None;
    }
    let rest_value = try_collapse_block_to_value(else_block, binding)?;
    if expr_mentions_local(&rest_value, binding) || expr_mentions_local(&rest_value, lx) {
        return None;
    }

    finalize_branch_value(lx_value, lx_value.clone(), rest_value)
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

fn block_mentions_local(block: &HirBlock, binding: LocalId) -> bool {
    let mut visitor = LocalMentionVisitor {
        binding,
        mentioned: false,
    };
    super::visit::visit_block(block, &mut visitor);
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
