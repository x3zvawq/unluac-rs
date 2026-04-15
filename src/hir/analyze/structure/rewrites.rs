//! 这个文件集中放结构化 lowering 里的局部重写 helper。
//!
//! `structure.rs` 主体更适合表达“什么时候能结构化恢复”，而这些函数只负责在
//! 结构已经确定之后，把 loop state/temp 身份同步改写到同一批 HIR 语句里。
//! 单独拆出来之后，主流程文件更容易看出控制流决策，重写细节也更容易局部维护。

use std::collections::BTreeMap;

use crate::cfg::DefId;
use crate::hir::common::{HirExpr, HirLValue, HirStmt, TempId};

/// 检查表达式中是否仍残留未被替换的 `TempRef`。
///
/// 当循环头部前缀包含无法内联的指令（如多返回值调用）时，
/// `block_prefix_temp_expr_overrides` 无法为所有 temp 生成 override，
/// 条件表达式里就会残留 TempRef 节点。这个 helper 用来检测这种情况，
/// 驱动 `lower_while_loop` 回退到 `while true + if-break` 模式。
pub(super) fn expr_has_temp_ref(expr: &HirExpr) -> bool {
    if matches!(expr, HirExpr::TempRef(_)) {
        return true;
    }
    let mut found = false;
    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { if expr_has_temp_ref(e) { found = true; } },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { if expr_has_temp_ref(e) { found = true; } }
            );
        },
        decision(d) => {
            traverse_hir_decision_children!(
                d,
                iter = iter,
                borrow = [&],
                expr(e) => { if expr_has_temp_ref(e) { found = true; } },
                condition(cond) => { if expr_has_temp_ref(cond) { found = true; } }
            );
        },
        table_constructor(t) => {
            traverse_hir_table_constructor_children!(
                t,
                iter = iter,
                opt = as_ref,
                borrow = [&],
                expr(e) => { if expr_has_temp_ref(e) { found = true; } }
            );
        }
    );
    found
}
use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};

pub(super) fn apply_loop_rewrites(
    stmts: &mut [HirStmt],
    target_overrides: &BTreeMap<TempId, HirLValue>,
) {
    if target_overrides.is_empty() {
        return;
    }

    // loop body 里某个 def 一旦被我们收成“稳定状态变量写回”，同 block 后面的 use
    // 也必须同步看到这个新身份；否则就会出现“target 已经是 l0，但后续读取还是 t2”
    // 这种半 SSA、半命令式的错误形状。
    let expr_overrides = temp_expr_overrides(target_overrides);
    for stmt in stmts {
        rewrite_stmt_exprs(stmt, &expr_overrides);
        rewrite_stmt_targets(stmt, target_overrides);
    }
}

pub(super) fn temp_expr_overrides(
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> BTreeMap<TempId, HirExpr> {
    target_overrides
        .iter()
        .filter_map(|(temp, lvalue)| lvalue_as_expr(lvalue).map(|expr| (*temp, expr)))
        .collect()
}

pub(super) fn lvalue_as_expr(lvalue: &HirLValue) -> Option<HirExpr> {
    match lvalue {
        HirLValue::Temp(temp) => Some(HirExpr::TempRef(*temp)),
        HirLValue::Local(local) => Some(HirExpr::LocalRef(*local)),
        HirLValue::Upvalue(upvalue) => Some(HirExpr::UpvalueRef(*upvalue)),
        HirLValue::Global(global) => Some(HirExpr::GlobalRef(global.clone())),
        HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn expr_as_lvalue(expr: &HirExpr) -> Option<HirLValue> {
    match expr {
        HirExpr::TempRef(temp) => Some(HirLValue::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(HirLValue::Local(*local)),
        HirExpr::UpvalueRef(upvalue) => Some(HirLValue::Upvalue(*upvalue)),
        HirExpr::GlobalRef(global) => Some(HirLValue::Global(global.clone())),
        _ => None,
    }
}

pub(super) fn shared_expr_for_defs<I>(
    fixed_temps: &[TempId],
    defs: I,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> Option<HirExpr>
where
    I: IntoIterator<Item = DefId>,
{
    let mut shared_expr = None;

    for def in defs {
        let temp = *fixed_temps.get(def.index())?;
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

    shared_expr
}

/// 检查一组 defs 是否全部 override 到同一个可表达为表达式的 lvalue。
///
/// 这是 `shared_expr_for_defs` 的 lvalue 版本——前者返回 `HirExpr`，这里返回
/// `HirLValue`。Branch 和 Loop 都需要用这个来判断"是否所有写入都指向同一个目标"
/// 从而决定能不能把 phi temp 直接收成 alias。
pub(super) fn shared_lvalue_for_defs<I>(
    fixed_temps: &[TempId],
    defs: I,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) -> Option<HirLValue>
where
    I: IntoIterator<Item = DefId>,
{
    let mut shared_target = None;

    for def in defs {
        let temp = *fixed_temps.get(def.index())?;
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

/// 把一组 defs 的 target override 批量安装到 override map 里。
///
/// Branch 和 Loop 都有"遍历 arm defs → 查 fixed_temp → 插入 target override"的模式，
/// 这里统一提取成 helper。
pub(super) fn install_def_target_overrides(
    fixed_temps: &[TempId],
    defs: impl IntoIterator<Item = DefId>,
    target: &HirLValue,
    overrides: &mut BTreeMap<TempId, HirLValue>,
) {
    for def in defs {
        let Some(def_temp) = fixed_temps.get(def.index()) else {
            continue;
        };
        overrides.insert(*def_temp, target.clone());
    }
}

pub(super) fn rewrite_stmt_targets(
    stmt: &mut HirStmt,
    target_overrides: &BTreeMap<TempId, HirLValue>,
) {
    let HirStmt::Assign(assign) = stmt else {
        return;
    };
    for target in &mut assign.targets {
        let HirLValue::Temp(temp) = target else {
            continue;
        };
        if let Some(replacement) = target_overrides.get(temp) {
            *target = replacement.clone();
        }
    }
}

pub(super) fn rewrite_stmt_exprs(stmt: &mut HirStmt, expr_overrides: &BTreeMap<TempId, HirExpr>) {
    traverse_hir_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(e) => { rewrite_expr_temps(e, expr_overrides); },
        lvalue(lv) => {
            traverse_hir_lvalue_children!(
                lv,
                borrow = [&mut],
                expr(e) => { rewrite_expr_temps(e, expr_overrides); }
            );
        },
        block(_b) => {},
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter_mut,
                borrow = [&mut],
                expr(e) => { rewrite_expr_temps(e, expr_overrides); }
            );
        },
        condition(cond) => { rewrite_expr_temps(cond, expr_overrides); }
    );
}

pub(super) fn rewrite_expr_temps(expr: &mut HirExpr, expr_overrides: &BTreeMap<TempId, HirExpr>) {
    if let HirExpr::TempRef(temp) = expr
        && let Some(replacement) = expr_overrides.get(temp)
    {
        *expr = replacement.clone();
        return;
    }

    traverse_hir_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(e) => { rewrite_expr_temps(e, expr_overrides); },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter_mut,
                borrow = [&mut],
                expr(e) => { rewrite_expr_temps(e, expr_overrides); }
            );
        },
        decision(d) => {
            traverse_hir_decision_children!(
                d,
                iter = iter_mut,
                borrow = [&mut],
                expr(e) => { rewrite_expr_temps(e, expr_overrides); },
                condition(cond) => { rewrite_expr_temps(cond, expr_overrides); }
            );
        },
        table_constructor(t) => {
            traverse_hir_table_constructor_children!(
                t,
                iter = iter_mut,
                opt = as_mut,
                borrow = [&mut],
                expr(e) => { rewrite_expr_temps(e, expr_overrides); }
            );
        }
    );
}
