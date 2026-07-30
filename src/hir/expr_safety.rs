//! HIR 表达式求值安全性的共享判断。
//!
//! HIR analyze 和 simplify 都会判断某个表达式是否能被挪动或折进别的表达式。
//! 这个文件只放跨 pass 共用、和具体恢复策略无关的谓词，避免求值序规则散落后漂移。

use super::common::{HirBinaryOpKind, HirCaptureMode, HirExpr, HirUnaryOpKind};

/// 表达式的求值能否在不改变 Lua 可观察行为的前提下被删除。
pub(crate) fn expr_is_discard_safe(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            expr_is_discard_safe(&unary.expr)
        }
        HirExpr::Binary(binary) if stable_literal_equality(binary.op, &binary.lhs, &binary.rhs) => {
            expr_is_discard_safe(&binary.lhs) && expr_is_discard_safe(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_discard_safe(&logical.lhs) && expr_is_discard_safe(&logical.rhs)
        }
        // 全局读取可触发环境表 __index；其余节点可能调用元方法、分配新身份或执行用户代码。
        HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_) => false,
    }
}

/// 表达式是否可以在同一个无副作用逻辑区域内合并重复求值。
///
/// 该谓词不等同于“可丢弃”：它只接纳不会调用元方法、不会读取动态环境、也不会
/// 产生新对象身份的稳定值。代数改写仍需保证被跨越的其他表达式也满足本谓词。
pub(crate) fn expr_is_repeatable(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_) => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => expr_is_repeatable(&unary.expr),
        HirExpr::Binary(binary) if stable_literal_equality(binary.op, &binary.lhs, &binary.rhs) => {
            expr_is_repeatable(&binary.lhs) && expr_is_repeatable(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_repeatable(&logical.lhs) && expr_is_repeatable(&logical.rhs)
        }
        HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

/// Lua equality 只有在两侧都可能是 table/userdata 一类对象时才会进入 `__eq`。
/// 一侧是原始字面量即可排除用户代码；另一侧仍必须由调用方证明可重复读取。
fn stable_literal_equality(op: HirBinaryOpKind, lhs: &HirExpr, rhs: &HirExpr) -> bool {
    op == HirBinaryOpKind::Eq
        && (is_metamethod_inert_literal(lhs) || is_metamethod_inert_literal(rhs))
}

fn is_metamethod_inert_literal(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
    )
}

pub(crate) fn expr_observes_eval_order(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::GlobalRef(_) | HirExpr::TableAccess(_) | HirExpr::Call(_) => true,
        HirExpr::Unary(_) | HirExpr::Binary(_) | HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
            true
        }
        HirExpr::Decision(_) | HirExpr::TableConstructor(_) => true,
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_observes_eval_order(&capture.value)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

/// 临时值记录的结果是否必须保留在后续语句中的读取顺序。
///
/// local/upvalue/param/temp 读取本身不是可观察事件，但其结果是定义点的快照；若把这份
/// 快照挪到更晚的调用或 lookup 之后，来源 binding 可能已经被改写。
pub(crate) fn expr_requires_ordered_snapshot(expr: &HirExpr) -> bool {
    expr_observes_eval_order(expr)
        || matches!(expr, HirExpr::Closure(closure) if closure.captures.iter().any(|capture| {
            capture.mode == HirCaptureMode::ByValue
                && expr_requires_ordered_snapshot(&capture.value)
        }))
        || matches!(
            expr,
            HirExpr::ParamRef(_)
                | HirExpr::LocalRef(_)
                | HirExpr::UpvalueRef(_)
                | HirExpr::TempRef(_)
        )
}
