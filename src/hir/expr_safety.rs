//! HIR 表达式求值安全性的共享判断。
//!
//! HIR analyze 和 simplify 都会判断某个表达式是否能被挪动或折进别的表达式。
//! 这个文件只放跨 pass 共用、和具体恢复策略无关的谓词，避免求值序规则散落后漂移。

use super::common::{HirBinaryOpKind, HirCaptureMode, HirExpr, HirUnaryOpKind};

/// 只计算不可能触发元方法的原始字面量比较。
///
/// 不同数值表示、cdata/vector/complex 等方言相关值故意不在这里互转；调用方只能把
/// `Some` 当作可删除求值的常量事实，`None` 必须继续保留原表达式。
pub(crate) fn primitive_literal_comparison_value(
    op: HirBinaryOpKind,
    lhs: &HirExpr,
    rhs: &HirExpr,
) -> Option<bool> {
    if op == HirBinaryOpKind::Eq {
        return match (lhs, rhs) {
            (HirExpr::Integer(lhs), HirExpr::Integer(rhs)) => Some(lhs == rhs),
            (HirExpr::Number(lhs), HirExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
                Some(lhs == rhs)
            }
            (HirExpr::String(lhs), HirExpr::String(rhs)) => Some(lhs == rhs),
            (HirExpr::Boolean(lhs), HirExpr::Boolean(rhs)) => Some(lhs == rhs),
            (HirExpr::Nil, HirExpr::Nil) => Some(true),
            _ => None,
        };
    }
    let ordering = match (lhs, rhs) {
        (HirExpr::Integer(lhs), HirExpr::Integer(rhs)) => lhs.cmp(rhs),
        (HirExpr::Number(lhs), HirExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
            lhs.partial_cmp(rhs)?
        }
        (HirExpr::String(lhs), HirExpr::String(rhs)) => lhs.cmp(rhs),
        _ => return None,
    };
    match op {
        HirBinaryOpKind::Lt => Some(ordering == std::cmp::Ordering::Less),
        HirBinaryOpKind::Le => Some(ordering != std::cmp::Ordering::Greater),
        _ => None,
    }
}

/// Luau 的 number 加法在两个原始数字操作数上走 VM 数值路径，不查用户元方法。
///
/// `HirExpr::Integer` 也可能来自 Luau 的 `LOADN`，并不代表 PUC Lua 的
/// `lua_Integer` 语义；因此这里只在调用方已确认目标是 Luau 时使用，并把两种
/// HIR 数字都先放进可精确表示的整数范围。超出范围、非有限数和负零都保留原
/// 运算，避免宿主 `f64` 舍入或符号位成为可观察差异。
pub(crate) fn luau_literal_addition_value(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    const MAX_EXACT_INTEGER: i128 = 1_i128 << 53;

    fn exact_integer(expr: &HirExpr) -> Option<i128> {
        match expr {
            HirExpr::Integer(value) => {
                let value = i128::from(*value);
                (-(MAX_EXACT_INTEGER)..=MAX_EXACT_INTEGER)
                    .contains(&value)
                    .then_some(value)
            }
            HirExpr::Number(value)
                if value.is_finite()
                    && !(*value == 0.0 && value.is_sign_negative())
                    && value.fract() == 0.0
                    && value.abs() <= MAX_EXACT_INTEGER as f64 =>
            {
                let integer = *value as i128;
                (integer as f64 == *value
                    && (-(MAX_EXACT_INTEGER)..=MAX_EXACT_INTEGER).contains(&integer))
                .then_some(integer)
            }
            _ => None,
        }
    }

    let value = exact_integer(lhs)?.checked_add(exact_integer(rhs)?)?;
    if !(-(MAX_EXACT_INTEGER)..=MAX_EXACT_INTEGER).contains(&value) {
        return None;
    }
    let result = value as f64;
    (result as i128 == value).then_some(HirExpr::Number(result))
}

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
        HirExpr::Binary(binary)
            if primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
                .is_some() =>
        {
            true
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
        HirExpr::Binary(binary)
            if primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
                .is_some() =>
        {
            true
        }
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
