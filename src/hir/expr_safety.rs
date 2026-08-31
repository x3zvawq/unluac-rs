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

/// Luau 的 number 加法在两个原始数字操作数上走 VM 的 IEEE 754 binary64 路径，
/// 不查用户元方法。
///
/// `HirExpr::Integer` 也可能来自 Luau 的 `LOADN`，并不代表 PUC Lua 的
/// `lua_Integer` 语义；因此这里只在调用方已确认目标是 Luau 时使用，并先把两种
/// HIR 数字统一到 Luau 唯一的 `f64` 数值域。这样由宿主执行同一次 binary64 加法，
/// 会自然保留舍入、溢出和负零结果。
pub(crate) fn luau_literal_addition_value(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    fn number(expr: &HirExpr) -> Option<f64> {
        match expr {
            HirExpr::Integer(value) => Some(*value as f64),
            HirExpr::Number(value) => Some(*value),
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Neg => {
                number(&unary.expr).map(std::ops::Neg::neg)
            }
            _ => None,
        }
    }

    Some(HirExpr::Number(number(lhs)? + number(rhs)?))
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

/// 表达式既可删除求值，也不承载必须交给 residual owner 的未解析诊断。
pub(crate) fn expr_is_discard_safe_without_residual(expr: &HirExpr) -> bool {
    if !expr_is_discard_safe(expr) {
        return false;
    }
    match expr {
        HirExpr::Unresolved(_) => false,
        HirExpr::Unary(unary) => expr_is_discard_safe_without_residual(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_discard_safe_without_residual(&binary.lhs)
                && expr_is_discard_safe_without_residual(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_discard_safe_without_residual(&logical.lhs)
                && expr_is_discard_safe_without_residual(&logical.rhs)
        }
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
        | HirExpr::VarArg => true,
        HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_) => false,
    }
}

/// 表达式的单值结果是否不会承载可观察的 GC 资源生命周期。
///
/// 这个谓词比“可丢弃求值”更窄：`not` 和原始比较的结果恒为 boolean，逻辑表达式
/// 则可能直接返回任一操作数。String 常量由 chunk 常量表持有，不会因为某个栈槽覆盖
/// 触发用户可观察的终结行为。LuaJIT 的 Int64/UInt64/Complex 虽由 GCcdata 表示，但
/// BC_KCDATA 指向 proto 的 KGC 常量且 proto 遍历会持续标记它；Luau vector 同样先由
/// proto 常量表持有。无论 vector 的宿主表示是内嵌值还是 boxed GC 对象，这些常量的
/// 存活期都不由某个栈槽是否继续引用决定。
pub(crate) fn expr_result_is_gc_inert(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. } => true,
        HirExpr::Unary(_) | HirExpr::Binary(_) => expr_is_discard_safe(expr),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_result_is_gc_inert(&logical.lhs) && expr_result_is_gc_inert(&logical.rhs)
        }
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

/// 表达式是否可以在同一个无副作用逻辑区域内合并重复求值。
///
/// 该谓词不等同于“可丢弃”：它只接纳不会调用元方法、不会读取动态环境、也不会
/// 产生新对象身份的稳定值。代数改写仍需保证被跨越的其他表达式也满足本谓词。
pub(crate) fn expr_is_repeatable(expr: &HirExpr) -> bool {
    expr_is_repeatable_with_context(expr, false)
}

/// 表达式作为普通单值操作数时，是否可以合并重复求值。
///
/// `HirExpr::VarArg` 在这里已经由逻辑/比较等外层表达式收成首个值，不再具有
/// value-pack tail 的展开宽度，因此同一函数调用中的两次读取稳定且无事件。
pub(crate) fn expr_is_repeatable_in_single_value_context(expr: &HirExpr) -> bool {
    expr_is_repeatable_with_context(expr, true)
}

fn expr_is_repeatable_with_context(expr: &HirExpr, single_value_vararg: bool) -> bool {
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
        HirExpr::VarArg => single_value_vararg,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            expr_is_repeatable_with_context(&unary.expr, single_value_vararg)
        }
        HirExpr::Binary(binary)
            if primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
                .is_some() =>
        {
            true
        }
        HirExpr::Binary(binary) if stable_literal_equality(binary.op, &binary.lhs, &binary.rhs) => {
            expr_is_repeatable_with_context(&binary.lhs, single_value_vararg)
                && expr_is_repeatable_with_context(&binary.rhs, single_value_vararg)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_repeatable_with_context(&logical.lhs, single_value_vararg)
                && expr_is_repeatable_with_context(&logical.rhs, single_value_vararg)
        }
        HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
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

/// 单值表达式的结果是否不会被夹在两次读取之间的任意 Lua 求值改写。
///
/// local、param 与 upvalue 都可能被中间调用经 closure capture 写入；temp 是 HIR
/// 已物化且 Lua 代码无法按名字访问的快照，vararg 则在函数入口固定。
pub(crate) fn expr_is_effect_invariant_in_single_value_context(expr: &HirExpr) -> bool {
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
        | HirExpr::TempRef(_)
        | HirExpr::VarArg => true,
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            expr_is_effect_invariant_in_single_value_context(&unary.expr)
        }
        HirExpr::Binary(binary)
            if primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
                .is_some() =>
        {
            true
        }
        HirExpr::Binary(binary) if stable_literal_equality(binary.op, &binary.lhs, &binary.rhs) => {
            expr_is_effect_invariant_in_single_value_context(&binary.lhs)
                && expr_is_effect_invariant_in_single_value_context(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_effect_invariant_in_single_value_context(&logical.lhs)
                && expr_is_effect_invariant_in_single_value_context(&logical.rhs)
        }
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
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
