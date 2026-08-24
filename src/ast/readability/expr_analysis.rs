//! AST readability 里的共享表达式分析工具。
//!
//! 这些 helper 故意只回答“readability 是否值得继续收”的问题：
//! - 表达式复杂度
//! - 是否属于保守安全子集
//! - 是否是 copy-like / lookup-like / 机械纯值表达式
//! - 是否是能安全收回调用参数位的简单表构造
//!
//! 它们不试图替代更前层的语义分析，只给 AST readability 提供统一边界，
//! 避免各个 pass 再各写一套相似但略有偏差的判断。

use std::collections::BTreeSet;

use super::super::common::{
    AstBinaryOpKind, AstExpr, AstNameRef, AstTableField, AstTableKey, AstUnaryOpKind,
};

/// 只计算同类型原始字面量比较。
///
/// 这份证明与 HIR 的同名规则保持一致：不跨数值表示，不触碰 cdata/vector/complex，
/// 也不把非有限 number 当成无运行时事件的字面量。调用方只能把 `Some` 当作可安全
/// 删除比较壳的事实，`None` 必须保留原表达式。
pub(super) fn primitive_literal_comparison_value(
    op: AstBinaryOpKind,
    lhs: &AstExpr,
    rhs: &AstExpr,
) -> Option<bool> {
    if op == AstBinaryOpKind::Eq {
        return match (lhs, rhs) {
            (AstExpr::Integer(lhs), AstExpr::Integer(rhs)) => Some(lhs == rhs),
            (AstExpr::Number(lhs), AstExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
                Some(lhs == rhs)
            }
            (AstExpr::String(lhs), AstExpr::String(rhs)) => Some(lhs == rhs),
            (AstExpr::Boolean(lhs), AstExpr::Boolean(rhs)) => Some(lhs == rhs),
            (AstExpr::Nil, AstExpr::Nil) => Some(true),
            _ => None,
        };
    }

    let ordering = match (lhs, rhs) {
        (AstExpr::Integer(lhs), AstExpr::Integer(rhs)) => lhs.cmp(rhs),
        (AstExpr::Number(lhs), AstExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
            lhs.partial_cmp(rhs)?
        }
        (AstExpr::String(lhs), AstExpr::String(rhs)) => lhs.cmp(rhs),
        _ => return None,
    };
    match op {
        AstBinaryOpKind::Lt => Some(ordering == std::cmp::Ordering::Less),
        AstBinaryOpKind::Le => Some(ordering != std::cmp::Ordering::Greater),
        _ => None,
    }
}

/// 表达式是否保证只产生布尔值。
pub(super) fn expr_is_boolean_valued(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Boolean(_) => true,
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => true,
        AstExpr::Binary(binary) => matches!(
            binary.op,
            AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le
        ),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_is_boolean_valued(&logical.lhs) && expr_is_boolean_valued(&logical.rhs)
        }
        AstExpr::SingleValue(inner) => expr_is_boolean_valued(inner),
        _ => false,
    }
}

pub(super) fn expr_complexity(expr: &AstExpr) -> usize {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => 1,
        AstExpr::Unary(unary) => 1 + expr_complexity(&unary.expr),
        AstExpr::Binary(binary) => 1 + expr_complexity(&binary.lhs) + expr_complexity(&binary.rhs),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            1 + expr_complexity(&logical.lhs) + expr_complexity(&logical.rhs)
        }
        AstExpr::FieldAccess(access) => 1 + expr_complexity(&access.base),
        AstExpr::IndexAccess(access) => {
            1 + expr_complexity(&access.base) + expr_complexity(&access.index)
        }
        AstExpr::Call(call) => {
            1 + expr_complexity(&call.callee) + call.args.iter().map(expr_complexity).sum::<usize>()
        }
        AstExpr::MethodCall(call) => {
            1 + expr_complexity(&call.receiver)
                + call.args.iter().map(expr_complexity).sum::<usize>()
        }
        AstExpr::SingleValue(expr) => 1 + expr_complexity(expr),
        AstExpr::TableConstructor(table) => {
            1 + table
                .fields
                .iter()
                .map(|field| match field {
                    AstTableField::Array(value) => expr_complexity(value),
                    AstTableField::Record(record) => {
                        let key_cost = match &record.key {
                            AstTableKey::Name(_) => 1,
                            AstTableKey::Expr(key) => expr_complexity(key),
                        };
                        key_cost + expr_complexity(&record.value)
                    }
                })
                .sum::<usize>()
        }
        AstExpr::FunctionExpr(function) => 1 + function.body.stmts.len(),
    }
}

pub(super) fn is_context_safe_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_),
        ) => true,
        AstExpr::Unary(unary) => {
            matches!(unary.op, super::super::common::AstUnaryOpKind::Not)
                && is_context_safe_expr(&unary.expr)
        }
        AstExpr::SingleValue(expr) => is_context_safe_expr(expr),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_context_safe_expr(&logical.lhs) && is_context_safe_expr(&logical.rhs)
        }
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

pub(super) fn expr_observes_eval_order(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_) => true,
        AstExpr::Unary(_) | AstExpr::Binary(_) | AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_) => {
            true
        }
        AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_) => true,
        AstExpr::SingleValue(expr) => expr_observes_eval_order(expr),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_),
        )
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

/// 表达式结果是否是必须保留读取时点的值快照。
pub(super) fn expr_requires_ordered_snapshot(
    expr: &AstExpr,
    mutable_snapshots: &BTreeSet<AstNameRef>,
) -> bool {
    expr_observes_eval_order(expr)
        || matches!(expr, AstExpr::Var(AstNameRef::Upvalue(_)))
        || matches!(expr, AstExpr::Var(name) if mutable_snapshots.contains(name))
        || matches!(
            expr,
            AstExpr::SingleValue(inner)
                if expr_requires_ordered_snapshot(inner, mutable_snapshots)
        )
}

pub(super) fn is_stable_inline_value(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::SingleValue(inner) => is_stable_inline_value(inner),
        AstExpr::Var(_)
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

pub(super) fn is_access_base_inline_expr(expr: &AstExpr) -> bool {
    is_atomic_access_base_expr(expr) || is_named_field_chain_expr(expr)
}

pub(super) fn is_raw_global_alias_expr(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Var(AstNameRef::Global(_)))
}

pub(super) fn is_lookup_inline_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => {
            is_atomic_access_base_expr(&access.base) || is_lookup_inline_expr(&access.base)
        }
        AstExpr::IndexAccess(access) => {
            (is_atomic_access_base_expr(&access.base) || is_lookup_inline_expr(&access.base))
                && is_context_safe_expr(&access.index)
        }
        _ => false,
    }
}

pub(super) fn is_copy_like_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_) => true,
        AstExpr::SingleValue(expr) => is_copy_like_expr(expr),
        AstExpr::FieldAccess(access) => is_copy_like_expr(&access.base),
        AstExpr::IndexAccess(access) => {
            is_copy_like_expr(&access.base) && is_copy_like_expr(&access.index)
        }
        AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// A direct local copy or primitive Lua literal has no expression-level work to repeat.
///
/// This is intentionally narrower than [`is_copy_like_expr`].  The latter is used by
/// run-level heuristics and also accepts dialect-specific literals and lookup-shaped
/// expressions. Int64/UInt64/Vector/Complex stay excluded because materializing those
/// can create a cdata/vector value rather than merely load a primitive Lua constant;
/// non-finite numbers are emitted as division expressions and therefore are not event-free.
pub(super) fn is_stable_copy_alias_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Number(value) => value.is_finite(),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::String(_)
        | AstExpr::Var(AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_)) => true,
        _ => false,
    }
}

pub(super) fn is_discard_safe_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_),
        ) => true,
        AstExpr::SingleValue(expr) => is_discard_safe_expr(expr),
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

pub(super) fn is_mechanical_run_inline_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_) => true,
        AstExpr::SingleValue(expr) => is_mechanical_run_inline_expr(expr),
        AstExpr::FieldAccess(access) => is_mechanical_run_inline_expr(&access.base),
        AstExpr::IndexAccess(access) => {
            is_mechanical_run_inline_expr(&access.base)
                && is_mechanical_run_inline_expr(&access.index)
        }
        AstExpr::Unary(unary) => is_mechanical_run_inline_expr(&unary.expr),
        AstExpr::Binary(binary) => {
            is_mechanical_run_inline_expr(&binary.lhs) && is_mechanical_run_inline_expr(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_mechanical_run_inline_expr(&logical.lhs)
                && is_mechanical_run_inline_expr(&logical.rhs)
        }
        AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// 直接终态 return 能否消费该表达式而不展开额外返回值。
///
/// `local value = expr; return value` 的 local initializer 处于目标计数上下文，
/// 因此裸 `Call` / `MethodCall` / `VarArg` 在移到 return 后可能从单值变成多值；
/// `SingleValue` 则是 lowering 已经保留的单值边界。其它 AST 表达式在运算、访问、
/// 构造器或函数表达式位置都只产出一个值。`Error` 继续保留为 residual，避免把未知
/// 语义伪装成可读源码。
pub(super) fn is_direct_return_inline_expr(expr: &AstExpr) -> bool {
    !matches!(
        expr,
        AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg | AstExpr::Error(_)
    )
}

/// 多值 `return` 中可安全收回的单值表达式。
///
/// 现有的 context-safe 子集已经覆盖不会观察运行时事件的表达式。额外放行的只有
/// “比较结果为布尔值”的表达式树，且比较操作数仍必须属于 context-safe 子集（或是
/// 已处于单值比较操作数语境的 vararg）；这样
/// 比较本身即使触发 Lua 的比较协议，也不会把对象结果从 local root 搬到别的求值点，
/// 并且不会产生多返回值。短路/`not` 只在整棵树仍保证布尔结果时递归接受。
pub(super) fn is_multi_return_inline_expr(expr: &AstExpr) -> bool {
    if is_context_safe_expr(expr) {
        return true;
    }
    if !expr_is_boolean_valued(expr) {
        return false;
    }
    match expr {
        AstExpr::Binary(binary)
            if matches!(
                binary.op,
                AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le
            ) =>
        {
            is_multi_return_comparison_operand(&binary.lhs)
                && is_multi_return_comparison_operand(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_multi_return_inline_expr(&logical.lhs) && is_multi_return_inline_expr(&logical.rhs)
        }
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            is_multi_return_inline_expr(&unary.expr)
        }
        AstExpr::SingleValue(inner) => is_multi_return_inline_expr(inner),
        _ => false,
    }
}

fn is_multi_return_comparison_operand(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr)
        || matches!(expr, AstExpr::VarArg)
        || matches!(expr, AstExpr::SingleValue(inner) if matches!(inner.as_ref(), AstExpr::VarArg))
}

pub(super) fn is_call_arg_constructor_inline_expr(expr: &AstExpr) -> bool {
    let AstExpr::TableConstructor(table) = expr else {
        return false;
    };
    table.fields.iter().all(|field| match field {
        AstTableField::Array(value) => is_call_arg_constructor_field_expr(value),
        AstTableField::Record(record) => {
            let key_is_safe = match &record.key {
                AstTableKey::Name(_) => true,
                AstTableKey::Expr(key) => is_context_safe_expr(key) || is_lookup_inline_expr(key),
            };
            key_is_safe && is_call_arg_constructor_field_expr(&record.value)
        }
    })
}

fn is_call_arg_constructor_field_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr)
        || is_lookup_inline_expr(expr)
        || is_call_arg_constructor_inline_expr(expr)
}

fn is_named_field_chain_expr(expr: &AstExpr) -> bool {
    let AstExpr::FieldAccess(access) = expr else {
        return false;
    };
    is_atomic_access_base_expr(&access.base) || is_named_field_chain_expr(&access.base)
}

fn is_atomic_access_base_expr(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Vector(_)
            | AstExpr::Complex { .. }
            | AstExpr::Var(_)
    )
}
