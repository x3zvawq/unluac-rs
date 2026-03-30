//! 这个子模块负责 `inline_exprs` pass 的候选识别和策略分类。
//!
//! 它依赖 AST 当前的赋值/local 形状与表达式分析，只回答“这一句能否当作 inline 候选”，
//! 不会在这里改写 use site。
//! 例如：`local r0 = print` 会在这里被识别成一个可继续审查的 local alias 候选。

use super::super::super::common::{
    AstAssign, AstBindingRef, AstExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstLocalOrigin,
    AstNameRef, AstStmt, AstTableField, AstTableKey,
};
use super::super::expr_analysis::{
    is_access_base_inline_expr, is_context_safe_expr, is_direct_return_constructor_inline_expr,
    is_lookup_inline_expr as is_lookup_expr, is_mechanical_run_inline_expr,
};

pub(super) fn inline_candidate(stmt: &AstStmt) -> Option<(InlineCandidate, &AstExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inline_candidate_from_assign(assign),
        AstStmt::LocalDecl(local_decl) => inline_candidate_from_local_decl(local_decl),
        _ => None,
    }
}

pub(super) fn stmt_is_alias_initializer_sink(stmt: &AstStmt) -> bool {
    matches!(
        inline_candidate(stmt),
        Some((InlineCandidate::LocalAlias { .. }, _))
    )
}

pub(super) fn stmt_is_adjacent_call_result_sink(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(expr_contains_direct_call_callee_var),
        AstStmt::Assign(assign) => assign
            .values
            .iter()
            .any(expr_contains_direct_call_callee_var),
        AstStmt::Return(ret) => ret.values.iter().any(expr_contains_direct_call_callee_var),
        AstStmt::GlobalDecl(_)
        | AstStmt::CallStmt(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

pub(super) fn stmt_is_direct_return_value_sink(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret) if matches!(ret.values.as_slice(), [AstExpr::Var(_)])
    )
}

#[derive(Clone, Copy)]
pub(super) enum InlineCandidate {
    TempLike(AstBindingRef),
    LocalAlias {
        binding: AstBindingRef,
        origin: AstLocalOrigin,
    },
}

#[derive(Clone, Copy)]
pub(super) enum InlinePolicy {
    Conservative,
    ExtendedCallChain,
    AliasInitializerChain,
    AdjacentCallResultCallee,
    DirectReturnConstructor,
    MechanicalRun,
}

impl InlineCandidate {
    pub(super) fn binding(self) -> AstBindingRef {
        match self {
            Self::TempLike(binding) => binding,
            Self::LocalAlias { binding, .. } => binding,
        }
    }

    pub(super) fn allows_expr_with_policy(self, expr: &AstExpr, policy: InlinePolicy) -> bool {
        match self {
            Self::TempLike(_) => match policy {
                InlinePolicy::MechanicalRun => is_mechanical_run_inline_expr(expr),
                InlinePolicy::DirectReturnConstructor => false,
                _ => is_inline_candidate_expr(expr),
            },
            // 这里故意不把普通 local 别名放宽到所有上下文：
            // 没有 debug 证据时，我们不能把用户可能主动写出来的局部语义名随手吞掉。
            // 目前只允许它们作为“前缀表达式别名”收回去，例如 `local concat = table.concat`。
            Self::LocalAlias {
                origin: AstLocalOrigin::DebugHinted,
                ..
            } => is_access_base_inline_expr(expr),
            Self::LocalAlias {
                origin: AstLocalOrigin::Recovered,
                ..
            } => match policy {
                InlinePolicy::MechanicalRun => is_mechanical_run_inline_expr(expr),
                InlinePolicy::AdjacentCallResultCallee => is_lookup_inline_expr(expr),
                InlinePolicy::DirectReturnConstructor => {
                    is_direct_return_constructor_inline_expr(expr)
                }
                InlinePolicy::AliasInitializerChain => {
                    is_access_base_inline_expr(expr)
                        || is_lookup_inline_expr(expr)
                        || is_recallable_inline_expr(expr)
                }
                InlinePolicy::Conservative | InlinePolicy::ExtendedCallChain => {
                    is_access_base_inline_expr(expr) || is_recallable_inline_expr(expr)
                }
            },
        }
    }
}

pub(super) fn is_lookup_inline_expr(expr: &AstExpr) -> bool {
    is_lookup_expr(expr)
}

pub(super) fn is_call_callee_inline_expr(expr: &AstExpr) -> bool {
    is_access_base_inline_expr(expr)
        || is_lookup_inline_expr(expr)
        || is_recallable_inline_expr(expr)
}

pub(super) fn is_extended_neutral_local_alias_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_lookup_inline_expr(expr)
}

pub(super) fn is_extended_call_arg_local_alias_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_lookup_inline_expr(expr)
}

pub(super) fn is_recallable_inline_expr(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Call(_) | AstExpr::MethodCall(_))
}

fn inline_candidate_from_assign(assign: &AstAssign) -> Option<(InlineCandidate, &AstExpr)> {
    let [AstLValue::Name(AstNameRef::Temp(temp))] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    Some((InlineCandidate::TempLike(AstBindingRef::Temp(*temp)), value))
}

fn inline_candidate_from_local_decl(
    local_decl: &AstLocalDecl,
) -> Option<(InlineCandidate, &AstExpr)> {
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None {
        return None;
    }
    let candidate = match binding.id {
        AstBindingRef::Temp(_) => InlineCandidate::TempLike(binding.id),
        AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => InlineCandidate::LocalAlias {
            binding: binding.id,
            origin: binding.origin,
        },
    };
    Some((candidate, value))
}

fn expr_contains_direct_call_callee_var(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Call(call) => matches!(call.callee, AstExpr::Var(_)),
        AstExpr::MethodCall(_) => false,
        AstExpr::SingleValue(expr) => expr_contains_direct_call_callee_var(expr),
        AstExpr::FieldAccess(access) => expr_contains_direct_call_callee_var(&access.base),
        AstExpr::IndexAccess(access) => {
            expr_contains_direct_call_callee_var(&access.base)
                || expr_contains_direct_call_callee_var(&access.index)
        }
        AstExpr::Unary(unary) => expr_contains_direct_call_callee_var(&unary.expr),
        AstExpr::Binary(binary) => {
            expr_contains_direct_call_callee_var(&binary.lhs)
                || expr_contains_direct_call_callee_var(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_contains_direct_call_callee_var(&logical.lhs)
                || expr_contains_direct_call_callee_var(&logical.rhs)
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_contains_direct_call_callee_var(value),
            AstTableField::Record(record) => {
                let key_has_call = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_contains_direct_call_callee_var(key),
                };
                key_has_call || expr_contains_direct_call_callee_var(&record.value)
            }
        }),
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn is_inline_candidate_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr) || is_access_base_inline_expr(expr)
}
