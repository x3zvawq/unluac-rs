//! 这个子模块负责 `inline_exprs` pass 的候选识别和策略分类。
//!
//! 它依赖 AST 当前的赋值/local 形状与表达式分析，只回答“这一句能否当作 inline 候选”，
//! 不会在这里改写 use site。
//! 例如：`local r0 = print` 会在这里被识别成一个可继续审查的 local alias 候选。

use super::super::super::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLocalAttr, AstLocalDecl, AstLocalOrigin, AstStmt,
    AstTableField, AstTableKey,
};
use super::super::expr_analysis::{
    is_access_base_inline_expr, is_context_safe_expr, is_direct_return_inline_expr,
    is_lookup_inline_expr as is_lookup_expr, is_mechanical_run_inline_expr,
    is_multi_return_inline_expr, is_raw_global_alias_expr as is_raw_global_expr,
    is_stable_copy_alias_expr,
};

pub(super) fn inline_candidate(stmt: &AstStmt) -> Option<(InlineCandidate, &AstExpr)> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => inline_candidate_from_local_decl(local_decl),
        _ => None,
    }
}

pub(super) fn stmt_is_alias_initializer_sink(stmt: &AstStmt) -> bool {
    inline_candidate(stmt).is_some()
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
        AstStmt::CallStmt(call_stmt) => matches!(
            &call_stmt.call,
            AstCallKind::Call(call) if matches!(call.callee, AstExpr::Var(_))
        ),
        AstStmt::GlobalDecl(_)
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
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

pub(super) fn stmt_is_direct_return_value_sink(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret) if matches!(ret.values.as_slice(), [AstExpr::Var(_)])
    )
}

pub(super) fn stmt_is_multi_return_value_sink(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret)
            if ret.values.len() > 1
                && ret.values.iter().any(
                    |value| matches!(value, AstExpr::Var(name) if binding.matches_name_ref(name))
                )
    )
}

/// 单值 `return` 的短路树是否在最左、必达位置读取该 binding。
///
/// 只有这个位置能保证把 producer 从相邻 local initializer 搬进 return 后仍然只求值
/// 一次；逻辑右臂会受前置 truthiness 控制，不能把可能触发比较协议的 producer 延后到那里。
pub(super) fn stmt_is_boolean_return_value_sink(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret)
            if matches!(ret.values.as_slice(), [value]
                if expr_has_unconditional_boolean_binding_use(value, binding))
    )
}

/// 终态查表值是否位于短路 return 的最左必达前缀，且其余逻辑尾部没有新的求值事件。
///
/// 这个比普通 boolean sink 更窄：查表结果会观察 lookup/元方法，只有在紧邻 return
/// 中先完成同一次 lookup，后续只剩 context-safe 的 truthiness/值读取时，才能证明把
/// local initializer 搬进表达式不会改变顺序或临时值的存活期。
pub(super) fn stmt_is_terminal_lookup_return_sink(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret)
            if matches!(ret.values.as_slice(), [value]
                if expr_has_terminal_lookup_binding_use(value, binding))
    )
}

fn expr_has_terminal_lookup_binding_use(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::Var(name) => binding.matches_name_ref(name),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_terminal_lookup_binding_use(&logical.lhs, binding)
                && is_context_safe_expr(&logical.rhs)
        }
        AstExpr::Unary(unary) if unary.op == super::super::super::common::AstUnaryOpKind::Not => {
            expr_has_terminal_lookup_binding_use(&unary.expr, binding)
        }
        AstExpr::SingleValue(inner) => expr_has_terminal_lookup_binding_use(inner, binding),
        _ => false,
    }
}

fn expr_has_unconditional_boolean_binding_use(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::Var(name) => binding.matches_name_ref(name),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_unconditional_boolean_binding_use(&logical.lhs, binding)
        }
        AstExpr::Unary(unary) if unary.op == super::super::super::common::AstUnaryOpKind::Not => {
            expr_has_unconditional_boolean_binding_use(&unary.expr, binding)
        }
        AstExpr::SingleValue(inner) => expr_has_unconditional_boolean_binding_use(inner, binding),
        _ => false,
    }
}

#[derive(Clone, Copy)]
pub(super) struct InlineCandidate {
    binding: AstBindingRef,
    origin: AstLocalOrigin,
}

#[derive(Clone, Copy)]
pub(super) enum InlinePolicy {
    Conservative,
    ExtendedCallChain,
    AliasInitializerChain,
    AdjacentCallResultCallee,
    AdjacentValueSink,
    DirectReturnValue,
    MultiReturnValue,
    BooleanReturnValue,
    MechanicalRun,
    LoopHeaderCall,
    /// 单次后续使用的稳定 local copy；不会重复 RHS，也不会移动 producer。
    StableCopy,
}

impl InlineCandidate {
    pub(super) fn binding(self) -> AstBindingRef {
        self.binding
    }

    pub(super) fn origin(self) -> AstLocalOrigin {
        self.origin
    }

    pub(super) fn allows_expr_with_policy(self, expr: &AstExpr, policy: InlinePolicy) -> bool {
        // debug local 明确表示源码中存在该 binding；把它内联掉会同时丢失名字和
        // 生命周期证据。编译器内部 for 槽已经在 Transformer 归一化时排除，因而这里
        // 可以完整保护 DebugHinted，普通 recovered alias 则继续按上下文收敛。
        match self.origin {
            AstLocalOrigin::DebugHinted => false,
            AstLocalOrigin::PhysicalRoot => {
                // 物理根若只是紧邻普通调用的全局 callee，调用帧会在参数求值期间继续
                // 持有同一函数值；把前置别名收回 callee 位不会缩短 GC 根，也不会改变
                // callee-before-argument 的求值顺序。其它物理根仍必须保留原声明。
                matches!(policy, InlinePolicy::AdjacentCallResultCallee)
                    && is_raw_global_alias_expr(expr)
            }
            AstLocalOrigin::Recovered => match policy {
                InlinePolicy::StableCopy => is_stable_copy_alias_expr(expr),
                InlinePolicy::MechanicalRun => is_mechanical_run_inline_expr(expr),
                InlinePolicy::AdjacentCallResultCallee => {
                    is_lookup_inline_expr(expr) || is_raw_global_alias_expr(expr)
                }
                InlinePolicy::AdjacentValueSink => {
                    is_extended_neutral_local_alias_expr(expr)
                        || is_recallable_inline_expr(expr)
                        || is_raw_global_alias_expr(expr)
                }
                InlinePolicy::DirectReturnValue => is_direct_return_inline_expr(expr),
                InlinePolicy::MultiReturnValue => is_multi_return_inline_expr(expr),
                InlinePolicy::BooleanReturnValue => {
                    is_multi_return_inline_expr(expr) || is_lookup_inline_expr(expr)
                }
                InlinePolicy::LoopHeaderCall => {
                    is_access_base_inline_expr(expr)
                        || is_lookup_inline_expr(expr)
                        || is_recallable_inline_expr(expr)
                        || is_raw_global_alias_expr(expr)
                        || super::super::expr_analysis::is_call_arg_constructor_inline_expr(expr)
                }
                InlinePolicy::AliasInitializerChain => {
                    is_access_base_inline_expr(expr)
                        || is_lookup_inline_expr(expr)
                        || is_recallable_inline_expr(expr)
                }
                InlinePolicy::Conservative => {
                    is_context_safe_expr(expr)
                        || is_access_base_inline_expr(expr)
                        || is_recallable_inline_expr(expr)
                }
                InlinePolicy::ExtendedCallChain => {
                    is_access_base_inline_expr(expr) || is_recallable_inline_expr(expr)
                }
            },
        }
    }
}

pub(super) fn is_lookup_inline_expr(expr: &AstExpr) -> bool {
    is_lookup_expr(expr)
}

pub(super) fn is_raw_global_alias_expr(expr: &AstExpr) -> bool {
    is_raw_global_expr(expr)
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
    match binding.id {
        AstBindingRef::Temp(_) => None,
        AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => Some((
            InlineCandidate {
                binding: binding.id,
                origin: binding.origin,
            },
            value,
        )),
    }
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
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}
