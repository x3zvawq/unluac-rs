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
    stmt_contains_direct_call_callee(stmt, None)
}

pub(super) fn stmt_uses_binding_as_direct_call_callee(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> bool {
    stmt_contains_direct_call_callee(stmt, Some(binding))
}

fn stmt_contains_direct_call_callee(stmt: &AstStmt, binding: Option<AstBindingRef>) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|expr| expr_contains_direct_call_callee_var(expr, binding)),
        AstStmt::Assign(assign) => assign
            .values
            .iter()
            .any(|expr| expr_contains_direct_call_callee_var(expr, binding)),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|expr| expr_contains_direct_call_callee_var(expr, binding)),
        AstStmt::CallStmt(call_stmt) => match &call_stmt.call {
            AstCallKind::Call(call) => {
                matches!(&call.callee, AstExpr::Var(name)
                    if binding.is_none_or(|binding| binding.matches_name_ref(name)))
                    || binding.is_some_and(|binding| {
                        expr_contains_direct_call_callee_var(&call.callee, Some(binding))
                            || call
                                .args
                                .iter()
                                .any(|arg| expr_contains_direct_call_callee_var(arg, Some(binding)))
                    })
            }
            AstCallKind::MethodCall(call) => binding.is_some_and(|binding| {
                expr_contains_direct_call_callee_var(&call.receiver, Some(binding))
                    || call
                        .args
                        .iter()
                        .any(|arg| expr_contains_direct_call_callee_var(arg, Some(binding)))
            }),
        },
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
                && stmt_has_top_level_return_binding_use(stmt, binding)
    )
}

pub(super) fn stmt_has_top_level_return_binding_use(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> bool {
    matches!(
        stmt,
        AstStmt::Return(ret)
            if ret.values.iter().any(
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
    initializer_may_affect_collectable_lifetime: bool,
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
    /// 同一语句内使用的稳定 local copy；不会重复有事件的 RHS，也不会移动 producer。
    StableCopy,
}

#[derive(Clone, Copy)]
pub(super) enum InlineExprRejection {
    DebugScope,
    Lifetime,
    PolicyMismatch,
}

impl InlineCandidate {
    pub(super) fn binding(self) -> AstBindingRef {
        self.binding
    }

    pub(super) fn origin(self) -> AstLocalOrigin {
        self.origin
    }

    pub(super) fn initializer_may_affect_collectable_lifetime(self) -> bool {
        self.initializer_may_affect_collectable_lifetime
    }

    pub(super) fn expr_rejection_with_policy(
        self,
        expr: &AstExpr,
        policy: InlinePolicy,
    ) -> Option<InlineExprRejection> {
        // debug local 明确表示源码中存在该 binding；把它内联掉会同时丢失名字和
        // 生命周期证据。编译器内部 for 槽已经在 Transformer 归一化时排除，因而这里
        // 可以完整保护 DebugHinted，普通 recovered alias 则继续按上下文收敛。
        match self.origin {
            AstLocalOrigin::DebugHinted | AstLocalOrigin::DebugHintedPhysicalRoot => {
                Some(InlineExprRejection::DebugScope)
            }
            AstLocalOrigin::PhysicalRoot => {
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 证明原 VM home 在最后一次
                // 表达式读取后仍须独立存活；callee operand 只保活到调用返回，不能据 raw
                // global 的 AST 形状推断两者终点相同（regress_419）。
                Some(InlineExprRejection::Lifetime)
            }
            AstLocalOrigin::Recovered => (!match policy {
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
                InlinePolicy::ExtendedCallChain => is_extended_call_chain_inline_expr(expr),
            })
            .then_some(InlineExprRejection::PolicyMismatch),
        }
    }

    pub(super) fn allows_expr_with_policy(self, expr: &AstExpr, policy: InlinePolicy) -> bool {
        self.expr_rejection_with_policy(expr, policy).is_none()
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

pub(super) fn is_extended_call_chain_inline_expr(expr: &AstExpr) -> bool {
    is_access_base_inline_expr(expr) || is_recallable_inline_expr(expr)
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
    if !local_attr_belongs_to_inline_pipeline(binding.attr) {
        return None;
    }
    if binding.rewrite_authority.must_preserve() {
        // 候选拒绝[LayerBoundary]：HIR 已证明删除这个 binding 会破坏底层生命周期或
        // value epoch。AST 只消费该结论，不根据当前 Lua 语法形状重新打开候选。
        return None;
    }
    match binding.id {
        // 候选拒绝[LayerBoundary]：Normal inline-exprs 不把原生 TempId 当作源码 local；
        // Deferred materialize-temps 把残留 temp 建成 SyntheticLocal，并发出 TempPresence、
        // BindingStructure 与 StatementAdjacency。调度器因此回到 Normal phase，cleanup
        // 先清理新声明，inline-exprs 再以 SyntheticLocal candidate 重审。
        AstBindingRef::Temp(_) => None,
        AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_) => Some((
            InlineCandidate {
                binding: binding.id,
                origin: binding.origin,
                initializer_may_affect_collectable_lifetime: local_decl
                    .initializer_root_profile
                    .as_ref()
                    .is_none_or(|profile| profile.may_affect_collectable_lifetime(0)),
            },
            value,
        )),
    }
}

pub(in crate::ast::readability) fn local_attr_belongs_to_inline_pipeline(
    attr: AstLocalAttr,
) -> bool {
    match attr {
        AstLocalAttr::None => true,
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：内联 `<close>` 会删除离开作用域时的关闭动作。
            false
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：`<const>` 的声明身份按源码保真策略保留；当前变换并不需要靠它阻止运行时不等价。
            false
        }
    }
}

fn expr_contains_direct_call_callee_var(expr: &AstExpr, binding: Option<AstBindingRef>) -> bool {
    match expr {
        AstExpr::IfExpr(branch) => [&branch.cond, &branch.then_expr, &branch.else_expr]
            .into_iter()
            .any(|expr| expr_contains_direct_call_callee_var(expr, binding)),
        AstExpr::Call(call) => {
            matches!(&call.callee, AstExpr::Var(name)
                if binding.is_none_or(|binding| binding.matches_name_ref(name)))
                || binding.is_some_and(|binding| {
                    expr_contains_direct_call_callee_var(&call.callee, Some(binding))
                        || call
                            .args
                            .iter()
                            .any(|arg| expr_contains_direct_call_callee_var(arg, Some(binding)))
                })
        }
        AstExpr::MethodCall(call) => binding.is_some_and(|binding| {
            expr_contains_direct_call_callee_var(&call.receiver, Some(binding))
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_direct_call_callee_var(arg, Some(binding)))
        }),
        AstExpr::SingleValue(expr) => expr_contains_direct_call_callee_var(expr, binding),
        AstExpr::FieldAccess(access) => expr_contains_direct_call_callee_var(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            expr_contains_direct_call_callee_var(&access.base, binding)
                || expr_contains_direct_call_callee_var(&access.index, binding)
        }
        AstExpr::Unary(unary) => expr_contains_direct_call_callee_var(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            expr_contains_direct_call_callee_var(&binary.lhs, binding)
                || expr_contains_direct_call_callee_var(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_contains_direct_call_callee_var(&logical.lhs, binding)
                || expr_contains_direct_call_callee_var(&logical.rhs, binding)
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_contains_direct_call_callee_var(value, binding),
            AstTableField::Record(record) => {
                let key_has_call = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_contains_direct_call_callee_var(key, binding),
                };
                key_has_call || expr_contains_direct_call_callee_var(&record.value, binding)
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
        | AstExpr::CaptureInitializer(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}
