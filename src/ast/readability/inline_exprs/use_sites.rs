//! 这个子模块负责 `inline_exprs` pass 的 use-site 重写。
//!
//! 它依赖 `candidate` 已经给好的候选类型和策略，只在允许的位置替换引用，不会回头重判
//! 候选本身是否安全。
//! 例如：`local r0 = print; r0(1)` 选中后，会在这里把调用位点改成 `print(1)`。

use crate::readability::ReadabilityOptions;

use super::super::super::common::{
    AstCallExpr, AstCallKind, AstExpr, AstGlobalDecl, AstLValue, AstMethodCallExpr, AstStmt,
    AstTableField, AstTableKey,
};
use super::super::binding_flow::name_matches_binding;
use super::super::expr_analysis::{
    expr_complexity, is_access_base_inline_expr, is_direct_return_constructor_inline_expr,
    is_mechanical_run_inline_expr,
};
use super::candidate::{
    InlineCandidate, InlinePolicy, is_call_callee_inline_expr,
    is_extended_call_arg_local_alias_expr, is_extended_neutral_local_alias_expr,
    is_lookup_inline_expr, is_raw_global_alias_expr, is_recallable_inline_expr,
};

pub(super) fn rewrite_stmt_use_sites_with_policy(
    stmt: &mut AstStmt,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => rewrite_expr_list_context(
            &mut local_decl.values,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::GlobalDecl(global_decl) => {
            rewrite_global_decl_use_sites(global_decl, candidate, replacement, options, policy)
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |=
                    rewrite_lvalue_use_sites(target, candidate, replacement, options, policy);
            }
            changed |= rewrite_expr_list_context(
                &mut assign.values,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstStmt::CallStmt(call_stmt) => {
            rewrite_call_use_sites(&mut call_stmt.call, candidate, replacement, options, policy)
        }
        AstStmt::Return(ret) => rewrite_expr_list_context(
            &mut ret.values,
            candidate,
            replacement,
            InlineSite::ReturnValue,
            options,
            policy,
        ),
        AstStmt::If(if_stmt) => rewrite_expr_use_sites(
            &mut if_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::While(while_stmt) => rewrite_expr_use_sites(
            &mut while_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::Repeat(repeat_stmt) => rewrite_expr_use_sites(
            &mut repeat_stmt.cond,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr_use_sites(
                &mut numeric_for.start,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.limit,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut numeric_for.step,
                candidate,
                replacement,
                InlineSite::Neutral,
                options,
                policy,
            );
            changed
        }
        AstStmt::GenericFor(generic_for) => rewrite_expr_list_context(
            &mut generic_for.iterator,
            candidate,
            replacement,
            InlineSite::Neutral,
            options,
            policy,
        ),
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) | AstStmt::Error(_) => false,
    }
}

fn rewrite_global_decl_use_sites(
    global_decl: &mut AstGlobalDecl,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    rewrite_expr_list_context(
        &mut global_decl.values,
        candidate,
        replacement,
        InlineSite::Neutral,
        options,
        policy,
    )
}

fn rewrite_expr_list_context(
    exprs: &mut [AstExpr],
    candidate: InlineCandidate,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    let mut changed = false;
    for expr in exprs {
        changed |=
            rewrite_top_level_expr_use_sites(expr, candidate, replacement, site, options, policy);
    }
    changed
}

fn rewrite_lvalue_use_sites(
    lvalue: &mut AstLValue,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            candidate,
            replacement,
            InlineSite::Neutral.descend_access_base(),
            options,
            policy,
        ),
        AstLValue::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                candidate,
                replacement,
                InlineSite::Neutral.descend_access_base(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                candidate,
                replacement,
                InlineSite::Index,
                options,
                policy,
            );
            changed
        }
    }
}

fn rewrite_call_use_sites(
    call: &mut AstCallKind,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match call {
        AstCallKind::Call(call) => {
            rewrite_call_expr_use_sites(call, candidate, replacement, options, policy, true)
        }
        AstCallKind::MethodCall(call) => {
            rewrite_method_call_expr_use_sites(call, candidate, replacement, options, policy, true)
        }
    }
}

fn rewrite_top_level_expr_use_sites(
    expr: &mut AstExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    match expr {
        AstExpr::Call(call) => {
            rewrite_call_expr_use_sites(call, candidate, replacement, options, policy, true)
        }
        AstExpr::MethodCall(call) => {
            rewrite_method_call_expr_use_sites(call, candidate, replacement, options, policy, true)
        }
        _ => rewrite_expr_use_sites(expr, candidate, replacement, site, options, policy),
    }
}

#[derive(Clone, Copy)]
struct CallRewriteMode {
    options: ReadabilityOptions,
    policy: InlinePolicy,
    allow_raw_global_adjacent_arg_inline: bool,
}

fn rewrite_call_expr_use_sites(
    call: &mut AstCallExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
    allow_raw_global_adjacent_arg_inline: bool,
) -> bool {
    rewrite_call_parts_use_sites(
        &mut call.callee,
        &mut call.args,
        InlineSite::CallCallee,
        candidate,
        replacement,
        CallRewriteMode {
            options,
            policy,
            allow_raw_global_adjacent_arg_inline,
        },
    )
}

fn rewrite_method_call_expr_use_sites(
    call: &mut AstMethodCallExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    options: ReadabilityOptions,
    policy: InlinePolicy,
    allow_raw_global_adjacent_arg_inline: bool,
) -> bool {
    rewrite_call_parts_use_sites(
        &mut call.receiver,
        &mut call.args,
        InlineSite::Neutral,
        candidate,
        replacement,
        CallRewriteMode {
            options,
            policy,
            allow_raw_global_adjacent_arg_inline,
        },
    )
}

fn rewrite_call_parts_use_sites(
    prefix: &mut AstExpr,
    args: &mut [AstExpr],
    prefix_site: InlineSite,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    mode: CallRewriteMode,
) -> bool {
    let mut changed = rewrite_expr_use_sites(
        prefix,
        candidate,
        replacement,
        prefix_site,
        mode.options,
        mode.policy,
    );
    let mut prefix_safe = mode.allow_raw_global_adjacent_arg_inline
        && call_prefix_base_allows_raw_global_arg_inline(mode.policy, replacement, prefix);
    let args_len = args.len();
    for (index, arg) in args.iter_mut().enumerate() {
        if prefix_safe && try_rewrite_raw_global_call_arg(arg, candidate, replacement) {
            changed = true;
        } else {
            changed |= rewrite_expr_use_sites(
                arg,
                candidate,
                replacement,
                call_arg_site(index, args_len),
                mode.options,
                mode.policy,
            );
        }
        prefix_safe &= raw_global_call_prefix_expr_is_barrier_free(arg);
    }
    changed
}

fn call_prefix_base_allows_raw_global_arg_inline(
    policy: InlinePolicy,
    replacement: &AstExpr,
    prefix: &AstExpr,
) -> bool {
    matches!(policy, InlinePolicy::AdjacentValueSink)
        && is_raw_global_alias_expr(replacement)
        && raw_global_call_prefix_expr_is_barrier_free(prefix)
}

fn raw_global_call_prefix_expr_is_barrier_free(expr: &AstExpr) -> bool {
    is_access_base_inline_expr(expr) || is_extended_call_arg_local_alias_expr(expr)
}

fn try_rewrite_raw_global_call_arg(
    arg: &mut AstExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
) -> bool {
    let AstExpr::Var(name) = arg else {
        return false;
    };
    if !name_matches_binding(name, candidate.binding()) {
        return false;
    }
    *arg = replacement.clone();
    true
}

fn rewrite_expr_use_sites(
    expr: &mut AstExpr,
    candidate: InlineCandidate,
    replacement: &AstExpr,
    site: InlineSite,
    options: ReadabilityOptions,
    policy: InlinePolicy,
) -> bool {
    if site.allows(candidate, expr, replacement, options, policy) {
        *expr = replacement.clone();
        return true;
    }

    match expr {
        AstExpr::FieldAccess(access) => rewrite_expr_use_sites(
            &mut access.base,
            candidate,
            replacement,
            site.descend_access_base(),
            options,
            policy,
        ),
        AstExpr::IndexAccess(access) => {
            let mut changed = rewrite_expr_use_sites(
                &mut access.base,
                candidate,
                replacement,
                site.descend_access_base(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut access.index,
                candidate,
                replacement,
                InlineSite::Index,
                options,
                policy,
            );
            changed
        }
        AstExpr::Unary(unary) => rewrite_expr_use_sites(
            &mut unary.expr,
            candidate,
            replacement,
            site.descend_value_expr(),
            options,
            policy,
        ),
        AstExpr::Binary(binary) => {
            let operand_site = match binary.op {
                super::super::super::common::AstBinaryOpKind::Eq
                | super::super::super::common::AstBinaryOpKind::Lt
                | super::super::super::common::AstBinaryOpKind::Le => InlineSite::ComparisonOperand,
                _ => site.descend_value_expr(),
            };
            let mut changed = rewrite_expr_use_sites(
                &mut binary.lhs,
                candidate,
                replacement,
                operand_site,
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut binary.rhs,
                candidate,
                replacement,
                operand_site,
                options,
                policy,
            );
            changed
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            let mut changed = rewrite_expr_use_sites(
                &mut logical.lhs,
                candidate,
                replacement,
                site.descend_value_expr(),
                options,
                policy,
            );
            changed |= rewrite_expr_use_sites(
                &mut logical.rhs,
                candidate,
                replacement,
                site.descend_value_expr(),
                options,
                policy,
            );
            changed
        }
        AstExpr::Call(call) => {
            rewrite_call_expr_use_sites(call, candidate, replacement, options, policy, false)
        }
        AstExpr::MethodCall(call) => {
            rewrite_method_call_expr_use_sites(call, candidate, replacement, options, policy, false)
        }
        AstExpr::SingleValue(expr) => rewrite_expr_use_sites(
            expr,
            candidate,
            replacement,
            site.descend_value_expr(),
            options,
            policy,
        ),
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_expr_use_sites(
                            value,
                            candidate,
                            replacement,
                            InlineSite::Neutral,
                            options,
                            policy,
                        );
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr_use_sites(
                                key,
                                candidate,
                                replacement,
                                InlineSite::Index,
                                options,
                                policy,
                            );
                        }
                        changed |= rewrite_expr_use_sites(
                            &mut record.value,
                            candidate,
                            replacement,
                            InlineSite::Neutral,
                            options,
                            policy,
                        );
                    }
                }
            }
            changed
        }
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
        | AstExpr::VarArg | AstExpr::Error(_) => false,
    }
}

#[derive(Clone, Copy)]
enum InlineSite {
    Neutral,
    ComparisonOperand,
    ReturnValue,
    ReturnNestedValue,
    Index,
    CallArgNonFinal,
    CallArgFinal,
    CallCallee,
    AccessBase,
}

impl InlineSite {
    fn allows(
        self,
        candidate: InlineCandidate,
        use_expr: &AstExpr,
        replacement: &AstExpr,
        options: ReadabilityOptions,
        policy: InlinePolicy,
    ) -> bool {
        if !matches!(use_expr, AstExpr::Var(name) if name_matches_binding(name, candidate.binding()))
        {
            return false;
        }

        let Some(limit) = self.complexity_limit(options, policy) else {
            return false;
        };
        if expr_complexity(replacement) > limit {
            return false;
        }

        match candidate {
            InlineCandidate::TempLike(_) => match policy {
                InlinePolicy::MechanicalRun => self.allows_mechanical_run_expr(replacement),
                InlinePolicy::DirectReturnConstructor => false,
                _ => {
                    !matches!(self, Self::AccessBase | Self::CallCallee)
                        || is_access_base_inline_expr(replacement)
                }
            },
            InlineCandidate::LocalAlias { origin, .. } => match policy {
                InlinePolicy::Conservative => match origin {
                    super::super::super::common::AstLocalOrigin::DebugHinted => {
                        matches!(self, Self::CallCallee | Self::AccessBase)
                            && is_access_base_inline_expr(replacement)
                    }
                    super::super::super::common::AstLocalOrigin::Recovered => match self {
                        Self::CallCallee | Self::AccessBase => {
                            is_access_base_inline_expr(replacement)
                                || is_lookup_inline_expr(replacement)
                        }
                        Self::ComparisonOperand => {
                            is_access_base_inline_expr(replacement)
                                || is_recallable_inline_expr(replacement)
                        }
                        Self::ReturnNestedValue => {
                            is_recallable_inline_expr(replacement)
                                || is_lookup_inline_expr(replacement)
                        }
                        _ => false,
                    },
                },
                InlinePolicy::ExtendedCallChain => self.allows_extended_local_alias(replacement),
                InlinePolicy::AliasInitializerChain => {
                    self.allows_alias_initializer_local_alias(replacement)
                }
                InlinePolicy::AdjacentCallResultCallee => {
                    self.allows_adjacent_call_result_local_alias(replacement)
                }
                InlinePolicy::AdjacentValueSink => match origin {
                    super::super::super::common::AstLocalOrigin::DebugHinted => false,
                    super::super::super::common::AstLocalOrigin::Recovered => {
                        self.allows_adjacent_value_sink_local_alias(replacement)
                    }
                },
                InlinePolicy::DirectReturnConstructor => match origin {
                    super::super::super::common::AstLocalOrigin::DebugHinted => false,
                    super::super::super::common::AstLocalOrigin::Recovered => {
                        self.allows_direct_return_constructor_local_alias(replacement)
                    }
                },
                InlinePolicy::MechanicalRun => match origin {
                    super::super::super::common::AstLocalOrigin::DebugHinted => false,
                    super::super::super::common::AstLocalOrigin::Recovered => {
                        self.allows_mechanical_run_expr(replacement)
                    }
                },
            },
        }
    }

    fn complexity_limit(self, options: ReadabilityOptions, policy: InlinePolicy) -> Option<usize> {
        match self {
            Self::Neutral => match policy {
                InlinePolicy::AliasInitializerChain => {
                    Some(options.access_base_inline_max_complexity)
                }
                InlinePolicy::AdjacentCallResultCallee => None,
                InlinePolicy::AdjacentValueSink => Some(options.return_inline_max_complexity),
                InlinePolicy::Conservative => None,
                InlinePolicy::DirectReturnConstructor => None,
                InlinePolicy::ExtendedCallChain => Some(options.access_base_inline_max_complexity),
                InlinePolicy::MechanicalRun => Some(options.return_inline_max_complexity),
            },
            Self::ComparisonOperand => Some(options.args_inline_max_complexity),
            Self::ReturnValue => match policy {
                InlinePolicy::DirectReturnConstructor => Some(usize::MAX),
                _ => Some(options.return_inline_max_complexity),
            },
            Self::ReturnNestedValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArgNonFinal | Self::CallArgFinal => Some(options.args_inline_max_complexity),
            // 这里刻意复用 access-base 的阈值：
            // `table.concat(tbl)` 这类“把别名还原回前缀表达式”的可读性取舍，
            // 本质上和 `obj[key]` 里的 base 折叠是同一种源码形状决策。
            Self::CallCallee => Some(options.access_base_inline_max_complexity),
            Self::AccessBase => Some(options.access_base_inline_max_complexity),
        }
    }

    fn descend_access_base(self) -> Self {
        match self {
            Self::Neutral => Self::AccessBase,
            Self::ComparisonOperand => Self::ComparisonOperand,
            Self::ReturnValue => Self::ReturnNestedValue,
            Self::ReturnNestedValue => Self::ReturnNestedValue,
            Self::Index | Self::CallArgNonFinal | Self::CallArgFinal | Self::AccessBase => {
                Self::Neutral
            }
            Self::CallCallee => Self::CallCallee,
        }
    }

    fn descend_value_expr(self) -> Self {
        match self {
            Self::ReturnValue | Self::ReturnNestedValue => Self::ReturnNestedValue,
            Self::ComparisonOperand => Self::ComparisonOperand,
            Self::Neutral
            | Self::Index
            | Self::CallArgNonFinal
            | Self::CallArgFinal
            | Self::CallCallee
            | Self::AccessBase => Self::Neutral,
        }
    }

    fn allows_extended_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral => is_extended_neutral_local_alias_expr(replacement),
            Self::ComparisonOperand => {
                is_extended_neutral_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            Self::ReturnNestedValue => {
                is_recallable_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::CallArgNonFinal => {
                is_extended_call_arg_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            // 这里只有在“局部别名包折回最终调用”时，才允许把纯 lookup 收回参数位。
            // 这能把 `local x = t[1]; local y = t.a; print(x, y)` 这类机械展开收回去，
            // 同时仍然不放宽到任意调用结果，避免把阶段 local 继续吞掉。
            Self::CallArgFinal => is_extended_call_arg_local_alias_expr(replacement),
            Self::AccessBase => is_access_base_inline_expr(replacement),
            Self::ReturnValue | Self::Index => false,
        }
    }

    fn allows_alias_initializer_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            // 这里专门服务“局部别名链初始化”：
            // `local unpack = table.unpack; local fn = unpack or _G.unpack`
            // 这种形状本质上还是在组装一个后续调用会消费的前缀表达式别名。
            // 允许它在紧邻的下一条 local alias 初始化式里收回，能把机械拆分重新压回
            // 更接近源码的单条声明，而不会放宽到普通 return/if/赋值上下文。
            Self::Neutral | Self::ComparisonOperand | Self::CallCallee => {
                is_access_base_inline_expr(replacement)
            }
            // 这里额外允许 lookup 落到 access base：
            // `local item = items[i]; local weight = item.weight`
            // 仍然只是把“取前缀再取字段”的机械两段式收回同一条 local 初始化。
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::ReturnValue
            | Self::ReturnNestedValue
            | Self::Index
            | Self::CallArgNonFinal
            | Self::CallArgFinal => false,
        }
    }

    fn allows_adjacent_call_result_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::CallCallee) && is_lookup_inline_expr(replacement)
    }

    fn allows_adjacent_value_sink_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral | Self::ComparisonOperand => {
                is_extended_neutral_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            Self::CallArgNonFinal | Self::CallArgFinal => {
                is_extended_call_arg_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            Self::ReturnNestedValue => {
                is_recallable_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::ReturnValue | Self::Index => false,
        }
    }

    fn allows_direct_return_constructor_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::ReturnValue) && is_direct_return_constructor_inline_expr(replacement)
    }

    fn allows_mechanical_run_expr(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral | Self::ComparisonOperand | Self::ReturnNestedValue | Self::Index => {
                is_mechanical_run_inline_expr(replacement)
            }
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::ReturnValue | Self::CallArgNonFinal | Self::CallArgFinal => false,
        }
    }
}

fn call_arg_site(index: usize, len: usize) -> InlineSite {
    if index + 1 == len {
        InlineSite::CallArgFinal
    } else {
        InlineSite::CallArgNonFinal
    }
}
