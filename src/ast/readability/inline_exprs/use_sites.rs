//! 这个子模块负责 `inline_exprs` pass 的 use-site 重写。
//!
//! 它依赖 `candidate` 已经给好的候选类型和策略，只在允许的位置替换引用，不会回头重判
//! 候选本身是否安全。
//! 例如：`local r0 = print; r0(1)` 选中后，会在这里把调用位点改成 `print(1)`。
//! mechanical run 的顶层 return 复用候选层的单值表达式集合；extended call run 在
//! 非尾 return 复用候选集合并由 run 级事件前缀约束顺序，index 则保留跨调用的 key root。
//! local initializer 中的裸调用已经被赋值收窄为单值；移入最终调用参数时用
//! `SingleValue` 保留该宽度，避免重新变成开放多返回值。

use crate::ast::ReadabilityOptions;

use super::super::super::common::{
    AstCallExpr, AstCallKind, AstExpr, AstGlobalDecl, AstLValue, AstMethodCallExpr, AstStmt,
    AstTableField, AstTableKey,
};
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::{
    direct_return_concat_cost, direct_return_logical_cost, expr_complexity,
    is_access_base_inline_expr, is_call_arg_constructor_inline_expr, is_context_safe_expr,
    is_direct_return_inline_expr, is_mechanical_run_inline_expr, is_multi_return_inline_expr,
    is_stable_copy_alias_expr,
};
use super::candidate::{
    InlineCandidate, InlinePolicy, is_call_callee_inline_expr,
    is_extended_call_arg_local_alias_expr, is_extended_call_chain_inline_expr,
    is_extended_neutral_local_alias_expr, is_lookup_inline_expr, is_raw_global_alias_expr,
    is_recallable_inline_expr,
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
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
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
        *expr = site.replacement_preserving_value_width(replacement);
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
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
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
    fn replacement_preserving_value_width(self, replacement: &AstExpr) -> AstExpr {
        if matches!(self, Self::CallArgFinal) && is_recallable_inline_expr(replacement) {
            AstExpr::SingleValue(Box::new(replacement.clone()))
        } else {
            replacement.clone()
        }
    }

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

        let Some(limit) = self.complexity_limit(options, policy, replacement) else {
            // 候选拒绝[ProofIncomplete]：该 policy/site 组合尚无位置级值宽度与求值顺序证明；不能因找到同名 use 就直接替换。
            return false;
        };
        let complexity_ok = expr_complexity(replacement) <= limit
            || (matches!(self, Self::ReturnValue)
                && matches!(policy, InlinePolicy::DirectReturnValue)
                && direct_return_concat_cost(replacement)
                    .is_some_and(|cost| cost <= options.return_inline_max_complexity))
            || (matches!(self, Self::ReturnValue)
                && matches!(policy, InlinePolicy::DirectReturnValue)
                && direct_return_logical_cost(replacement)
                    .is_some_and(|cost| cost <= options.return_inline_max_complexity));
        if !complexity_ok {
            // 候选拒绝[PolicyBoundary]：表达式超过用户配置的 index/arg/access-base/return 展示预算；这是源码密度选择，不是语义不等价证明。
            return false;
        }

        match policy {
            InlinePolicy::StableCopy => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && is_stable_copy_alias_expr(replacement)
            }
            InlinePolicy::Conservative => match candidate.origin() {
                // 候选拒绝[SemanticBarrier:DebugScope]：删除 debug local 会改变 debug.getlocal 可观察的作用域（regress_351）；候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 可能被弱表/`__gc` 观察，不能走通用 use-site 内联。
                super::super::super::common::AstLocalOrigin::DebugHinted
                | super::super::super::common::AstLocalOrigin::PhysicalRoot => false,
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
                        is_context_safe_expr(replacement)
                            || is_recallable_inline_expr(replacement)
                            || is_lookup_inline_expr(replacement)
                    }
                    Self::ReturnValue => is_context_safe_expr(replacement),
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
            InlinePolicy::AdjacentValueSink => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && self.allows_adjacent_value_sink_local_alias(replacement)
            }
            InlinePolicy::LoopHeaderCall => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && self.allows_loop_header_call_local_alias(replacement)
            }
            InlinePolicy::DirectReturnValue => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && self.allows_direct_return_value_local_alias(replacement)
            }
            InlinePolicy::MultiReturnValue => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && self.allows_multi_return_value_local_alias(replacement)
            }
            InlinePolicy::BooleanReturnValue => {
                candidate.origin() == super::super::super::common::AstLocalOrigin::Recovered
                    && self.allows_boolean_return_value_local_alias(replacement)
            }
            InlinePolicy::MechanicalRun => self.allows_mechanical_run_expr(replacement),
        }
    }

    fn complexity_limit(
        self,
        options: ReadabilityOptions,
        policy: InlinePolicy,
        replacement: &AstExpr,
    ) -> Option<usize> {
        match self {
            Self::Neutral => match policy {
                InlinePolicy::StableCopy => Some(options.return_inline_max_complexity),
                InlinePolicy::AliasInitializerChain => {
                    Some(options.access_base_inline_max_complexity)
                }
                InlinePolicy::AdjacentCallResultCallee => None,
                InlinePolicy::AdjacentValueSink => Some(options.return_inline_max_complexity),
                InlinePolicy::Conservative => None,
                InlinePolicy::DirectReturnValue => None,
                InlinePolicy::MultiReturnValue => None,
                InlinePolicy::BooleanReturnValue => Some(options.return_inline_max_complexity),
                InlinePolicy::ExtendedCallChain => Some(options.access_base_inline_max_complexity),
                InlinePolicy::LoopHeaderCall => Some(options.return_inline_max_complexity),
                InlinePolicy::MechanicalRun => Some(options.return_inline_max_complexity),
            },
            Self::ComparisonOperand => Some(options.args_inline_max_complexity),
            Self::ReturnValue => match policy {
                InlinePolicy::StableCopy => Some(options.return_inline_max_complexity),
                InlinePolicy::DirectReturnValue => {
                    if matches!(replacement, AstExpr::TableConstructor(_)) {
                        Some(usize::MAX)
                    } else {
                        Some(options.return_inline_max_complexity)
                    }
                }
                InlinePolicy::MultiReturnValue => Some(options.return_inline_max_complexity),
                InlinePolicy::BooleanReturnValue => Some(options.return_inline_max_complexity),
                _ => Some(options.return_inline_max_complexity),
            },
            Self::ReturnNestedValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArgNonFinal | Self::CallArgFinal => match policy {
                InlinePolicy::StableCopy => Some(options.args_inline_max_complexity),
                InlinePolicy::LoopHeaderCall => Some(usize::MAX),
                // MechanicalRun 已经证明这一组相邻 local 只服务于同一个消费点；
                // 这里适度放宽到 return 阈值，让长 lookup 迭代器不会残留成两行脚手架。
                InlinePolicy::MechanicalRun => Some(options.return_inline_max_complexity),
                _ => Some(options.args_inline_max_complexity),
            },
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
            // 调用参数中的 field access base 用 AccessBase 而非 Neutral：
            // `f(r.KEY)` 内联 `r = T.F` 只是把 call arg 从 `r.KEY` 延长成 `T.F.KEY`，
            // 仍然是同类型的命名字段链，不会引入新的副作用或可读性退化。
            Self::CallArgNonFinal | Self::CallArgFinal => Self::AccessBase,
            Self::Index | Self::AccessBase => Self::Neutral,
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
                    || is_call_arg_constructor_inline_expr(replacement)
            }
            // 最终参数只接受不会重新打开返回值的 lookup/constructor。
            Self::CallArgFinal => {
                is_extended_call_arg_local_alias_expr(replacement)
                    || is_call_arg_constructor_inline_expr(replacement)
            }
            Self::AccessBase => is_access_base_inline_expr(replacement),
            // terminal call run 的直接 return use 必然位于最终 tail call 之前；local
            // 初始化与非尾 return 都把裸 call 收窄为单值，完整事件顺序再由 run 前缀证明。
            Self::ReturnValue => is_extended_call_chain_inline_expr(replacement),
            Self::Index => {
                // 候选拒绝[LayerBoundary]：primitive/copy-like index alias 由 stable-copy 或 HIR locals 消费；候选拒绝[SemanticBarrier:Lifetime]：把 call/method/field 结果移入 index 会让 key root 在参数求值前失活，弱表与强制 GC 可观察差异（regress_353_extended_index_key_lifetime）。
                false
            }
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
            | Self::CallArgFinal => {
                // 候选拒绝[LayerBoundary]：alias-initializer 策略只拥有紧邻 initializer 内部，return/index/call 参数由其它 sink policy 证明。
                false
            }
        }
    }

    fn allows_adjacent_call_result_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::CallCallee)
            && (is_lookup_inline_expr(replacement) || is_raw_global_alias_expr(replacement))
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
            Self::ReturnValue => {
                // 候选拒绝[LayerBoundary]：直接 return 由 DirectReturnValue/MultiReturnValue/
                // BooleanReturnValue policy 负责，AdjacentValueSink 不拥有该站点。
                false
            }
            Self::Index => {
                // 候选拒绝[ProofIncomplete]：index 位置仍缺 base 求值顺序与 key root
                // lifetime 的联合证明，不能把 call/lookup 结果直接移入索引。
                false
            }
        }
    }

    fn allows_loop_header_call_local_alias(self, replacement: &AstExpr) -> bool {
        match self {
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::CallArgNonFinal | Self::CallArgFinal => {
                is_extended_call_arg_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
                    || is_call_arg_constructor_inline_expr(replacement)
            }
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::Neutral | Self::ComparisonOperand | Self::ReturnNestedValue => {
                is_extended_neutral_local_alias_expr(replacement)
                    || is_recallable_inline_expr(replacement)
            }
            // 候选拒绝[LayerBoundary]：loop-header policy 只服务循环头；return/index 由各自 sink policy 判断。
            Self::ReturnValue | Self::Index => false,
        }
    }

    fn allows_direct_return_value_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::ReturnValue) && is_direct_return_inline_expr(replacement)
    }

    fn allows_multi_return_value_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::ReturnValue) && is_multi_return_inline_expr(replacement)
    }

    fn allows_boolean_return_value_local_alias(self, replacement: &AstExpr) -> bool {
        matches!(self, Self::ReturnNestedValue | Self::ReturnValue)
            && (is_multi_return_inline_expr(replacement) || is_lookup_inline_expr(replacement))
    }

    fn allows_mechanical_run_expr(self, replacement: &AstExpr) -> bool {
        match self {
            Self::Neutral
            | Self::ComparisonOperand
            | Self::ReturnValue
            | Self::ReturnNestedValue
            | Self::Index => is_mechanical_run_inline_expr(replacement),
            Self::CallCallee => is_call_callee_inline_expr(replacement),
            Self::AccessBase => {
                is_access_base_inline_expr(replacement) || is_lookup_inline_expr(replacement)
            }
            Self::CallArgNonFinal | Self::CallArgFinal => {
                is_mechanical_run_inline_expr(replacement)
            }
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
