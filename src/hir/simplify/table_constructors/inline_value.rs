//! 这个子模块负责把构造器生产者内联进字段值。
//!
//! 它依赖 `bindings` 已经识别好的同一绑定和 pending producer 列表，只尝试安全内联字段/
//! callee/access-base 值，不会在这里决定整段 region 的分段边界。
//! producer 只有一个消费 owner；内联同时记录其求值事件，region builder 证明事件顺序
//! 未变后才提交。例如：`local v = f(); t.x = v` 只在 `f()` 仍位于同一事件位置时折叠。

use crate::hir::common::{
    HirBinaryExpr, HirBlock, HirCallExpr, HirDecisionTarget, HirExpr, HirLogicalExpr, HirPackTail,
    HirTableField, HirTableKey, HirUnaryExpr, HirValuePack,
};
use crate::hir::expr_safety::expr_requires_ordered_snapshot;

use super::bindings::{BindingIndex, BindingUseSummary, binding_from_expr};
use super::{BindingId, ConstructorEvalEvent, PendingProducer, PendingProducerSource};

pub(super) struct InlineContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    pending_producers: &'a [PendingProducer],
    producer_index_by_binding: &'a [Option<usize>],
    consumed_bindings: &'a mut [bool],
    consumed_groups: &'a mut [bool],
    eval_events: &'a mut Vec<ConstructorEvalEvent>,
    inside_producer_value: bool,
    remaining_uses: BindingUseSummary<'a>,
}

pub(super) struct InlineRewriteState<'a> {
    pub(super) consumed_bindings: &'a mut [bool],
    pub(super) consumed_groups: &'a mut [bool],
    pub(super) eval_events: &'a mut Vec<ConstructorEvalEvent>,
}

impl<'a> InlineContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        pending_producers: &'a [PendingProducer],
        producer_index_by_binding: &'a [Option<usize>],
        state: InlineRewriteState<'a>,
        remaining_uses: BindingUseSummary<'a>,
    ) -> Self {
        Self {
            block,
            binding_index,
            pending_producers,
            producer_index_by_binding,
            consumed_bindings: state.consumed_bindings,
            consumed_groups: state.consumed_groups,
            eval_events: state.eval_events,
            inside_producer_value: false,
            remaining_uses,
        }
    }
}

pub(super) fn inline_constructor_value(
    context: &mut InlineContext<'_>,
    value: &HirExpr,
) -> Option<HirExpr> {
    inline_constructor_value_at_site(context, value, ConstructorInlineSite::Neutral)
}

#[derive(Clone, Copy)]
enum ConstructorInlineSite {
    Neutral,
    CallCallee,
    AccessBase,
}

fn inline_constructor_value_at_site(
    context: &mut InlineContext<'_>,
    value: &HirExpr,
    site: ConstructorInlineSite,
) -> Option<HirExpr> {
    if let Some(binding) = binding_from_expr(value)
        && let Some(binding_id) = context.binding_index.id_of(binding)
        && let Some(producer_index) = context
            .producer_index_by_binding
            .get(binding_id)
            .and_then(|producer_index| *producer_index)
    {
        let producer = &context.pending_producers[producer_index];
        // 候选拒绝[ProofIncomplete]：producer 有 region 后续 use 时，当前事务只能整句删除
        // 它；保留声明并仅重建 table write 本可继续优化，需扩展 partial-consume 计划。
        if context.remaining_uses.contains(producer.binding_id) {
            return None;
        }
        // 候选拒绝[SemanticBarrier:EvalMultiplicity]：同一 producer 被第二次消费时再次展开会
        // 重复求值；`local v = mark(); t[v] = v` 必须只调用一次，见 regress_235。
        if context.consumed_bindings[producer.binding_id] {
            return None;
        }
        let producer_value = pending_producer_value(context.block, producer)?;
        if !matches!(site, ConstructorInlineSite::Neutral)
            && !producer_value_reaches_access_base_shape(context, producer_value)
        {
            // 候选拒绝[ProofIncomplete]：callee/access-base 只接受当前可直接生成的前缀形状；
            // 其它可加括号或继续展开的表达式尚未由 Generate 语法事实证明。
            return None;
        }
        context.consumed_bindings[producer.binding_id] = true;
        if let Some(group) = producer.group {
            context.consumed_groups[group] = true;
        }
        let producer_value = producer_value.clone();
        // 已经决定把这个 producer 值内联到当前站点，接下来要继续展开它内部的
        // 子表达式。被内联进来的表达式的内部位置在语法上没有 callee/access-base
        // 级别的形状约束（它们是这个值的内部组合），所以这里把站点重置为
        // Neutral 再递归。不然像 `trailing=t47 → call(t4)` 这类形状会因为
        // `t4` 出现在 CallCallee 位置时被 access-base 过滤掉，导致 producer
        // t4 仍然未消费，整段 region 回滚而无法折回构造器。
        let was_inside_producer_value = context.inside_producer_value;
        context.inside_producer_value = true;
        let inlined = inline_constructor_value_at_site(
            context,
            &producer_value,
            ConstructorInlineSite::Neutral,
        );
        context.inside_producer_value = was_inside_producer_value;
        let inlined = inlined?;
        if expr_requires_ordered_snapshot(&producer_value) {
            context
                .eval_events
                .push(ConstructorEvalEvent::Producer(producer_index));
        }
        return Some(inlined);
    }

    let records_barrier = !context.inside_producer_value && expr_requires_ordered_snapshot(value);
    let inlined = match value {
        HirExpr::Unary(unary) => HirExpr::Unary(Box::new(HirUnaryExpr {
            op: unary.op,
            expr: inline_constructor_value_at_site(
                context,
                &unary.expr,
                ConstructorInlineSite::Neutral,
            )?,
        })),
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(HirBinaryExpr {
            op: binary.op,
            lhs: inline_constructor_value_at_site(
                context,
                &binary.lhs,
                ConstructorInlineSite::Neutral,
            )?,
            rhs: inline_constructor_value_at_site(
                context,
                &binary.rhs,
                ConstructorInlineSite::Neutral,
            )?,
        })),
        HirExpr::TableAccess(access) => {
            HirExpr::TableAccess(Box::new(crate::hir::common::HirTableAccess {
                base: inline_constructor_value_at_site(
                    context,
                    &access.base,
                    ConstructorInlineSite::AccessBase,
                )?,
                key: inline_constructor_value_at_site(
                    context,
                    &access.key,
                    ConstructorInlineSite::Neutral,
                )?,
            }))
        }
        HirExpr::Call(call) => HirExpr::Call(Box::new(inline_constructor_call(context, call)?)),
        HirExpr::LogicalAnd(logical) => {
            inline_short_circuit_expr(context, logical, HirExpr::LogicalAnd)?
        }
        HirExpr::LogicalOr(logical) => {
            inline_short_circuit_expr(context, logical, HirExpr::LogicalOr)?
        }
        _ if expr_depends_on_any_pending_binding(
            value,
            context.binding_index,
            context.producer_index_by_binding,
            context.consumed_bindings,
        ) =>
        {
            // 候选拒绝[ProofIncomplete]：Decision、嵌套 constructor、closure capture 等节点
            // 尚未实现 pending-binding 的结构化替换，不能把“未支持”当成不等价证明。
            return None;
        }
        _ => value.clone(),
    };
    if records_barrier {
        context.eval_events.push(ConstructorEvalEvent::Barrier);
    }
    Some(inlined)
}

pub(super) fn inline_constructor_call(
    context: &mut InlineContext<'_>,
    call: &HirCallExpr,
) -> Option<HirCallExpr> {
    let inline_args = |context: &mut InlineContext<'_>, args: &HirValuePack| {
        let fixed = args
            .fixed
            .iter()
            .map(|arg| {
                inline_constructor_value_at_site(context, arg, ConstructorInlineSite::Neutral)
            })
            .collect::<Option<Vec<_>>>()?;
        let tail = match &args.tail {
            Some(tail) => Some(tail.clone().try_map_call(|nested| {
                let mapped = inline_constructor_call(context, &nested)?;
                // `try_map_call` bypasses the normal expression wrapper, so account for the
                // nested tail call explicitly in the eval-order proof.
                context.eval_events.push(ConstructorEvalEvent::Barrier);
                Some(mapped)
            })?),
            None => None,
        };
        Some(HirValuePack { fixed, tail })
    };

    // Luau FASTCALL materializes direct arguments before fallback callee setup.  The metadata
    // is part of HIR's evaluation-order contract even though AST still prints a normal call.
    let (callee, args) = if call.fastcall.is_some() {
        let args = inline_args(context, &call.args)?;
        let callee = inline_constructor_value_at_site(
            context,
            &call.callee,
            ConstructorInlineSite::CallCallee,
        )?;
        (callee, args)
    } else {
        let callee = inline_constructor_value_at_site(
            context,
            &call.callee,
            ConstructorInlineSite::CallCallee,
        )?;
        let args = inline_args(context, &call.args)?;
        (callee, args)
    };
    Some(HirCallExpr {
        callee,
        args,
        method: call.method,
        fastcall: call.fastcall,
        method_name: call.method_name.clone(),
    })
}

fn inline_short_circuit_expr(
    context: &mut InlineContext<'_>,
    logical: &HirLogicalExpr,
    ctor: fn(Box<HirLogicalExpr>) -> HirExpr,
) -> Option<HirExpr> {
    // 短路右侧不是无条件求值位置；如果它引用 pending producer，
    // 把 producer 折进去会把原本已执行的求值变成条件执行，或留下未定义引用。
    if expr_mentions_any_pending_binding(
        &logical.rhs,
        context.binding_index,
        context.producer_index_by_binding,
    ) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：producer 原本无条件先求值；搬入短路右臂会
        // 变成条件求值，例如 `v = mark(); t.x = false and v` 不能内联为一次表达式。
        return None;
    }

    Some(ctor(Box::new(HirLogicalExpr {
        lhs: inline_constructor_value_at_site(
            context,
            &logical.lhs,
            ConstructorInlineSite::Neutral,
        )?,
        rhs: logical.rhs.clone(),
    })))
}

pub(super) fn expr_mentions_any_pending_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producer_index_by_binding: &[Option<usize>],
) -> bool {
    expr_mentions_binding_where(expr, binding_index, |binding_id| {
        producer_index_by_binding
            .get(binding_id)
            .is_some_and(Option::is_some)
    })
}

fn expr_mentions_binding_where(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    predicate: impl Fn(BindingId) -> bool + Copy,
) -> bool {
    if binding_from_expr(expr)
        .and_then(|binding| binding_index.id_of(binding))
        .is_some_and(predicate)
    {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_mentions_binding_where(&access.base, binding_index, predicate)
                || expr_mentions_binding_where(&access.key, binding_index, predicate)
        }
        HirExpr::Unary(unary) => expr_mentions_binding_where(&unary.expr, binding_index, predicate),
        HirExpr::Binary(binary) => {
            expr_mentions_binding_where(&binary.lhs, binding_index, predicate)
                || expr_mentions_binding_where(&binary.rhs, binding_index, predicate)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_mentions_binding_where(&logical.lhs, binding_index, predicate)
                || expr_mentions_binding_where(&logical.rhs, binding_index, predicate)
        }
        HirExpr::Call(call) => {
            expr_mentions_binding_where(&call.callee, binding_index, predicate)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_mentions_binding_where(arg, binding_index, predicate))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(value) => {
                    expr_mentions_binding_where(value, binding_index, predicate)
                }
                HirTableField::Record(field) => {
                    expr_mentions_binding_where(&field.value, binding_index, predicate)
                        || matches!(
                            &field.key,
                            HirTableKey::Expr(key_expr)
                                if expr_mentions_binding_where(
                                    key_expr,
                                    binding_index,
                                    predicate,
                                )
                        )
                }
            }) || table.trailing_multivalue.as_ref().is_some_and(|tail| {
                expr_mentions_binding_where(tail.as_expr(), binding_index, predicate)
            })
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_mentions_binding_where(&node.test, binding_index, predicate)
                || decision_target_mentions_binding_where(&node.truthy, binding_index, predicate)
                || decision_target_mentions_binding_where(&node.falsy, binding_index, predicate)
        }),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_mentions_binding_where(&capture.value, binding_index, predicate)),
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
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

fn decision_target_mentions_binding_where(
    target: &HirDecisionTarget,
    binding_index: &BindingIndex,
    predicate: impl Fn(BindingId) -> bool + Copy,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => {
            expr_mentions_binding_where(expr, binding_index, predicate)
        }
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn pending_producer_value<'a>(
    block: &'a HirBlock,
    producer: &PendingProducer,
) -> Option<&'a HirExpr> {
    match producer.source {
        PendingProducerSource::Value {
            stmt_index,
            value_index,
        } => producer_source_value(block, stmt_index, value_index),
        PendingProducerSource::Tail { stmt_index } => producer_tail_source_value(block, stmt_index),
        PendingProducerSource::Empty => None,
    }
}

fn producer_tail_source_value(block: &HirBlock, stmt_index: usize) -> Option<&HirExpr> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        crate::hir::common::HirStmt::LocalDecl(local_decl) => {
            local_decl.values.tail.as_ref().map(HirPackTail::as_expr)
        }
        crate::hir::common::HirStmt::Assign(assign) => {
            assign.values.tail.as_ref().map(HirPackTail::as_expr)
        }
        _ => None,
    }
}

fn producer_source_value(
    block: &HirBlock,
    stmt_index: usize,
    value_index: usize,
) -> Option<&HirExpr> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        crate::hir::common::HirStmt::LocalDecl(local_decl) => {
            local_decl.values.fixed.get(value_index)
        }
        crate::hir::common::HirStmt::Assign(assign) => assign.values.fixed.get(value_index),
        _ => None,
    }
}

fn expr_depends_on_any_pending_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producer_index_by_binding: &[Option<usize>],
    consumed_bindings: &[bool],
) -> bool {
    expr_mentions_binding_where(expr, binding_index, |binding_id| {
        producer_index_by_binding
            .get(binding_id)
            .is_some_and(Option::is_some)
            && !consumed_bindings[binding_id]
    })
}

/// 判断一个 producer-value 内联到 callee / access-base 位置后，经过后续
/// 内联展开，最终形态是否是合法的 access-base 形状。
///
/// 这个谓词是 `is_constructor_access_base_inline_expr` 的“透视版”：当值中
/// 出现 `TempRef`/`LocalRef` 时，若该绑定是 pending 的 producer 且尚未消费，
/// 我们会沿着 producer chain 再判一次；这样像
/// `call(t4)` ← `t4=t3["status"]` ← `t3=require("jit")` 这种形状也可以被
/// 接受 —— 因为最终折出的是 `require("jit")["status"](...)`，访问基本身
/// 本就是合法 access-base。
///
/// 不做修改（不消费 consumed_bindings），只做只读判定。
fn producer_value_reaches_access_base_shape(context: &InlineContext<'_>, expr: &HirExpr) -> bool {
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
        | HirExpr::GlobalRef(_) => true,
        HirExpr::TableAccess(access) => {
            producer_value_reaches_access_base_shape(context, &access.base)
        }
        // Lua 的 prefixexp 语法允许 `Call` 结果继续作为下标/调用前缀
        // （例如 `require("jit")["status"]()`）。因此 Call 本身也是合法的
        // callee / access-base 形状，只要其 callee 本身是合法前缀表达式。
        HirExpr::Call(call) => producer_value_reaches_access_base_shape(context, &call.callee),
        HirExpr::TempRef(_) => {
            // TempRef 对应的 binding 如果还在 pending producer 列表里，
            // 说明它有机会被继续内联展开；透视到它的 producer 值再次判断一次。
            if let Some(binding) = binding_from_expr(expr)
                && let Some(binding_id) = context.binding_index.id_of(binding)
                && let Some(producer_index) = context
                    .producer_index_by_binding
                    .get(binding_id)
                    .and_then(|producer_index| *producer_index)
            {
                let producer = &context.pending_producers[producer_index];
                if context.remaining_uses.contains(producer.binding_id) {
                    return false;
                }
                if let Some(inner) = pending_producer_value(context.block, producer) {
                    return producer_value_reaches_access_base_shape(context, inner);
                }
            }
            false
        }
        _ => false,
    }
}
