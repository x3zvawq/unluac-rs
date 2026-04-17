//! 这个子模块负责把构造器生产者内联进字段值。
//!
//! 它依赖 `bindings` 已经识别好的同一绑定和 pending producer 列表，只尝试安全内联字段/
//! callee/access-base 值，不会在这里决定整段 region 的分段边界。
//! 例如：`local v = f(); t.x = v` 可能在这里折叠成 `t.x = f()`。

use crate::hir::common::{HirBlock, HirCallExpr, HirExpr};

use super::bindings::{BindingIndex, BindingUseSummary, binding_from_expr};
use super::{PendingProducer, PendingProducerSource};

pub(super) struct InlineContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    pending_producers: &'a [PendingProducer],
    producer_index_by_binding: &'a [Option<usize>],
    consumed_bindings: &'a mut [bool],
    consumed_groups: &'a mut [bool],
    remaining_uses: &'a BindingUseSummary,
}

impl<'a> InlineContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        pending_producers: &'a [PendingProducer],
        producer_index_by_binding: &'a [Option<usize>],
        consumed_bindings: &'a mut [bool],
        consumed_groups: &'a mut [bool],
        remaining_uses: &'a BindingUseSummary,
    ) -> Self {
        Self {
            block,
            binding_index,
            pending_producers,
            producer_index_by_binding,
            consumed_bindings,
            consumed_groups,
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
        if context.remaining_uses.contains(producer.binding_id) {
            return None;
        }
        let producer_value = pending_producer_value(context.block, producer)?;
        if !matches!(site, ConstructorInlineSite::Neutral)
            && !producer_value_reaches_access_base_shape(context, producer_value)
        {
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
        return inline_constructor_value_at_site(
            context,
            &producer_value,
            ConstructorInlineSite::Neutral,
        );
    }

    match value {
        HirExpr::TableAccess(access) => {
            return Some(HirExpr::TableAccess(Box::new(
                crate::hir::common::HirTableAccess {
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
                },
            )));
        }
        HirExpr::Call(call) => {
            return Some(HirExpr::Call(Box::new(HirCallExpr {
                callee: inline_constructor_value_at_site(
                    context,
                    &call.callee,
                    ConstructorInlineSite::CallCallee,
                )?,
                args: call
                    .args
                    .iter()
                    .map(|arg| {
                        inline_constructor_value_at_site(
                            context,
                            arg,
                            ConstructorInlineSite::Neutral,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
                multiret: call.multiret,
                method: call.method,
                method_name: call.method_name.clone(),
            })));
        }
        _ => {}
    }

    if expr_depends_on_any_pending_binding(
        value,
        context.binding_index,
        context.pending_producers,
        context.consumed_bindings,
    ) {
        None
    } else {
        Some(value.clone())
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
        PendingProducerSource::Empty => None,
    }
}

fn producer_source_value(
    block: &HirBlock,
    stmt_index: usize,
    value_index: usize,
) -> Option<&HirExpr> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        crate::hir::common::HirStmt::LocalDecl(local_decl) => local_decl.values.get(value_index),
        crate::hir::common::HirStmt::Assign(assign) => assign.values.get(value_index),
        _ => None,
    }
}

fn expr_depends_on_any_pending_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    pending_producers: &[PendingProducer],
    consumed_bindings: &[bool],
) -> bool {
    if let Some(binding) = binding_from_expr(expr)
        && let Some(binding_id) = binding_index.id_of(binding)
        && !consumed_bindings[binding_id]
        && pending_producers
            .iter()
            .any(|producer| producer.binding_id == binding_id)
    {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_depends_on_any_pending_binding(
                &access.base,
                binding_index,
                pending_producers,
                consumed_bindings,
            ) || expr_depends_on_any_pending_binding(
                &access.key,
                binding_index,
                pending_producers,
                consumed_bindings,
            )
        }
        HirExpr::Unary(unary) => expr_depends_on_any_pending_binding(
            &unary.expr,
            binding_index,
            pending_producers,
            consumed_bindings,
        ),
        HirExpr::Binary(binary) => {
            expr_depends_on_any_pending_binding(
                &binary.lhs,
                binding_index,
                pending_producers,
                consumed_bindings,
            ) || expr_depends_on_any_pending_binding(
                &binary.rhs,
                binding_index,
                pending_producers,
                consumed_bindings,
            )
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_depends_on_any_pending_binding(
                &logical.lhs,
                binding_index,
                pending_producers,
                consumed_bindings,
            ) || expr_depends_on_any_pending_binding(
                &logical.rhs,
                binding_index,
                pending_producers,
                consumed_bindings,
            )
        }
        HirExpr::Call(call) => {
            expr_depends_on_any_pending_binding(
                &call.callee,
                binding_index,
                pending_producers,
                consumed_bindings,
            ) || call.args.iter().any(|arg| {
                expr_depends_on_any_pending_binding(
                    arg,
                    binding_index,
                    pending_producers,
                    consumed_bindings,
                )
            })
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::hir::common::HirTableField::Array(value) => {
                    expr_depends_on_any_pending_binding(
                        value,
                        binding_index,
                        pending_producers,
                        consumed_bindings,
                    )
                }
                crate::hir::common::HirTableField::Record(field) => {
                    expr_depends_on_any_pending_binding(
                        &field.value,
                        binding_index,
                        pending_producers,
                        consumed_bindings,
                    ) || matches!(
                        &field.key,
                        crate::hir::common::HirTableKey::Expr(key_expr)
                            if expr_depends_on_any_pending_binding(
                                key_expr,
                                binding_index,
                                pending_producers,
                                consumed_bindings,
                            )
                    )
                }
            }) || table.trailing_multivalue.as_ref().is_some_and(|value| {
                expr_depends_on_any_pending_binding(
                    value,
                    binding_index,
                    pending_producers,
                    consumed_bindings,
                )
            })
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_depends_on_any_pending_binding(
                &node.test,
                binding_index,
                pending_producers,
                consumed_bindings,
            ) || match &node.truthy {
                crate::hir::common::HirDecisionTarget::Expr(expr) => {
                    expr_depends_on_any_pending_binding(
                        expr,
                        binding_index,
                        pending_producers,
                        consumed_bindings,
                    )
                }
                crate::hir::common::HirDecisionTarget::Node(_)
                | crate::hir::common::HirDecisionTarget::CurrentValue => false,
            } || match &node.falsy {
                crate::hir::common::HirDecisionTarget::Expr(expr) => {
                    expr_depends_on_any_pending_binding(
                        expr,
                        binding_index,
                        pending_producers,
                        consumed_bindings,
                    )
                }
                crate::hir::common::HirDecisionTarget::Node(_)
                | crate::hir::common::HirDecisionTarget::CurrentValue => false,
            }
        }),
        HirExpr::Closure(closure) => closure.captures.iter().any(|capture| {
            expr_depends_on_any_pending_binding(
                &capture.value,
                binding_index,
                pending_producers,
                consumed_bindings,
            )
        }),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
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
fn producer_value_reaches_access_base_shape(
    context: &InlineContext<'_>,
    expr: &HirExpr,
) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
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
        HirExpr::Call(call) => {
            producer_value_reaches_access_base_shape(context, &call.callee)
        }
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
