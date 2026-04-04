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
            && !is_constructor_access_base_inline_expr(producer_value)
        {
            return None;
        }
        context.consumed_bindings[producer.binding_id] = true;
        if let Some(group) = producer.group {
            context.consumed_groups[group] = true;
        }
        return Some(producer_value.clone());
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

fn is_constructor_access_base_inline_expr(expr: &HirExpr) -> bool {
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
        HirExpr::TableAccess(access) => is_constructor_access_base_inline_expr(&access.base),
        _ => false,
    }
}
