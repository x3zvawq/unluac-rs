//! 校验构造器 producer 移除后 closure capture 仍有物化绑定；依赖 BindingIndex 与 producer 表，不负责字段/求值顺序重建；例如识别递归 closure 槽和嵌套表达式中的 orphan capture。

use super::*;

pub(super) fn binding_is_recursive_closure_slot(
    block: &HirBlock,
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producers: &[PendingProducer],
    producer_index_by_binding: &[Option<usize>],
) -> bool {
    let Some(binding) = binding_from_expr(expr) else {
        return false;
    };
    let Some(binding_id) = binding_index.id_of(binding) else {
        return false;
    };
    let Some(producer_index) = producer_index_by_binding
        .get(binding_id)
        .and_then(|producer_index| *producer_index)
    else {
        return false;
    };
    let Some(HirExpr::Closure(closure)) = pending_producer_value(block, &producers[producer_index])
    else {
        return false;
    };
    closure
        .captures
        .iter()
        .any(|capture| match (binding, &capture.value) {
            (TableBinding::Local(local), HirExpr::LocalRef(captured)) => *captured == local,
            (TableBinding::Temp(temp), HirExpr::TempRef(captured)) => *captured == temp,
            _ => false,
        })
}

pub(super) fn expr_captures_orphaned_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    match expr {
        HirExpr::Unary(unary) => expr_captures_orphaned_binding(
            &unary.expr,
            binding_index,
            materialized_binding_counts,
            removed_materializations,
        ),
        HirExpr::Binary(binary) => {
            expr_captures_orphaned_binding(
                &binary.lhs,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &binary.rhs,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_captures_orphaned_binding(
                &logical.lhs,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &logical.rhs,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_captures_orphaned_binding(
                &node.test,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            ) || decision_target_captures_orphaned_binding(
                &node.truthy,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            ) || decision_target_captures_orphaned_binding(
                &node.falsy,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        }),
        HirExpr::Call(call) => call_captures_orphaned_binding(
            call,
            binding_index,
            materialized_binding_counts,
            removed_materializations,
        ),
        HirExpr::TableAccess(access) => {
            expr_captures_orphaned_binding(
                &access.base,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &access.key,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(value) => expr_captures_orphaned_binding(
                    value,
                    binding_index,
                    materialized_binding_counts,
                    removed_materializations,
                ),
                HirTableField::Record(field) => {
                    table_key_captures_orphaned_binding(
                        &field.key,
                        binding_index,
                        materialized_binding_counts,
                        removed_materializations,
                    ) || expr_captures_orphaned_binding(
                        &field.value,
                        binding_index,
                        materialized_binding_counts,
                        removed_materializations,
                    )
                }
            }) || table.trailing_multivalue.as_ref().is_some_and(|tail| {
                expr_captures_orphaned_binding(
                    tail.as_expr(),
                    binding_index,
                    materialized_binding_counts,
                    removed_materializations,
                )
            })
        }
        HirExpr::Closure(closure) => closure.captures.iter().any(|capture| {
            capture_is_orphaned(
                capture,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        }),
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
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

pub(super) fn capture_is_orphaned(
    capture: &HirCapture,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    let Some(binding) = binding_from_expr(&capture.value) else {
        return false;
    };
    let Some(binding_id) = binding_index.id_of(binding) else {
        return false;
    };
    let surviving = materialized_binding_counts
        .get(binding_id)
        .copied()
        .unwrap_or_default()
        .saturating_sub(
            removed_materializations
                .get(binding_id)
                .copied()
                .unwrap_or_default(),
        );
    surviving == 0
}

pub(super) fn call_captures_orphaned_binding(
    call: &HirCallExpr,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    expr_captures_orphaned_binding(
        &call.callee,
        binding_index,
        materialized_binding_counts,
        removed_materializations,
    ) || call.args.iter().any(|arg| {
        expr_captures_orphaned_binding(
            arg,
            binding_index,
            materialized_binding_counts,
            removed_materializations,
        )
    })
}

pub(super) fn decision_target_captures_orphaned_binding(
    target: &HirDecisionTarget,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_captures_orphaned_binding(
            expr,
            binding_index,
            materialized_binding_counts,
            removed_materializations,
        ),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

pub(super) fn table_key_captures_orphaned_binding(
    key: &HirTableKey,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_captures_orphaned_binding(
            expr,
            binding_index,
            materialized_binding_counts,
            removed_materializations,
        ),
    }
}
