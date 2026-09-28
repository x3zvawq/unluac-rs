//! 校验构造器改写后 closure 的直接 capture 仍有物化绑定。
//!
//! 消费 BindingIndex 与当前事务，不重新推断 capture 来源或展开 child proto。

use super::super::bindings::binding_from_identity;
use super::*;
use crate::hir::visit::any_expr;

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
    let Some(HirExpr::Closure(closure)) = producers[producer_index].source.value(block) else {
        return false;
    };
    closure
        .captures
        .iter()
        .any(|capture| binding_from_identity(capture.binding) == Some(binding))
}

pub(super) fn expr_captures_orphaned_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    any_expr(expr, &mut |expr| {
        let HirExpr::Closure(closure) = expr else {
            return false;
        };
        closure.captures.iter().any(|capture| {
            capture_is_orphaned(
                capture,
                binding_index,
                materialized_binding_counts,
                removed_materializations,
            )
        })
    })
}

fn capture_is_orphaned(
    capture: &HirCapture,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    removed_materializations: &[u32],
) -> bool {
    let Some(binding) = binding_from_identity(capture.binding) else {
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
