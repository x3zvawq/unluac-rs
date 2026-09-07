//! 校验构造器 producer 移除后，closure 的直接 capture 仍有物化绑定。
//!
//! 字段表达式的子节点只由共享 HIR 查询遍历；capture 边消费 BindingIndex 与本事务的
//! materialization 计数，不把它改成一般表达式提及，也不展开绑定定义或子 proto。
//! 例如字段 closure 捕获的 Local 若只由被删除 producer 声明，则拒绝该构造器事务；
//! 参数及 upvalue 的存活不由本事务签发。这里不重建字段顺序或 capture 来源。

use super::super::bindings::binding_from_capture;
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
        .any(|capture| binding_from_capture(capture.binding) == Some(binding))
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
    let Some(binding) = binding_from_capture(capture.binding) else {
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
