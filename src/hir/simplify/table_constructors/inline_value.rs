//! 这个子模块负责把构造器生产者内联进字段值。
//!
//! 它依赖 `bindings` 已经识别好的同一绑定和 pending producer 列表，只尝试安全内联字段/
//! callee/access-base 值，不会在这里决定整段 region 的分段边界。
//! 例如：`local v = f(); t.x = v` 可能在这里折叠成 `t.x = f()`。

use std::collections::BTreeSet;

use crate::hir::common::{HirCallExpr, HirExpr};

use super::bindings::{expr_depends_on_any_binding, matches_binding_ref};
use super::{PendingProducer, TableBinding};

pub(super) fn inline_constructor_value(
    value: &HirExpr,
    pending_producers: &[PendingProducer],
    consumed: &mut BTreeSet<TableBinding>,
    consumed_groups: &mut BTreeSet<usize>,
    remaining_uses: &BTreeSet<TableBinding>,
) -> Option<HirExpr> {
    inline_constructor_value_at_site(
        value,
        pending_producers,
        consumed,
        consumed_groups,
        remaining_uses,
        ConstructorInlineSite::Neutral,
    )
}

#[derive(Clone, Copy)]
enum ConstructorInlineSite {
    Neutral,
    CallCallee,
    AccessBase,
}

fn inline_constructor_value_at_site(
    value: &HirExpr,
    pending_producers: &[PendingProducer],
    consumed: &mut BTreeSet<TableBinding>,
    consumed_groups: &mut BTreeSet<usize>,
    remaining_uses: &BTreeSet<TableBinding>,
    site: ConstructorInlineSite,
) -> Option<HirExpr> {
    for producer in pending_producers {
        if matches_binding_ref(value, producer.binding) {
            if remaining_uses.contains(&producer.binding) {
                return None;
            }
            let producer_value = producer.value.as_ref()?;
            if !matches!(site, ConstructorInlineSite::Neutral)
                && !is_constructor_access_base_inline_expr(producer_value)
            {
                return None;
            }
            consumed.insert(producer.binding);
            if let Some(group) = producer.group {
                consumed_groups.insert(group);
            }
            return Some(producer_value.clone());
        }
    }

    match value {
        HirExpr::TableAccess(access) => {
            return Some(HirExpr::TableAccess(Box::new(
                crate::hir::common::HirTableAccess {
                    base: inline_constructor_value_at_site(
                        &access.base,
                        pending_producers,
                        consumed,
                        consumed_groups,
                        remaining_uses,
                        ConstructorInlineSite::AccessBase,
                    )?,
                    key: inline_constructor_value_at_site(
                        &access.key,
                        pending_producers,
                        consumed,
                        consumed_groups,
                        remaining_uses,
                        ConstructorInlineSite::Neutral,
                    )?,
                },
            )));
        }
        HirExpr::Call(call) => {
            return Some(HirExpr::Call(Box::new(HirCallExpr {
                callee: inline_constructor_value_at_site(
                    &call.callee,
                    pending_producers,
                    consumed,
                    consumed_groups,
                    remaining_uses,
                    ConstructorInlineSite::CallCallee,
                )?,
                args: call
                    .args
                    .iter()
                    .map(|arg| {
                        inline_constructor_value_at_site(
                            arg,
                            pending_producers,
                            consumed,
                            consumed_groups,
                            remaining_uses,
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

    if expr_depends_on_any_binding(
        value,
        &pending_producers
            .iter()
            .filter(|producer| !consumed.contains(&producer.binding))
            .map(|producer| producer.binding)
            .collect::<Vec<_>>(),
    ) {
        None
    } else {
        Some(value.clone())
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
