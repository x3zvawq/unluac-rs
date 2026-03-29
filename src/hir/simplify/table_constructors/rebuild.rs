//! 这个子模块负责把扫描得到的 region steps 重建回表构造器。
//!
//! 它依赖 `scan` 产出的 step 序列和 `inline_value` 的安全内联结果，只负责按顺序 flush
//! 片段，不会回头重新判定哪个 stmt 属于候选 region。
//! 例如：一串 `record/setlist/producer` step 会在这里重新拼成 `HirTableConstructor`。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::hir::common::{
    HirCallExpr, HirCapture, HirDecisionTarget, HirExpr, HirStmt, HirTableConstructor,
    HirTableField, HirTableKey, HirTableSetList,
};

use super::bindings::{collect_stmt_slice_bindings, matches_binding_ref};
use super::inline_value::inline_constructor_value;
use super::{PendingProducer, ProducerGroupMeta, RegionStep, SegmentToken, TableBinding};

pub(super) fn rebuild_constructor_from_steps(
    mut constructor: HirTableConstructor,
    steps: &[RegionStep],
    remaining_stmts: &[HirStmt],
    materialized_bindings: &BTreeMap<TableBinding, usize>,
) -> Option<HirTableConstructor> {
    let remaining_uses = collect_stmt_slice_bindings(remaining_stmts);
    let region_contains_set_list = steps
        .iter()
        .any(|step| matches!(step, RegionStep::SetList(_)));
    let mut pending_segment = Vec::new();

    for step in steps {
        match step {
            RegionStep::Producer(_, _) | RegionStep::ProducerGroup(_) | RegionStep::Record(_) => {
                pending_segment.push(step.clone())
            }
            RegionStep::SetList(set_list) => {
                flush_constructor_segment(
                    &mut constructor,
                &pending_segment,
                Some(set_list),
                &remaining_uses,
                region_contains_set_list,
                materialized_bindings,
            )?;
                pending_segment.clear();
            }
        }
    }

    flush_constructor_segment(
        &mut constructor,
        &pending_segment,
        None,
        &remaining_uses,
        region_contains_set_list,
        materialized_bindings,
    )?;

    Some(constructor)
}

fn flush_constructor_segment(
    constructor: &mut HirTableConstructor,
    segment: &[RegionStep],
    set_list: Option<&HirTableSetList>,
    remaining_uses: &BTreeSet<TableBinding>,
    allow_closure_records: bool,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
) -> Option<()> {
    if segment.is_empty() {
        normalize_sequential_integer_record_fields(constructor);
        if let Some(set_list) = set_list {
            if set_list.start_index != next_array_index(constructor) {
                return None;
            }
            for value in &set_list.values {
                constructor.fields.push(HirTableField::Array(value.clone()));
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                constructor.trailing_multivalue = Some(trailing.clone());
            }
        }
        return Some(());
    }

    let mut producer_values = Vec::<PendingProducer>::new();
    let mut producer_groups = Vec::<ProducerGroupMeta>::new();
    let mut tokens = Vec::<SegmentToken>::new();
    let mut consumed = BTreeSet::new();
    let mut consumed_groups = BTreeSet::new();
    let mut removed_materializations = BTreeMap::<TableBinding, usize>::new();

    for step in segment {
        match step {
            RegionStep::Producer(binding, value) => {
                producer_values.push(PendingProducer {
                    binding: *binding,
                    value: Some(value.clone()),
                    group: None,
                });
                *removed_materializations.entry(*binding).or_default() += 1;
                tokens.push(SegmentToken::Producer(*binding));
            }
            RegionStep::ProducerGroup(group) => {
                let group_id = producer_groups.len();
                producer_groups.push(ProducerGroupMeta {
                    drop_without_consumption_is_safe: group.drop_without_consumption_is_safe,
                });
                for slot in &group.slots {
                    producer_values.push(PendingProducer {
                        binding: slot.binding,
                        value: slot.value.clone(),
                        group: Some(group_id),
                    });
                    *removed_materializations.entry(slot.binding).or_default() += 1;
                    tokens.push(SegmentToken::Producer(slot.binding));
                }
            }
            RegionStep::Record(field) => {
                let recursive_closure_slot =
                    binding_is_recursive_closure_slot(&field.value, &producer_values);
                let value = inline_constructor_value(
                    &field.value,
                    &producer_values,
                    &mut consumed,
                    &mut consumed_groups,
                    remaining_uses,
                )?;
                // 只有能证明这段 region 还处在字面量初始化 flush 里时，才允许无条件吸收
                // `field = function() ... end`。如果整段根本没有 `SETLIST`，名字字段上的
                // closure 赋值更像“先建表、再挂方法”，需要把结构机会留给后续 method sugar。
                //
                // 但像 `tbl[key] = function() ... end` 这种表达式 key 的 closure record，
                // 本身并不是 method 语法候选；继续保守退回只会错过真实的构造器字面量机会。
                // 另外，递归局部函数“先占槽、再把自己塞进表里”的形状也必须保留显式绑定，
                // 否则后面就没有稳定的 self-recursive 名字可供恢复。
                if matches!(value, HirExpr::Closure(_))
                    && (recursive_closure_slot
                        || (!allow_closure_records && matches!(field.key, HirTableKey::Name(_))))
                {
                    return None;
                }
                // 这里还要守住另一条结构不变量：如果 closure 里 capture 的 local/temp
                // 只靠当前 region 里的 producer 语句才能“显式存在”，那一旦把整段
                // producer 都吃进 `{ ... }`，后面就只剩悬空 capture 了。递归 local
                // function slot 正是这种形状，所以要在 HIR 这里拒绝折叠，而不是等
                // AST/readability 再兜底补名字。
                if expr_captures_orphaned_binding(
                    &value,
                    materialized_bindings,
                    &removed_materializations,
                ) {
                    return None;
                }
                tokens.push(SegmentToken::Record(crate::hir::common::HirRecordField {
                    key: field.key.clone(),
                    value,
                }));
            }
            RegionStep::SetList(_) => unreachable!("set-list should terminate constructor segment"),
        }
    }

    if let Some(set_list) = set_list {
        if set_list.start_index != next_array_index(constructor) {
            return None;
        }

        let mut queued_values = VecDeque::from(set_list.values.clone());
        for token in tokens {
            match token {
                SegmentToken::Producer(binding) => {
                    if consumed.contains(&binding) {
                        continue;
                    }
                    match queued_values.front() {
                        Some(front) if matches_binding_ref(front, binding) => {
                            let producer_value =
                                producer_value_for_binding(&producer_values, binding)?;
                            if remaining_uses.contains(&binding) {
                                return None;
                            }
                            consumed.insert(binding);
                            queued_values.pop_front();
                            constructor
                                .fields
                                .push(HirTableField::Array(producer_value.clone()));
                        }
                        Some(_)
                            if queued_values
                                .iter()
                                .any(|value| matches_binding_ref(value, binding)) =>
                        {
                            // Lua 编译器为构造器批量刷出的 `SETLIST` 顺序和源码数组项顺序一致。
                            // 如果 producer 在 token 序里出现得更早，却在 set-list 队列里更晚，
                            // 说明这段 region 已经不是我们能稳定证明的字面量顺序。
                            return None;
                        }
                        _ => {}
                    }
                }
                SegmentToken::Record(field) => {
                    push_constructor_field(constructor, field);
                }
            }
        }

        for value in queued_values {
            let value = inline_constructor_value(
                &value,
                &producer_values,
                &mut consumed,
                &mut consumed_groups,
                remaining_uses,
            )?;
            constructor.fields.push(HirTableField::Array(value));
        }

        if let Some(trailing) = &set_list.trailing_multivalue {
            let trailing = inline_constructor_value(
                trailing,
                &producer_values,
                &mut consumed,
                &mut consumed_groups,
                remaining_uses,
            )?;
            constructor.trailing_multivalue = Some(trailing);
        }
    } else {
        for token in tokens {
            match token {
                SegmentToken::Producer(binding) if !consumed.contains(&binding) => return None,
                SegmentToken::Producer(_) => {}
                SegmentToken::Record(field) => {
                    push_constructor_field(constructor, field);
                }
            }
        }
        normalize_sequential_integer_record_fields(constructor);
    }

    if producer_values.iter().any(|producer| {
        if consumed.contains(&producer.binding) {
            return false;
        }
        if remaining_uses.contains(&producer.binding) {
            return true;
        }
        match producer.group {
            Some(group) if consumed_groups.contains(&group) => false,
            Some(group) => !producer_groups[group].drop_without_consumption_is_safe,
            None => true,
        }
    }) {
        return None;
    }

    Some(())
}

fn next_array_index(constructor: &HirTableConstructor) -> u32 {
    constructor
        .fields
        .iter()
        .filter(|field| matches!(field, HirTableField::Array(_)))
        .count() as u32
        + 1
}

fn push_constructor_field(
    constructor: &mut HirTableConstructor,
    field: crate::hir::common::HirRecordField,
) {
    let next_index = i64::from(next_array_index(constructor));
    match &field.key {
        HirTableKey::Expr(HirExpr::Integer(value)) if *value == next_index => {
            constructor.fields.push(HirTableField::Array(field.value));
        }
        _ => constructor.fields.push(HirTableField::Record(field)),
    }
}

fn normalize_sequential_integer_record_fields(constructor: &mut HirTableConstructor) {
    loop {
        let next_index = i64::from(next_array_index(constructor));
        let Some(record_index) = constructor.fields.iter().position(|field| {
            let HirTableField::Record(field) = field else {
                return false;
            };
            matches!(&field.key, HirTableKey::Expr(HirExpr::Integer(value)) if *value == next_index)
                && can_reorder_integer_record_value(&field.value)
        }) else {
            break;
        };
        let HirTableField::Record(field) = constructor.fields.remove(record_index) else {
            unreachable!("record field position was validated above");
        };
        constructor.fields.push(HirTableField::Array(field.value));
    }
}

fn can_reorder_integer_record_value(expr: &HirExpr) -> bool {
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
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::Closure(_) => true,
        HirExpr::Unary(unary) => can_reorder_integer_record_value(&unary.expr),
        HirExpr::Binary(binary) => {
            can_reorder_integer_record_value(&binary.lhs)
                && can_reorder_integer_record_value(&binary.rhs)
        }
        _ => false,
    }
}

fn producer_value_for_binding(
    producers: &[PendingProducer],
    binding: TableBinding,
) -> Option<&HirExpr> {
    producers.iter().find_map(|producer| {
        (producer.binding == binding)
            .then_some(producer.value.as_ref())
            .flatten()
    })
}

fn binding_is_recursive_closure_slot(expr: &HirExpr, producers: &[PendingProducer]) -> bool {
    let Some(binding) = matches_binding_ref_expr(expr) else {
        return false;
    };
    let Some(HirExpr::Closure(closure)) = producer_value_for_binding(producers, binding) else {
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

fn matches_binding_ref_expr(expr: &HirExpr) -> Option<TableBinding> {
    match expr {
        HirExpr::LocalRef(local) => Some(TableBinding::Local(*local)),
        HirExpr::TempRef(temp) => Some(TableBinding::Temp(*temp)),
        _ => None,
    }
}

fn expr_captures_orphaned_binding(
    expr: &HirExpr,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
    removed_materializations: &BTreeMap<TableBinding, usize>,
) -> bool {
    match expr {
        HirExpr::Unary(unary) => expr_captures_orphaned_binding(
            &unary.expr,
            materialized_bindings,
            removed_materializations,
        ),
        HirExpr::Binary(binary) => {
            expr_captures_orphaned_binding(
                &binary.lhs,
                materialized_bindings,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &binary.rhs,
                materialized_bindings,
                removed_materializations,
            )
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_captures_orphaned_binding(
                &logical.lhs,
                materialized_bindings,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &logical.rhs,
                materialized_bindings,
                removed_materializations,
            )
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_captures_orphaned_binding(
                &node.test,
                materialized_bindings,
                removed_materializations,
            ) || decision_target_captures_orphaned_binding(
                &node.truthy,
                materialized_bindings,
                removed_materializations,
            ) || decision_target_captures_orphaned_binding(
                &node.falsy,
                materialized_bindings,
                removed_materializations,
            )
        }),
        HirExpr::Call(call) => call_captures_orphaned_binding(
            call,
            materialized_bindings,
            removed_materializations,
        ),
        HirExpr::TableAccess(access) => {
            expr_captures_orphaned_binding(
                &access.base,
                materialized_bindings,
                removed_materializations,
            ) || expr_captures_orphaned_binding(
                &access.key,
                materialized_bindings,
                removed_materializations,
            )
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(value) => expr_captures_orphaned_binding(
                    value,
                    materialized_bindings,
                    removed_materializations,
                ),
                HirTableField::Record(field) => {
                    table_key_captures_orphaned_binding(
                        &field.key,
                        materialized_bindings,
                        removed_materializations,
                    ) || expr_captures_orphaned_binding(
                        &field.value,
                        materialized_bindings,
                        removed_materializations,
                    )
                }
            }) || table.trailing_multivalue.as_ref().is_some_and(|value| {
                expr_captures_orphaned_binding(
                    value,
                    materialized_bindings,
                    removed_materializations,
                )
            })
        }
        HirExpr::Closure(closure) => closure.captures.iter().any(|capture| {
            capture_is_orphaned(
                capture,
                materialized_bindings,
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

fn capture_is_orphaned(
    capture: &HirCapture,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
    removed_materializations: &BTreeMap<TableBinding, usize>,
) -> bool {
    let Some(binding) = matches_binding_ref_expr(&capture.value) else {
        return false;
    };
    let surviving = materialized_bindings
        .get(&binding)
        .copied()
        .unwrap_or_default()
        .saturating_sub(removed_materializations.get(&binding).copied().unwrap_or_default());
    surviving == 0
}

fn call_captures_orphaned_binding(
    call: &HirCallExpr,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
    removed_materializations: &BTreeMap<TableBinding, usize>,
) -> bool {
    expr_captures_orphaned_binding(
        &call.callee,
        materialized_bindings,
        removed_materializations,
    ) || call.args.iter().any(|arg| {
        expr_captures_orphaned_binding(arg, materialized_bindings, removed_materializations)
    })
}

fn decision_target_captures_orphaned_binding(
    target: &HirDecisionTarget,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
    removed_materializations: &BTreeMap<TableBinding, usize>,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_captures_orphaned_binding(
            expr,
            materialized_bindings,
            removed_materializations,
        ),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_captures_orphaned_binding(
    key: &HirTableKey,
    materialized_bindings: &BTreeMap<TableBinding, usize>,
    removed_materializations: &BTreeMap<TableBinding, usize>,
) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_captures_orphaned_binding(
            expr,
            materialized_bindings,
            removed_materializations,
        ),
    }
}
