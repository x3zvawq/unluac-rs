//! 这个子模块负责把扫描得到的 region steps 重建回表构造器。
//!
//! 它依赖 `scan` 产出的 step 序列和 `inline_value` 的安全内联结果，只负责按顺序 flush
//! 片段，不会回头重新判定哪个 stmt 属于候选 region。
//! 例如：一串 `record/setlist/producer` step 会在这里重新拼成 `HirTableConstructor`。

use std::collections::{BTreeSet, VecDeque};

use crate::hir::common::{
    HirExpr, HirStmt, HirTableConstructor, HirTableField, HirTableKey, HirTableSetList,
};

use super::bindings::{collect_stmt_slice_bindings, matches_binding_ref};
use super::inline_value::inline_constructor_value;
use super::{PendingProducer, ProducerGroupMeta, RegionStep, SegmentToken, TableBinding};

pub(super) fn rebuild_constructor_from_steps(
    mut constructor: HirTableConstructor,
    steps: &[RegionStep],
    remaining_stmts: &[HirStmt],
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
    )?;

    Some(constructor)
}

fn flush_constructor_segment(
    constructor: &mut HirTableConstructor,
    segment: &[RegionStep],
    set_list: Option<&HirTableSetList>,
    remaining_uses: &BTreeSet<TableBinding>,
    allow_closure_records: bool,
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

    for step in segment {
        match step {
            RegionStep::Producer(binding, value) => {
                producer_values.push(PendingProducer {
                    binding: *binding,
                    value: Some(value.clone()),
                    group: None,
                });
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
                    tokens.push(SegmentToken::Producer(slot.binding));
                }
            }
            RegionStep::Record(field) => {
                let value = inline_constructor_value(
                    &field.value,
                    &producer_values,
                    &mut consumed,
                    &mut consumed_groups,
                    remaining_uses,
                )?;
                // 只有能证明这段 region 还处在字面量初始化 flush 里时，才允许继续吸收
                // `field = function() ... end`。如果整段根本没有 `SETLIST`，这类 closure
                // 赋值更像“先建表、再挂方法”，需要把结构机会留给后续 method sugar。
                if matches!(value, HirExpr::Closure(_)) && !allow_closure_records {
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
