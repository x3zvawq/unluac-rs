//! 这个子模块负责把扫描得到的 region steps 重建回表构造器。
//!
//! 它依赖 `scan` 产出的轻量 step 描述和 `inline_value` 的安全内联结果，只负责按顺序 flush
//! 片段，不会回头重新判定哪个 stmt 属于候选 region。
//! 例如：一串 `record/setlist/producer` step 会在这里重新拼成 `HirTableConstructor`；
//! producer、record key/value 的求值事件序列不一致时，整个推测事务回滚。

use std::collections::VecDeque;

mod captures;
use captures::*;

use crate::ast::DecompileDialect;
use crate::hir::common::{
    HirBlock, HirCallExpr, HirCapture, HirDecisionTarget, HirExpr, HirLValue, HirPackTail, HirStmt,
    HirTableField, HirTableKey, HirTableSetList,
};
use crate::hir::expr_safety::expr_requires_ordered_snapshot;

use super::bindings::{
    BindingIndex, BindingUseSummary, binding_from_expr, binding_from_lvalue, matches_binding_ref,
    table_key_from_expr,
};
use super::builder::{ConstructorBuilder, RecordPromotionPolicy};
use super::inline_value::{
    InlineContext, InlineRewriteState, expr_mentions_any_pending_binding, inline_constructor_value,
};
use super::{
    ConstructorEvalEvent, PendingProducer, PendingProducerSource, PreparedRecord,
    ProducerGroupMeta, RebuildScratch, RegionStep, SegmentToken, TableBinding,
};

pub(super) struct RegionRebuildContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    remaining_uses: BindingUseSummary<'a>,
    materialized_binding_counts: &'a [u32],
    dialect: DecompileDialect,
    scratch: &'a mut RebuildScratch,
}

impl<'a> RegionRebuildContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        remaining_uses: BindingUseSummary<'a>,
        materialized_binding_counts: &'a [u32],
        dialect: DecompileDialect,
        scratch: &'a mut RebuildScratch,
    ) -> Self {
        Self {
            block,
            binding_index,
            remaining_uses,
            materialized_binding_counts,
            dialect,
            scratch,
        }
    }
}

pub(super) fn try_extend_constructor_from_steps(
    builder: &mut ConstructorBuilder,
    steps: &[RegionStep],
    context: &mut RegionRebuildContext<'_>,
) -> bool {
    let checkpoint = builder.checkpoint(context.scratch);
    let mut segment_start = 0;

    for (index, step) in steps.iter().enumerate() {
        if let RegionStep::SetList { stmt_index } = step {
            if flush_constructor_segment(
                builder,
                &steps[segment_start..index],
                Some(*stmt_index),
                context,
            )
            .is_none()
            {
                builder.rollback(checkpoint, context.scratch);
                return false;
            }
            segment_start = index + 1;
        }
    }

    if flush_constructor_segment(builder, &steps[segment_start..], None, context).is_none() {
        builder.rollback(checkpoint, context.scratch);
        return false;
    }

    builder.commit(&checkpoint, context.scratch);
    true
}

fn flush_constructor_segment(
    builder: &mut ConstructorBuilder,
    segment: &[RegionStep],
    set_list_stmt_index: Option<usize>,
    context: &mut RegionRebuildContext<'_>,
) -> Option<()> {
    prepare_scratch(context.scratch, context.binding_index.len());
    if builder.trailing_multivalue.is_some()
        && (!segment.is_empty() || set_list_stmt_index.is_some())
    {
        return None;
    }

    if segment.is_empty() {
        if builder.trailing_multivalue.is_some() {
            return set_list_stmt_index.is_none().then_some(());
        }
        if let Some(stmt_index) = set_list_stmt_index {
            let set_list = set_list_stmt(context.block, stmt_index)?;
            if set_list.start_index < builder.next_array_index()
                && !builder.demote_array_suffix(
                    set_list.start_index,
                    &mut context.scratch.restored_array_fields,
                )
            {
                return None;
            }
            builder
                .drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
            if set_list.start_index != builder.next_array_index() {
                return None;
            }
            for value in &set_list.values.fixed {
                builder.push_array_value(value.clone());
            }
            if let Some(trailing) = &set_list.values.tail {
                builder.trailing_multivalue = Some(trailing.clone());
            }
        } else {
            builder
                .drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
        }
        return Some(());
    }

    let expected_set_list_start = if let Some(stmt_index) = set_list_stmt_index {
        let start_index = set_list_stmt(context.block, stmt_index)?.start_index;
        if start_index < builder.next_array_index()
            && !builder.demote_array_suffix(start_index, &mut context.scratch.restored_array_fields)
        {
            return None;
        }
        builder.next_array_index()
    } else {
        builder.next_array_index()
    };

    for step in segment {
        match step {
            RegionStep::Producer {
                stmt_index,
                slot_index,
            } => register_single_producer(
                context.block,
                context.binding_index,
                *stmt_index,
                *slot_index,
                context.scratch,
            )?,
            RegionStep::ProducerGroup { stmt_index } => register_producer_group(
                context.block,
                context.binding_index,
                *stmt_index,
                context.scratch,
            )?,
            RegionStep::Record { stmt_index } => prepare_record_step(*stmt_index, context)?,
            RegionStep::SetList { .. } => {
                unreachable!("set-list should terminate constructor segment")
            }
        }
    }

    if let Some(stmt_index) = set_list_stmt_index {
        let set_list = set_list_stmt(context.block, stmt_index)?;
        if set_list.start_index != expected_set_list_start {
            return None;
        }

        let mut queued_values = VecDeque::from_iter(set_list.values.fixed.iter());
        let tokens = context.scratch.tokens.clone();
        for token in &tokens {
            match token {
                SegmentToken::Producer { producer_index } => {
                    let producer = context.scratch.pending_producers[*producer_index].clone();
                    if context.scratch.consumed_bindings[producer.binding_id] {
                        continue;
                    }
                    flush_set_list_values_before_producer(
                        builder,
                        &mut queued_values,
                        producer.binding,
                        context,
                    )?;
                    match queued_values.front() {
                        Some(front) if matches_binding_ref(front, producer.binding) => {
                            let value = inline_set_list_value(context, front)?;
                            queued_values.pop_front();
                            builder.push_array_value(value);
                        }
                        _ => {}
                    }
                }
                SegmentToken::Record {
                    prepared_record_index,
                } => {
                    append_prepared_record_events(context.scratch, *prepared_record_index);
                    builder.push_record_field_with_policy(
                        context.scratch.prepared_records[*prepared_record_index]
                            .field
                            .clone(),
                        RecordPromotionPolicy::PreserveSetListPrefix {
                            start_index: expected_set_list_start,
                        },
                    );
                }
            }
        }

        for value in queued_values {
            let value = inline_set_list_value(context, value)?;
            builder.push_array_value(value);
        }

        if let Some(trailing) = &set_list.values.tail {
            builder.trailing_multivalue = Some(trailing.clone().try_map_call(|call| {
                let expr = inline_set_list_value(context, &HirExpr::Call(Box::new(call)))?;
                let HirExpr::Call(call) = expr else {
                    return None;
                };
                Some(*call)
            })?);
        }
    }

    if set_list_stmt_index.is_none() {
        let tokens = context.scratch.tokens.clone();
        for token in &tokens {
            if let SegmentToken::Record {
                prepared_record_index,
            } = token
            {
                append_prepared_record_events(context.scratch, *prepared_record_index);
                builder.push_record_field(
                    context.scratch.prepared_records[*prepared_record_index]
                        .field
                        .clone(),
                );
            }
        }
    }

    if context.scratch.pending_producers.iter().any(|producer| {
        if context.scratch.consumed_bindings[producer.binding_id] {
            return false;
        }
        if context.remaining_uses.contains(producer.binding_id) {
            return true;
        }
        match producer.group {
            Some(group) if context.scratch.consumed_groups[group] => false,
            Some(group) => !context.scratch.producer_groups[group].drop_without_consumption_is_safe,
            None => true,
        }
    }) {
        return None;
    }

    if !constructor_eval_order_is_preserved(set_list_stmt_index, context) {
        return None;
    }

    if set_list_stmt_index.is_none() {
        builder.drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
    }

    Some(())
}

fn flush_set_list_values_before_producer(
    builder: &mut ConstructorBuilder,
    queued_values: &mut VecDeque<&HirExpr>,
    producer_binding: TableBinding,
    context: &mut RegionRebuildContext<'_>,
) -> Option<()> {
    let Some(target_offset) = queued_values
        .iter()
        .position(|value| matches_binding_ref(value, producer_binding))
    else {
        return Some(());
    };

    for _ in 0..target_offset {
        let front = queued_values.front()?;
        if expr_mentions_any_pending_binding(
            front,
            context.binding_index,
            &context.scratch.producer_index_by_binding,
        ) {
            return None;
        }
        let value = queued_values.pop_front()?;
        let value = inline_set_list_value(context, value)?;
        builder.push_array_value(value);
    }
    Some(())
}

fn inline_set_list_value(
    context: &mut RegionRebuildContext<'_>,
    value: &HirExpr,
) -> Option<HirExpr> {
    let scratch = &mut context.scratch;
    let mut inline_context = InlineContext::new(
        context.block,
        context.binding_index,
        &scratch.pending_producers,
        &scratch.producer_index_by_binding,
        InlineRewriteState {
            consumed_bindings: &mut scratch.consumed_bindings,
            consumed_groups: &mut scratch.consumed_groups,
            eval_events: &mut scratch.generated_eval_events,
        },
        context.remaining_uses,
    );
    inline_constructor_value(&mut inline_context, value)
}

fn append_prepared_record_events(scratch: &mut RebuildScratch, record_index: usize) {
    let range = scratch.prepared_records[record_index].eval_events.clone();
    scratch
        .generated_eval_events
        .extend_from_slice(&scratch.prepared_eval_events[range]);
}

fn constructor_eval_order_is_preserved(
    set_list_stmt_index: Option<usize>,
    context: &RegionRebuildContext<'_>,
) -> bool {
    let scratch = &context.scratch;
    let mut expected = scratch.source_eval_events.clone();
    if let Some(stmt_index) = set_list_stmt_index {
        let Some(set_list) = set_list_stmt(context.block, stmt_index) else {
            return false;
        };
        for value in &set_list.values.fixed {
            collect_source_eval_events(
                value,
                context.binding_index,
                &scratch.producer_index_by_binding,
                &mut expected,
            );
        }
        if let Some(tail) = &set_list.values.tail {
            collect_source_eval_events(
                tail.as_expr(),
                context.binding_index,
                &scratch.producer_index_by_binding,
                &mut expected,
            );
        }
    }
    expected == scratch.generated_eval_events
}

fn collect_source_eval_events(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producer_index_by_binding: &[Option<usize>],
    events: &mut Vec<ConstructorEvalEvent>,
) {
    if binding_from_expr(expr)
        .and_then(|binding| binding_index.id_of(binding))
        .and_then(|binding_id| producer_index_by_binding.get(binding_id))
        .is_some_and(Option::is_some)
    {
        return;
    }

    match expr {
        HirExpr::Unary(unary) => collect_source_eval_events(
            &unary.expr,
            binding_index,
            producer_index_by_binding,
            events,
        ),
        HirExpr::Binary(binary) => {
            for value in [&binary.lhs, &binary.rhs] {
                collect_source_eval_events(value, binding_index, producer_index_by_binding, events);
            }
        }
        HirExpr::TableAccess(access) => {
            for value in [&access.base, &access.key] {
                collect_source_eval_events(value, binding_index, producer_index_by_binding, events);
            }
        }
        HirExpr::Call(call) => {
            if call.fastcall.is_some() {
                for value in &call.args {
                    collect_source_eval_events(
                        value,
                        binding_index,
                        producer_index_by_binding,
                        events,
                    );
                }
                collect_source_eval_events(
                    &call.callee,
                    binding_index,
                    producer_index_by_binding,
                    events,
                );
            } else {
                for value in std::iter::once(&call.callee).chain(&call.args) {
                    collect_source_eval_events(
                        value,
                        binding_index,
                        producer_index_by_binding,
                        events,
                    );
                }
            }
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_source_eval_events(
                &logical.lhs,
                binding_index,
                producer_index_by_binding,
                events,
            );
        }
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
        | HirExpr::TempRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Decision(_)
        | HirExpr::Unresolved(_) => {}
    }
    if expr_requires_ordered_snapshot(expr) {
        events.push(ConstructorEvalEvent::Barrier);
    }
}

fn prepare_scratch(scratch: &mut RebuildScratch, binding_count: usize) {
    scratch.pending_producers.clear();
    scratch.producer_groups.clear();
    scratch.tokens.clear();
    scratch.prepared_records.clear();
    scratch.prepared_eval_events.clear();
    scratch.source_eval_events.clear();
    scratch.generated_eval_events.clear();
    scratch.consumed_groups.clear();
    reset_touched_bindings(scratch);
    ensure_binding_capacity(scratch, binding_count);
}

fn reset_touched_bindings(scratch: &mut RebuildScratch) {
    for binding_id in scratch.touched_binding_ids.drain(..) {
        scratch.producer_index_by_binding[binding_id] = None;
        scratch.consumed_bindings[binding_id] = false;
        scratch.removed_materializations[binding_id] = 0;
    }
}

fn ensure_binding_capacity(scratch: &mut RebuildScratch, binding_count: usize) {
    if scratch.producer_index_by_binding.len() < binding_count {
        scratch
            .producer_index_by_binding
            .resize(binding_count, None);
    }
    if scratch.consumed_bindings.len() < binding_count {
        scratch.consumed_bindings.resize(binding_count, false);
    }
    if scratch.removed_materializations.len() < binding_count {
        scratch.removed_materializations.resize(binding_count, 0);
    }
}

fn mark_binding_active(scratch: &mut RebuildScratch, binding_id: usize) {
    if scratch.producer_index_by_binding[binding_id].is_none() {
        scratch.touched_binding_ids.push(binding_id);
    }
}

fn register_single_producer(
    block: &HirBlock,
    binding_index: &BindingIndex,
    stmt_index: usize,
    slot_index: usize,
    scratch: &mut RebuildScratch,
) -> Option<()> {
    let producer = single_producer(block, binding_index, stmt_index, slot_index)?;
    let producer_index = scratch.pending_producers.len();
    mark_binding_active(scratch, producer.binding_id);
    scratch.producer_index_by_binding[producer.binding_id] = Some(producer_index);
    scratch.removed_materializations[producer.binding_id] += 1;
    scratch.pending_producers.push(producer);
    if pending_producer_value(block, &scratch.pending_producers[producer_index])
        .is_some_and(expr_requires_ordered_snapshot)
    {
        scratch
            .source_eval_events
            .push(ConstructorEvalEvent::Producer(producer_index));
    }
    scratch
        .tokens
        .push(SegmentToken::Producer { producer_index });
    Some(())
}

fn register_producer_group(
    block: &HirBlock,
    binding_index: &BindingIndex,
    stmt_index: usize,
    scratch: &mut RebuildScratch,
) -> Option<()> {
    let (bindings, source) = producer_group_stmt(block, stmt_index)?;
    let group_id = scratch.producer_groups.len();
    scratch.producer_groups.push(ProducerGroupMeta {
        drop_without_consumption_is_safe: can_drop_open_pack_source_if_unused(source),
    });
    scratch.consumed_groups.push(false);

    for (slot_index, binding) in bindings.into_iter().enumerate() {
        let binding_id = binding_index.id_of(binding)?;
        let source = if slot_index == 0 {
            PendingProducerSource::Tail { stmt_index }
        } else {
            PendingProducerSource::Empty
        };
        let producer_index = scratch.pending_producers.len();
        mark_binding_active(scratch, binding_id);
        scratch.producer_index_by_binding[binding_id] = Some(producer_index);
        scratch.removed_materializations[binding_id] += 1;
        scratch.pending_producers.push(PendingProducer {
            binding,
            binding_id,
            source,
            group: Some(group_id),
        });
        if pending_producer_value(block, &scratch.pending_producers[producer_index])
            .is_some_and(expr_requires_ordered_snapshot)
        {
            scratch
                .source_eval_events
                .push(ConstructorEvalEvent::Producer(producer_index));
        }
        scratch
            .tokens
            .push(SegmentToken::Producer { producer_index });
    }

    Some(())
}

fn prepare_record_step(stmt_index: usize, context: &mut RegionRebuildContext<'_>) -> Option<()> {
    let (key, value) = record_field_parts(context.block, stmt_index, context.dialect)?;
    if let HirTableKey::Expr(key_expr) = &key {
        collect_source_eval_events(
            key_expr,
            context.binding_index,
            &context.scratch.producer_index_by_binding,
            &mut context.scratch.source_eval_events,
        );
    }
    collect_source_eval_events(
        value,
        context.binding_index,
        &context.scratch.producer_index_by_binding,
        &mut context.scratch.source_eval_events,
    );
    let eval_event_start = context.scratch.prepared_eval_events.len();
    // 内联 record key 表达式：如果 key 是一个引用了 pending producer 的变量引用
    // （例如 `local k = "name"; t[k] = v`），把 producer 值折叠进 key 并消费绑定。
    let key = match key {
        HirTableKey::Expr(key_expr) => {
            let inlined = {
                let scratch = &mut context.scratch;
                let mut inline_context = InlineContext::new(
                    context.block,
                    context.binding_index,
                    &scratch.pending_producers,
                    &scratch.producer_index_by_binding,
                    InlineRewriteState {
                        consumed_bindings: &mut scratch.consumed_bindings,
                        consumed_groups: &mut scratch.consumed_groups,
                        eval_events: &mut scratch.prepared_eval_events,
                    },
                    context.remaining_uses,
                );
                inline_constructor_value(&mut inline_context, &key_expr)?
            };
            table_key_from_expr(&inlined, context.dialect)
        }
        name => name,
    };
    let recursive_closure_slot = binding_is_recursive_closure_slot(
        context.block,
        value,
        context.binding_index,
        &context.scratch.pending_producers,
        &context.scratch.producer_index_by_binding,
    );
    let value = {
        let scratch = &mut context.scratch;
        let mut inline_context = InlineContext::new(
            context.block,
            context.binding_index,
            &scratch.pending_producers,
            &scratch.producer_index_by_binding,
            InlineRewriteState {
                consumed_bindings: &mut scratch.consumed_bindings,
                consumed_groups: &mut scratch.consumed_groups,
                eval_events: &mut scratch.prepared_eval_events,
            },
            context.remaining_uses,
        );
        inline_constructor_value(&mut inline_context, value)?
    };
    if matches!(value, HirExpr::Closure(_)) && recursive_closure_slot {
        return None;
    }
    if expr_captures_orphaned_binding(
        &value,
        context.binding_index,
        context.materialized_binding_counts,
        &context.scratch.removed_materializations,
    ) {
        return None;
    }
    let prepared_record_index = context.scratch.prepared_records.len();
    context.scratch.prepared_records.push(PreparedRecord {
        field: crate::hir::common::HirRecordField { key, value },
        eval_events: eval_event_start..context.scratch.prepared_eval_events.len(),
    });
    context.scratch.tokens.push(SegmentToken::Record {
        prepared_record_index,
    });
    Some(())
}

fn record_field_parts(
    block: &HirBlock,
    stmt_index: usize,
    dialect: DecompileDialect,
) -> Option<(HirTableKey, &HirExpr)> {
    let HirStmt::Assign(assign) = block.stmts.get(stmt_index)? else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    Some((table_key_from_expr(&access.key, dialect), value))
}

fn set_list_stmt(block: &HirBlock, stmt_index: usize) -> Option<&HirTableSetList> {
    let HirStmt::TableSetList(set_list) = block.stmts.get(stmt_index)? else {
        return None;
    };
    Some(set_list)
}

fn single_producer(
    block: &HirBlock,
    binding_index: &BindingIndex,
    stmt_index: usize,
    slot_index: usize,
) -> Option<PendingProducer> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let binding = TableBinding::Local(*local_decl.bindings.get(slot_index)?);
            Some(PendingProducer {
                binding,
                binding_id: binding_index.id_of(binding)?,
                source: PendingProducerSource::Value {
                    stmt_index,
                    value_index: slot_index,
                },
                group: None,
            })
        }
        HirStmt::Assign(assign) => {
            let binding = binding_from_lvalue(assign.targets.get(slot_index)?)?;
            Some(PendingProducer {
                binding,
                binding_id: binding_index.id_of(binding)?,
                source: PendingProducerSource::Value {
                    stmt_index,
                    value_index: slot_index,
                },
                group: None,
            })
        }
        _ => None,
    }
}

/// A producer declaration is removable only when its value cannot carry a source-visible
/// object/root.  A table field may be cleared before the producer's lexical scope ends, so
/// aliases, calls, constructors, strings, and unknown expressions must retain their explicit
/// materialization even if the constructor would otherwise consume them exactly once.
pub(super) fn producer_value_can_be_dropped(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
    )
}

fn producer_group_stmt(
    block: &HirBlock,
    stmt_index: usize,
) -> Option<(Vec<TableBinding>, &HirPackTail)> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            if !local_decl.values.fixed.is_empty() {
                return None;
            }
            let source = local_decl.values.tail.as_ref()?;
            Some((
                local_decl
                    .bindings
                    .iter()
                    .copied()
                    .map(TableBinding::Local)
                    .collect(),
                source,
            ))
        }
        HirStmt::Assign(assign) => {
            if !assign.values.fixed.is_empty() {
                return None;
            }
            let source = assign.values.tail.as_ref()?;
            let bindings = assign
                .targets
                .iter()
                .map(binding_from_lvalue)
                .collect::<Option<Vec<_>>>()?;
            Some((bindings, source))
        }
        _ => None,
    }
}

fn can_drop_open_pack_source_if_unused(tail: &HirPackTail) -> bool {
    matches!(tail.as_expr(), HirExpr::VarArg)
}

fn pending_producer_value<'a>(
    block: &'a HirBlock,
    producer: &PendingProducer,
) -> Option<&'a HirExpr> {
    match producer.source {
        PendingProducerSource::Value {
            stmt_index,
            value_index,
        } => match block.stmts.get(stmt_index)? {
            HirStmt::LocalDecl(local_decl) => local_decl.values.fixed.get(value_index),
            HirStmt::Assign(assign) => assign.values.fixed.get(value_index),
            _ => None,
        },
        PendingProducerSource::Tail { stmt_index } => match block.stmts.get(stmt_index)? {
            HirStmt::LocalDecl(local_decl) => {
                local_decl.values.tail.as_ref().map(HirPackTail::as_expr)
            }
            HirStmt::Assign(assign) => assign.values.tail.as_ref().map(HirPackTail::as_expr),
            _ => None,
        },
        PendingProducerSource::Empty => None,
    }
}
