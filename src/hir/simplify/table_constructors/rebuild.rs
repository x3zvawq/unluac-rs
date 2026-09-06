//! 这个子模块负责把扫描得到的 region steps 重建回表构造器。
//!
//! 它依赖 `scan` 产出的带 producer 投影与字段/batch 引用的 step 和安全内联结果，按顺序 flush
//! 片段，不会回头重新判定哪个 stmt 属于候选 region。
//! 例如：一串 `record/setlist/producer` step 会在这里重新拼成 `HirTableConstructor`；
//! producer、record key/value 的求值事件序列不一致时，整个推测事务回滚。

use std::collections::VecDeque;

mod captures;
use captures::*;

use crate::hir::common::{
    HirBlock, HirCallExpr, HirCapture, HirDecisionTarget, HirExpr, HirTableField, HirTableSetList,
};
use crate::hir::expr_safety::expr_requires_ordered_snapshot;

use super::bindings::{BindingIndex, BindingUseSummary, binding_from_expr, matches_binding_ref};
use super::builder::{ConstructorBuilder, RecordPromotionPolicy};
use super::inline_value::{InlineContext, InlineRewriteState, inline_constructor_value};
use super::{
    ConstructorEvalEvent, PendingProducer, PendingProducerSource, PreparedRecord,
    ProducerSourcePreservation, RebuildScratch, RegionStep, SegmentToken, TableBinding,
};
use crate::hir::value_facts::value_facts;

pub(super) struct RegionRebuildContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    remaining_uses: BindingUseSummary<'a>,
    materialized_binding_counts: &'a [u32],
    scratch: &'a mut RebuildScratch,
}

impl<'a> RegionRebuildContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        remaining_uses: BindingUseSummary<'a>,
        materialized_binding_counts: &'a [u32],
        scratch: &'a mut RebuildScratch,
    ) -> Self {
        Self {
            block,
            binding_index,
            remaining_uses,
            materialized_binding_counts,
            scratch,
        }
    }
}

pub(super) fn try_extend_constructor_from_steps(
    builder: &mut ConstructorBuilder,
    steps: &[RegionStep<'_>],
    context: &mut RegionRebuildContext<'_>,
) -> Option<Vec<usize>> {
    let checkpoint = builder.checkpoint(context.scratch);
    let mut segment_start = 0;
    let mut preserved_producer_sources = Vec::new();

    for (index, step) in steps.iter().enumerate() {
        if let RegionStep::SetList { batch, .. } = step {
            if flush_constructor_segment(
                builder,
                &steps[segment_start..index],
                Some(batch),
                context,
                &mut preserved_producer_sources,
            )
            .is_none()
            {
                builder.rollback(checkpoint, context.scratch);
                return None;
            }
            segment_start = index + 1;
        }
    }

    if flush_constructor_segment(
        builder,
        &steps[segment_start..],
        None,
        context,
        &mut preserved_producer_sources,
    )
    .is_none()
    {
        builder.rollback(checkpoint, context.scratch);
        return None;
    }

    if !builder.fits_preallocated_field_count() {
        builder.rollback(checkpoint, context.scratch);
        return None;
    }
    builder.commit(&checkpoint, context.scratch);
    Some(preserved_producer_sources)
}

fn flush_constructor_segment(
    builder: &mut ConstructorBuilder,
    segment: &[RegionStep<'_>],
    set_list: Option<&HirTableSetList>,
    context: &mut RegionRebuildContext<'_>,
    preserved_producer_sources: &mut Vec<usize>,
) -> Option<()> {
    prepare_scratch(context.scratch, context.binding_index.len());
    if builder.trailing_multivalue.is_some() && (!segment.is_empty() || set_list.is_some()) {
        // 候选拒绝[SemanticBarrier:ValueArity]：constructor 的 open tail 已决定后续数组槽；
        // 再吸收字段会改变多返回值覆盖范围，反例见 regress_52_table_trailing_multivalue_boundary。
        return None;
    }

    if segment.is_empty() {
        if builder.trailing_multivalue.is_some() {
            return set_list.is_none().then_some(());
        }
        if let Some(set_list) = set_list {
            if set_list.start_index < builder.next_array_index()
                && !builder.demote_array_suffix(
                    set_list.start_index,
                    &mut context.scratch.restored_array_fields,
                )
            {
                // 候选拒绝[SemanticBarrier:TableShape]：唯一失败形状是 raw SETLIST
                // 起点 0；吸收到 constructor array 会把原键 0 改写成键 1。
                return None;
            }
            builder
                .drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
            if set_list.start_index != builder.next_array_index() {
                // 候选拒绝[SemanticBarrier:TableShape]：SETLIST 起点与隐式数组下标不连续，
                // 直接追加会改写键集合与 `#table` 结果。
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

    let expected_set_list_start = if let Some(set_list) = set_list {
        let start_index = set_list.start_index;
        if start_index < builder.next_array_index()
            && !builder.demote_array_suffix(start_index, &mut context.scratch.restored_array_fields)
        {
            // 候选拒绝[SemanticBarrier:TableShape]：唯一失败形状是 raw SETLIST
            // 起点 0；吸收到 constructor array 会把原键 0 改写成键 1。
            return None;
        }
        // 索引式构造器先用 record 写入固定前缀，末尾才是 open SETLIST。
        // 前层布局证书允许本段 record 填满前缀；在 tail 提交前仍必须精确核对起点。
        if builder.has_indexed_array_layout()
            && set_list.values.fixed.is_empty()
            && set_list.values.tail.is_some()
        {
            start_index
        } else {
            builder.next_array_index()
        }
    } else {
        builder.next_array_index()
    };

    for step in segment {
        match step {
            RegionStep::Producer {
                binding,
                source,
                value,
                source_preservation,
                ..
            } => register_single_producer(
                context.binding_index,
                *binding,
                *source,
                value,
                *source_preservation,
                context.scratch,
            ),
            RegionStep::Record { key, value, .. } => prepare_record_step(key, value, context)?,
            RegionStep::SetList { .. } => {
                unreachable!("set-list should terminate constructor segment")
            }
        }
    }

    if let Some(set_list) = set_list {
        if set_list.start_index != expected_set_list_start {
            // 候选拒绝[SemanticBarrier:TableShape]：producer/record 不能改变 raw SETLIST 的
            // 固定起点；否则隐式 array key 与原字节码不一致。
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
            if set_list.values.fixed.is_empty()
                && builder.next_array_index() != set_list.start_index
            {
                return None;
            }
            builder.trailing_multivalue = Some(trailing.clone().try_map_call(|call| {
                let expr = inline_set_list_value(context, &HirExpr::Call(Box::new(call)))?;
                let HirExpr::Call(call) = expr else {
                    return None;
                };
                Some(*call)
            })?);
        }
    }

    if set_list.is_none() {
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

    for producer in &context.scratch.pending_producers {
        if !context.scratch.consumed_bindings[producer.binding_id]
            || context.remaining_uses.contains(producer.binding_id)
        {
            preserve_producer_source(producer, preserved_producer_sources)?;
        }
    }

    if !constructor_eval_order_is_preserved(set_list, context) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：source/generated 事件序列不同会重排 lookup、
        // call 或元方法；反例见 regress_212 与 regress_235。
        return None;
    }

    if set_list.is_none() {
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
        let value = queued_values.pop_front()?;
        // 所有 producer 已在 segment 预注册；允许队首递归消费稍后 token 的依赖，随后
        // token 会因 consumed 跳过。source/generated event 序列在事务末比较，因此 effectful
        // producer 若被拓扑重排仍会回滚，eventless 依赖则无需 blanket 拒绝。
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
    set_list: Option<&HirTableSetList>,
    context: &RegionRebuildContext<'_>,
) -> bool {
    let scratch = &context.scratch;
    let mut expected = scratch.source_eval_events.clone();
    if let Some(set_list) = set_list {
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
        HirExpr::Decision(decision) => {
            if let Some(entry) = decision.nodes.get(decision.entry.index()) {
                collect_source_eval_events(
                    &entry.test,
                    binding_index,
                    producer_index_by_binding,
                    events,
                );
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => collect_source_eval_events(
                        value,
                        binding_index,
                        producer_index_by_binding,
                        events,
                    ),
                    HirTableField::Record(field) => {
                        collect_source_eval_events(
                            &field.key,
                            binding_index,
                            producer_index_by_binding,
                            events,
                        );
                        collect_source_eval_events(
                            &field.value,
                            binding_index,
                            producer_index_by_binding,
                            events,
                        );
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                collect_source_eval_events(
                    tail.as_expr(),
                    binding_index,
                    producer_index_by_binding,
                    events,
                );
            }
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
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
    if expr_requires_ordered_snapshot(expr) {
        events.push(ConstructorEvalEvent::Barrier);
    }
}

fn prepare_scratch(scratch: &mut RebuildScratch, binding_count: usize) {
    scratch.pending_producers.clear();
    scratch.tokens.clear();
    scratch.prepared_records.clear();
    scratch.prepared_eval_events.clear();
    scratch.source_eval_events.clear();
    scratch.generated_eval_events.clear();
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
    binding_index: &BindingIndex,
    binding: TableBinding,
    source: PendingProducerSource,
    value: &HirExpr,
    source_preservation: ProducerSourcePreservation,
    scratch: &mut RebuildScratch,
) {
    let producer = PendingProducer {
        binding,
        binding_id: binding_index
            .id_of(binding)
            .expect("scanned producer is indexed"),
        source,
        source_preservation,
    };
    let producer_index = scratch.pending_producers.len();
    mark_binding_active(scratch, producer.binding_id);
    scratch.producer_index_by_binding[producer.binding_id] = Some(producer_index);
    scratch.removed_materializations[producer.binding_id] += 1;
    scratch.pending_producers.push(producer);
    if expr_requires_ordered_snapshot(value) {
        scratch
            .source_eval_events
            .push(ConstructorEvalEvent::Producer(producer_index));
    }
    scratch
        .tokens
        .push(SegmentToken::Producer { producer_index });
}

fn prepare_record_step(
    key: &HirExpr,
    value: &HirExpr,
    context: &mut RegionRebuildContext<'_>,
) -> Option<()> {
    collect_source_eval_events(
        key,
        context.binding_index,
        &context.scratch.producer_index_by_binding,
        &mut context.scratch.source_eval_events,
    );
    collect_source_eval_events(
        value,
        context.binding_index,
        &context.scratch.producer_index_by_binding,
        &mut context.scratch.source_eval_events,
    );
    let eval_event_start = context.scratch.prepared_eval_events.len();
    // 内联 record key 表达式：如果 key 是一个引用了 pending producer 的变量引用
    // （例如 `local k = "name"; t[k] = v`），把 producer 值折叠进 key 并消费绑定。
    let key = {
        let scratch = &mut context.scratch;
        let mut inline_context = InlineContext::new(
            context.block,
            context.binding_index,
            &scratch.pending_producers,
            &scratch.producer_index_by_binding,
            InlineRewriteState {
                consumed_bindings: &mut scratch.consumed_bindings,
                eval_events: &mut scratch.prepared_eval_events,
            },
            context.remaining_uses,
        );
        inline_constructor_value(&mut inline_context, key)?
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
                eval_events: &mut scratch.prepared_eval_events,
            },
            context.remaining_uses,
        );
        inline_constructor_value(&mut inline_context, value)?
    };
    if matches!(value, HirExpr::Closure(_)) && recursive_closure_slot {
        // 候选拒绝[SemanticBarrier:Capture]：删除递归 closure 的独立 binding 会让 closure
        // 捕获失去自身 owner，例如 `local f; f = function() return f end; t.x = f`。
        return None;
    }
    if expr_captures_orphaned_binding(
        &value,
        context.binding_index,
        context.materialized_binding_counts,
        &context.scratch.removed_materializations,
    ) {
        // 候选拒绝[SemanticBarrier:Capture]：被删除的最后一次 materialization 仍被 closure
        // 捕获会产生 orphan upvalue；反例见 regress_224_table_capture_writeback。
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

fn preserve_producer_source(
    producer: &PendingProducer,
    preserved_stmt_indices: &mut Vec<usize>,
) -> Option<()> {
    match producer.source_preservation {
        ProducerSourcePreservation::Safe => {}
        ProducerSourcePreservation::InertWholeStatement => {}
        ProducerSourcePreservation::DebugIdentity => {
            // 候选拒绝[PolicyBoundary]：把字段提前到 source-visible producer 声明之前会让
            // hook 在该声明行观察到已填充的 table；debug identity 声明必须保持原边界。
            return None;
        }
        ProducerSourcePreservation::ObservableReplay => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：保留并内联 effectful producer 会重复求值，
            // 未消费时保留又会让后续字段越过它；`mark()` 次数/顺序由 regress_235 观察。
            return None;
        }
        ProducerSourcePreservation::UnsupportedShape => {
            // 候选拒绝[PolicyBoundary]：scanner 已把逐槽 primitive/vararg、snapshot 与
            // allocation 分流；这里只剩 permissive 输出必须原样保留的 Unresolved 失败证据。
            return None;
        }
    }

    let stmt_index = match producer.source {
        PendingProducerSource::Value { stmt_index, .. }
        | PendingProducerSource::ImplicitNil { stmt_index } => stmt_index,
    };
    if !preserved_stmt_indices.contains(&stmt_index) {
        preserved_stmt_indices.push(stmt_index);
    }
    Some(())
}

/// producer 的结果根分类来自共享值域；区域 evaluator 独立保留求值事件及顺序。
/// 例如比较结果是 boolean，不代表调用其元方法的求值本身可以删除。
pub(super) fn producer_value_can_be_dropped(expr: &HirExpr) -> bool {
    value_facts(expr).is_gc_inert()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::{
        HirBlock, HirExpr, HirLocalDecl, HirStmt, HirTableConstructor, HirTableField,
        HirTableSetList, HirValuePack, LocalId,
    };
    use crate::hir::promotion::ProtoPromotionFacts;

    use super::super::bindings::{
        BindingIndex, BindingOccurrenceIndex, BindingSlots, collect_stmt_binding_summary,
    };
    use super::super::builder::ConstructorBuilder;
    use super::super::{
        PendingProducerSource, ProducerSourcePreservation, RebuildScratch, RegionStep, TableBinding,
    };
    use super::{RegionRebuildContext, try_extend_constructor_from_steps};

    #[test]
    fn set_list_topologically_consumes_eventless_later_producer() {
        let table = LocalId(0);
        let first = LocalId(1);
        let second = LocalId(2);
        let local = |binding, value| {
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![binding],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
            }))
        };
        let block = HirBlock {
            stmts: vec![
                local(table, HirExpr::TableConstructor(Box::default())),
                local(first, HirExpr::Integer(1)),
                local(second, HirExpr::Integer(2)),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(table),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![
                        HirExpr::LocalRef(second),
                        HirExpr::LocalRef(first),
                    ]),
                })),
            ],
        };
        let mut binding_index = BindingIndex::new(0, 3);
        let summaries = block
            .stmts
            .iter()
            .map(|stmt| collect_stmt_binding_summary(stmt, &mut binding_index))
            .collect::<Vec<_>>();
        let empty_binding_flags = BindingSlots::from_debug_hints(&[], &[None, None, None]);
        let occurrences = BindingOccurrenceIndex::new(
            &binding_index,
            &summaries,
            &empty_binding_flags,
            &BTreeSet::new(),
            &empty_binding_flags,
            &ProtoPromotionFacts::default(),
        );
        let mut scratch = RebuildScratch::default();
        let mut builder = ConstructorBuilder::from_constructor(HirTableConstructor::default());
        let materialized_counts = vec![1; binding_index.len()];
        let mut context = RegionRebuildContext::new(
            &block,
            &binding_index,
            occurrences.remaining_uses_after(3),
            &materialized_counts,
            &mut scratch,
        );

        assert!(
            try_extend_constructor_from_steps(
                &mut builder,
                &[
                    RegionStep::Producer {
                        binding: TableBinding::Local(first),
                        source: PendingProducerSource::Value {
                            stmt_index: 1,
                            value_index: 0
                        },
                        value: &HirExpr::Integer(1),
                        scalar_call: false,
                        source_gc_inert: true,
                        source_preservation: ProducerSourcePreservation::Safe,
                    },
                    RegionStep::Producer {
                        binding: TableBinding::Local(second),
                        source: PendingProducerSource::Value {
                            stmt_index: 2,
                            value_index: 0
                        },
                        value: &HirExpr::Integer(2),
                        scalar_call: false,
                        source_gc_inert: true,
                        source_preservation: ProducerSourcePreservation::Safe,
                    },
                    RegionStep::SetList {
                        stmt_index: 3,
                        batch: match &block.stmts[3] {
                            HirStmt::TableSetList(batch) => batch,
                            _ => unreachable!(),
                        }
                    },
                ],
                &mut context,
            )
            .is_some()
        );
        assert_eq!(
            builder.into_constructor().fields,
            vec![
                HirTableField::Array(HirExpr::Integer(2)),
                HirTableField::Array(HirExpr::Integer(1)),
            ]
        );
    }
}
