//! 这个子模块负责把扫描得到的 region steps 重建回表构造器。
//!
//! 它依赖 `scan` 产出的轻量 step 描述和 `inline_value` 的安全内联结果，只负责按顺序 flush
//! 片段，不会回头重新判定哪个 stmt 属于候选 region。
//! 例如：一串 `record/setlist/producer` step 会在这里重新拼成 `HirTableConstructor`。

use std::collections::{BTreeMap, VecDeque};

use crate::hir::common::{
    HirBlock, HirCallExpr, HirCapture, HirDecisionTarget, HirExpr, HirLValue, HirStmt,
    HirTableConstructor, HirTableField, HirTableKey, HirTableSetList,
};

use super::bindings::{
    BindingIndex, BindingUseSummary, binding_from_expr, binding_from_lvalue, matches_binding_ref,
    table_key_from_expr,
};
use super::inline_value::{InlineContext, inline_constructor_value};
use super::{
    PendingProducer, PendingProducerSource, ProducerGroupMeta, RebuildScratch, RegionStep,
    RestoredPendingIntegerField, SegmentToken, TableBinding,
};

#[derive(Debug, Clone)]
enum BuilderField {
    Final(HirTableField),
    PendingInt { key: i64, value: HirExpr },
    MovedPendingInt,
}

#[derive(Debug, Clone, Copy)]
enum RecordPromotionPolicy {
    Normal,
    PreserveSetListPrefix { start_index: u32 },
}

#[derive(Debug, Clone)]
pub(super) struct ConstructorBuilder {
    fields: Vec<BuilderField>,
    trailing_multivalue: Option<HirExpr>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, usize>,
}

#[derive(Debug, Clone)]
struct BuilderCheckpoint {
    fields_len: usize,
    trailing_multivalue: Option<HirExpr>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, usize>,
    restored_pending_integer_fields_len: usize,
}

pub(super) struct RegionRebuildContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    remaining_uses: &'a BindingUseSummary,
    allow_closure_records_prefix: bool,
    materialized_binding_counts: &'a [u32],
    scratch: &'a mut RebuildScratch,
}

impl<'a> RegionRebuildContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        remaining_uses: &'a BindingUseSummary,
        allow_closure_records_prefix: bool,
        materialized_binding_counts: &'a [u32],
        scratch: &'a mut RebuildScratch,
    ) -> Self {
        Self {
            block,
            binding_index,
            remaining_uses,
            allow_closure_records_prefix,
            materialized_binding_counts,
            scratch,
        }
    }

    fn region_contains_set_list(&self, steps: &[RegionStep]) -> bool {
        self.allow_closure_records_prefix
            || steps
                .iter()
                .any(|step| matches!(step, RegionStep::SetList { .. }))
    }
}

impl ConstructorBuilder {
    pub(super) fn from_constructor(constructor: HirTableConstructor) -> Self {
        let mut builder = Self {
            fields: Vec::with_capacity(constructor.fields.len()),
            trailing_multivalue: constructor.trailing_multivalue,
            next_array_index: 1,
            pending_integer_fields: BTreeMap::new(),
        };
        for field in constructor.fields {
            match field {
                HirTableField::Array(value) => {
                    builder.push_array_value(value);
                }
                HirTableField::Record(field) => {
                    builder.push_record_field(field);
                }
            }
        }
        builder
    }

    pub(super) fn into_constructor(self) -> HirTableConstructor {
        let mut fields = Vec::with_capacity(self.fields.len());
        for field in self.fields {
            match field {
                BuilderField::Final(field) => fields.push(field),
                BuilderField::PendingInt { key, value } => {
                    fields.push(HirTableField::Record(crate::hir::common::HirRecordField {
                        key: HirTableKey::Expr(HirExpr::Integer(key)),
                        value,
                    }));
                }
                BuilderField::MovedPendingInt => {}
            }
        }
        HirTableConstructor {
            fields,
            trailing_multivalue: self.trailing_multivalue,
        }
    }

    fn checkpoint(&self, scratch: &RebuildScratch) -> BuilderCheckpoint {
        BuilderCheckpoint {
            fields_len: self.fields.len(),
            trailing_multivalue: self.trailing_multivalue.clone(),
            next_array_index: self.next_array_index,
            pending_integer_fields: self.pending_integer_fields.clone(),
            restored_pending_integer_fields_len: scratch.restored_pending_integer_fields.len(),
        }
    }

    fn rollback(&mut self, checkpoint: BuilderCheckpoint, scratch: &mut RebuildScratch) {
        self.fields.truncate(checkpoint.fields_len);
        self.trailing_multivalue = checkpoint.trailing_multivalue;
        self.next_array_index = checkpoint.next_array_index;
        self.pending_integer_fields = checkpoint.pending_integer_fields;
        for restored in scratch.restored_pending_integer_fields
            [checkpoint.restored_pending_integer_fields_len..]
            .iter()
            .rev()
        {
            self.fields[restored.field_index] = BuilderField::PendingInt {
                key: restored.key,
                value: restored.value.clone(),
            };
        }
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
    }

    fn commit(&mut self, checkpoint: &BuilderCheckpoint, scratch: &mut RebuildScratch) {
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
    }

    fn next_array_index(&self) -> u32 {
        self.next_array_index
    }

    fn push_array_value(&mut self, value: HirExpr) {
        self.fields.push(BuilderField::Final(HirTableField::Array(value)));
        self.next_array_index += 1;
    }

    fn push_record_field(&mut self, field: crate::hir::common::HirRecordField) {
        self.push_record_field_with_policy(field, RecordPromotionPolicy::Normal);
    }

    fn push_record_field_with_policy(
        &mut self,
        field: crate::hir::common::HirRecordField,
        policy: RecordPromotionPolicy,
    ) {
        let current_next_index = i64::from(self.next_array_index);
        match field.key {
            HirTableKey::Expr(HirExpr::Integer(value))
                if matches!(policy, RecordPromotionPolicy::Normal) && value == current_next_index =>
            {
                self.push_array_value(field.value);
            }
            HirTableKey::Expr(HirExpr::Integer(value))
                if can_stage_pending_integer_record(
                    value,
                    current_next_index,
                    &field.value,
                    policy,
                ) =>
            {
                if let std::collections::btree_map::Entry::Vacant(entry) =
                    self.pending_integer_fields.entry(value)
                {
                    let field_index = self.fields.len();
                    self.fields.push(BuilderField::PendingInt {
                        key: value,
                        value: field.value,
                    });
                    entry.insert(field_index);
                } else {
                    self.fields.push(BuilderField::Final(HirTableField::Record(
                        crate::hir::common::HirRecordField {
                            key: HirTableKey::Expr(HirExpr::Integer(value)),
                            value: field.value,
                        },
                    )));
                }
            }
            key => self.fields.push(BuilderField::Final(HirTableField::Record(
                crate::hir::common::HirRecordField {
                    key,
                    value: field.value,
                },
            ))),
        }
    }

    fn drain_pending_integer_fields(
        &mut self,
        restored_pending_integer_fields: &mut Vec<RestoredPendingIntegerField>,
    ) {
        while let Some(field_index) = self
            .pending_integer_fields
            .remove(&i64::from(self.next_array_index))
        {
            let old_field = std::mem::replace(
                &mut self.fields[field_index],
                BuilderField::MovedPendingInt,
            );
            let BuilderField::PendingInt { key, value } = old_field else {
                unreachable!("pending integer field index should always point at a pending field");
            };
            restored_pending_integer_fields.push(RestoredPendingIntegerField {
                field_index,
                key,
                value: value.clone(),
            });
            self.fields.push(BuilderField::Final(HirTableField::Array(value)));
            self.next_array_index += 1;
        }
    }
}

pub(super) fn try_extend_constructor_from_steps(
    builder: &mut ConstructorBuilder,
    steps: &[RegionStep],
    context: &mut RegionRebuildContext<'_>,
) -> bool {
    let checkpoint = builder.checkpoint(context.scratch);
    let region_contains_set_list = context.region_contains_set_list(steps);
    let mut segment_start = 0;

    for (index, step) in steps.iter().enumerate() {
        if let RegionStep::SetList { stmt_index } = step {
            if flush_constructor_segment(
                builder,
                &steps[segment_start..index],
                Some(*stmt_index),
                region_contains_set_list,
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

    if flush_constructor_segment(
        builder,
        &steps[segment_start..],
        None,
        region_contains_set_list,
        context,
    )
    .is_none()
    {
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
    allow_closure_records: bool,
    context: &mut RegionRebuildContext<'_>,
) -> Option<()> {
    let expected_set_list_start = builder.next_array_index();
    prepare_scratch(context.scratch, context.binding_index.len());

    if segment.is_empty() {
        builder.drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
        if let Some(stmt_index) = set_list_stmt_index {
            let set_list = set_list_stmt(context.block, stmt_index)?;
            if set_list.start_index != builder.next_array_index() {
                return None;
            }
            for value in &set_list.values {
                builder.push_array_value(value.clone());
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                builder.trailing_multivalue = Some(trailing.clone());
            }
        }
        return Some(());
    }

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
            RegionStep::ProducerGroup { stmt_index } => {
                register_producer_group(
                    context.block,
                    context.binding_index,
                    *stmt_index,
                    context.scratch,
                )?
            }
            RegionStep::Record { stmt_index } => prepare_record_step(
                *stmt_index,
                allow_closure_records,
                context,
            )?,
            RegionStep::SetList { .. } => unreachable!("set-list should terminate constructor segment"),
        }
    }

    if let Some(stmt_index) = set_list_stmt_index {
        let set_list = set_list_stmt(context.block, stmt_index)?;
        if set_list.start_index != expected_set_list_start {
            return None;
        }

        let mut queued_values = VecDeque::from_iter(set_list.values.iter());
        for token in &context.scratch.tokens {
            match token {
                SegmentToken::Producer { producer_index } => {
                    let producer = &context.scratch.pending_producers[*producer_index];
                    if context.scratch.consumed_bindings[producer.binding_id] {
                        continue;
                    }
                    match queued_values.front() {
                        Some(front) if matches_binding_ref(front, producer.binding) => {
                            if context.remaining_uses.contains(producer.binding_id) {
                                return None;
                            }
                            let value = pending_producer_value(context.block, producer)?;
                            context.scratch.consumed_bindings[producer.binding_id] = true;
                            queued_values.pop_front();
                            builder.push_array_value(value.clone());
                        }
                        Some(_)
                            if queued_values
                                .iter()
                                .any(|value| matches_binding_ref(value, producer.binding)) =>
                        {
                            return None;
                        }
                        _ => {}
                    }
                }
                SegmentToken::Record {
                    prepared_record_index,
                } => builder.push_record_field_with_policy(
                    context.scratch.prepared_records[*prepared_record_index].clone(),
                    RecordPromotionPolicy::PreserveSetListPrefix {
                        start_index: expected_set_list_start,
                    },
                ),
            }
        }

        for value in queued_values {
            let value = {
                let scratch = &mut context.scratch;
                let mut inline_context = InlineContext::new(
                    context.block,
                    context.binding_index,
                    &scratch.pending_producers,
                    &scratch.producer_index_by_binding,
                    &mut scratch.consumed_bindings,
                    &mut scratch.consumed_groups,
                    context.remaining_uses,
                );
                inline_constructor_value(&mut inline_context, value)?
            };
            builder.push_array_value(value);
        }

        if let Some(trailing) = &set_list.trailing_multivalue {
            let trailing = {
                let scratch = &mut context.scratch;
                let mut inline_context = InlineContext::new(
                    context.block,
                    context.binding_index,
                    &scratch.pending_producers,
                    &scratch.producer_index_by_binding,
                    &mut scratch.consumed_bindings,
                    &mut scratch.consumed_groups,
                    context.remaining_uses,
                );
                inline_constructor_value(&mut inline_context, trailing)?
            };
            builder.trailing_multivalue = Some(trailing);
        }
    }

    if set_list_stmt_index.is_none() {
        for token in &context.scratch.tokens {
            if let SegmentToken::Record {
                prepared_record_index,
            } = token
            {
                builder.push_record_field(
                    context.scratch.prepared_records[*prepared_record_index].clone(),
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

    if set_list_stmt_index.is_none() {
        builder
            .drain_pending_integer_fields(&mut context.scratch.restored_pending_integer_fields);
    }

    Some(())
}

fn prepare_scratch(scratch: &mut RebuildScratch, binding_count: usize) {
    scratch.pending_producers.clear();
    scratch.producer_groups.clear();
    scratch.tokens.clear();
    scratch.prepared_records.clear();
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
        scratch.producer_index_by_binding.resize(binding_count, None);
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
    scratch.tokens.push(SegmentToken::Producer { producer_index });
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
            PendingProducerSource::Value {
                stmt_index,
                value_index: 0,
            }
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
        scratch.tokens.push(SegmentToken::Producer { producer_index });
    }

    Some(())
}

fn prepare_record_step(
    stmt_index: usize,
    allow_closure_records: bool,
    context: &mut RegionRebuildContext<'_>,
) -> Option<()> {
    let (key, value) = record_field_parts(context.block, stmt_index)?;
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
            &mut scratch.consumed_bindings,
            &mut scratch.consumed_groups,
            context.remaining_uses,
        );
        inline_constructor_value(&mut inline_context, value)?
    };
    if matches!(value, HirExpr::Closure(_))
        && (recursive_closure_slot
            || (!allow_closure_records && matches!(key, HirTableKey::Name(_))))
    {
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
    context
        .scratch
        .prepared_records
        .push(crate::hir::common::HirRecordField { key, value });
    context
        .scratch
        .tokens
        .push(SegmentToken::Record { prepared_record_index });
    Some(())
}

fn record_field_parts(block: &HirBlock, stmt_index: usize) -> Option<(HirTableKey, &HirExpr)> {
    let HirStmt::Assign(assign) = block.stmts.get(stmt_index)? else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    Some((table_key_from_expr(&access.key), value))
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

fn producer_group_stmt(block: &HirBlock, stmt_index: usize) -> Option<(Vec<TableBinding>, &HirExpr)> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [source] = local_decl.values.as_slice() else {
                return None;
            };
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
            let [source] = assign.values.as_slice() else {
                return None;
            };
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

fn can_drop_open_pack_source_if_unused(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::VarArg)
}

fn pending_producer_value<'a>(block: &'a HirBlock, producer: &PendingProducer) -> Option<&'a HirExpr> {
    match producer.source {
        PendingProducerSource::Value {
            stmt_index,
            value_index,
        } => match block.stmts.get(stmt_index)? {
            HirStmt::LocalDecl(local_decl) => local_decl.values.get(value_index),
            HirStmt::Assign(assign) => assign.values.get(value_index),
            _ => None,
        },
        PendingProducerSource::Empty => None,
    }
}

fn binding_is_recursive_closure_slot(
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

fn expr_captures_orphaned_binding(
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
            }) || table.trailing_multivalue.as_ref().is_some_and(|value| {
                expr_captures_orphaned_binding(
                    value,
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

fn call_captures_orphaned_binding(
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

fn decision_target_captures_orphaned_binding(
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

fn table_key_captures_orphaned_binding(
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

fn can_stage_pending_integer_record(
    value: i64,
    current_next_index: i64,
    record_value: &HirExpr,
    policy: RecordPromotionPolicy,
) -> bool {
    if !can_reorder_integer_record_value(record_value) {
        return false;
    }

    match policy {
        RecordPromotionPolicy::Normal => value > current_next_index,
        RecordPromotionPolicy::PreserveSetListPrefix { start_index } => {
            value >= i64::from(start_index)
        }
    }
}
