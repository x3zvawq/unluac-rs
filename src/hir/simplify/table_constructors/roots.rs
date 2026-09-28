//! 证明构造区域中 producer 根的终点与确定持有关系。
//!
//! 消费已验证的字段和事件顺序，发布允许删除独立物化的根证明。

use super::*;

/// scanner 发布角色，rebuild 发布成功前缀；在同一遍步骤访问中汇总提交所需的根事实。
/// preserved 声明仍保留原根，不能计入删除集；强字段证明独立于通用的后续写入近似。
pub(super) struct RegionRootFacts {
    pub(super) temp_producers: Vec<TempId>,
    pub(super) has_exact_width_tail: bool,
    pub(super) has_removed_object_producer: bool,
    pub(super) has_followup_object_write: bool,
    pub(super) removed_roots_are_inert_tables: bool,
    scalar_results_held: bool,
}

impl RegionRootFacts {
    pub(super) fn new(steps: &[RegionStep<'_>], preserved: &[usize]) -> Self {
        let mut facts = Self {
            temp_producers: Vec::new(),
            has_exact_width_tail: false,
            has_removed_object_producer: false,
            has_followup_object_write: false,
            removed_roots_are_inert_tables: true,
            scalar_results_held: true,
        };
        let mut first_write_after_object = false;
        let mut pending = BTreeSet::new();
        let mut integer_keys = BTreeSet::new();
        let mut string_keys = BTreeSet::new();
        for (index, step) in steps.iter().enumerate() {
            match step {
                RegionStep::Producer {
                    binding,
                    source,
                    scalar_result,
                    source_gc_inert,
                    value,
                    ..
                } => {
                    if let TableBinding::Temp(temp) = binding {
                        facts.temp_producers.push(*temp);
                    }
                    let stmt_index = source.stmt_index();
                    if preserved.binary_search(&stmt_index).is_err() && !source_gc_inert {
                        facts.has_removed_object_producer = true;
                        facts.removed_roots_are_inert_tables &= inert_table_contents(value);
                    }
                    facts.scalar_results_held &= *scalar_result;
                    pending.insert(*binding);
                }
                RegionStep::Record { key, value, .. } => {
                    facts.scalar_results_held &= match key {
                        HirExpr::Integer(key) => integer_keys.insert(*key),
                        HirExpr::String(key) => string_keys.insert(key),
                        _ => false,
                    };
                    if let Some(binding) = binding_from_expr(value) {
                        pending.remove(&binding);
                    }
                }
                RegionStep::SetList { batch, .. } => {
                    facts.has_exact_width_tail |= batch
                        .values
                        .tail
                        .as_ref()
                        .is_some_and(|tail| tail.exact_width().is_some());
                    facts.scalar_results_held &= index + 1 == steps.len()
                        && integer_keys
                            .range(i64::from(batch.start_index)..)
                            .next()
                            .is_none();
                    for value in &batch.values.fixed {
                        if let Some(binding) = binding_from_expr(value) {
                            pending.remove(&binding);
                        }
                    }
                }
            }
            if !matches!(step, RegionStep::Producer { .. }) && facts.has_removed_object_producer {
                facts.has_followup_object_write |= first_write_after_object;
                first_write_after_object = true;
            }
        }
        facts.scalar_results_held &= pending.is_empty();
        facts
    }
}

/// 新建表尚未暴露时，只有其内容也不持有外部可观察资源，才能丢弃独立临时根。
/// 表身份仍由原构造器分配一次；此查询不授权移动分配或删除字段求值。
fn inert_table_contents(value: &HirExpr) -> bool {
    let HirExpr::TableConstructor(table) = value else {
        return false;
    };
    table.trailing_multivalue.is_none()
        && table.fields.iter().all(|field| match field {
            HirTableField::Array(value) => {
                producer_value_can_be_dropped(value) || inert_table_contents(value)
            }
            HirTableField::Record(record) => {
                producer_value_can_be_dropped(&record.key)
                    && (producer_value_can_be_dropped(&record.value)
                        || inert_table_contents(&record.value))
            }
        })
}

impl TableConstructorPass<'_> {
    pub(super) fn returned_indexed_region_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        start: usize,
        binding: TableBinding,
        region: &scan::ConstructorRegion<'_>,
        roots: &RegionRootFacts,
    ) -> bool {
        let scan::ConstructorRegion {
            constructor,
            end_index: end,
            preserved_stmt_indices: preserved,
            ..
        } = region;
        let end = *end;
        let [HirStmt::Return(ret)] = &block.stmts[end + 1..] else {
            return false;
        };
        let Some((_, seed)) = constructor_seed(&block.stmts[start]) else {
            return false;
        };
        if self.has_cleanup
            || !roots.scalar_results_held
            || !preserved.is_empty()
            || ret.values.tail.is_some()
            || ret.values.fixed.len() != 1
            || binding_from_expr(&ret.values.fixed[0]) != Some(binding)
            || seed.allocation != constructor.allocation
            || !constructor.matches_indexed_array_capacity(
                constructor
                    .fields
                    .iter()
                    .filter(|field| matches!(field, HirTableField::Array(_)))
                    .count(),
            )
            || constructor_uses_binding(constructor, binding)
            || self
                .preserved_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || !self.open_constructor_capture_region_is_safe(block, start, end, binding)
            || seed.fields.iter().any(|field| match field {
                HirTableField::Array(value) => !producer_value_can_be_dropped(value),
                HirTableField::Record(record) => !producer_value_can_be_dropped(&record.value),
            })
        {
            return false;
        }
        match binding {
            TableBinding::Temp(_) if !self.seed_overwrites_unobservable_entry_nil(binding) => {
                return false;
            }
            TableBinding::Local(_) if !matches!(block.stmts[start], HirStmt::LocalDecl(_)) => {
                return false;
            }
            _ => {}
        }
        true
    }
}
