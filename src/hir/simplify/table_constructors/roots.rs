//! 构造区域的终点与正向强持有证明。
//!
//! scanner/rebuild 提供已经验证的消费与事件序，本模块证明删除的 producer 根由独立
//! 字段持有到 frame 出口。例如三次调用写入三个不同键后立即 return，不能先合并
//! 三个结果身份再要求后层恢复。这里不从 may-alias 集合推导 must-hold 关系。

use super::*;

/// scanner 发布角色，rebuild 发布成功前缀；在同一遍步骤访问中汇总提交所需的根事实。
/// preserved 声明仍保留原根，不能计入删除集；强字段证明独立于通用的后续写入近似。
pub(super) struct RegionRootFacts {
    pub(super) temp_producers: Vec<TempId>,
    pub(super) has_exact_width_tail: bool,
    pub(super) has_removed_object_producer: bool,
    pub(super) has_followup_object_write: bool,
    scalar_calls_held: bool,
}

impl RegionRootFacts {
    pub(super) fn new(steps: &[RegionStep<'_>], preserved: &[usize]) -> Self {
        let mut facts = Self {
            temp_producers: Vec::new(),
            has_exact_width_tail: false,
            has_removed_object_producer: false,
            has_followup_object_write: false,
            scalar_calls_held: true,
        };
        let mut first_write_after_object = false;
        let mut pending = BTreeSet::new();
        let mut keys = Vec::new();
        for (index, step) in steps.iter().enumerate() {
            match step {
                RegionStep::Producer {
                    binding,
                    source,
                    scalar_call,
                    source_gc_inert,
                    ..
                } => {
                    if let TableBinding::Temp(temp) = binding {
                        facts.temp_producers.push(*temp);
                    }
                    let stmt_index = source.stmt_index();
                    if preserved.binary_search(&stmt_index).is_err() && !source_gc_inert {
                        facts.has_removed_object_producer = true;
                    }
                    facts.scalar_calls_held &= *scalar_call;
                    pending.insert(*binding);
                }
                RegionStep::Record { key, value, .. } => {
                    facts.scalar_calls_held &=
                        matches!(key, HirExpr::Integer(_) | HirExpr::String(_))
                            && !keys.contains(key);
                    keys.push(*key);
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
                    facts.scalar_calls_held &= index + 1 == steps.len()
                        && !keys.iter().any(|key| matches!(key, HirExpr::Integer(key) if *key >= i64::from(batch.start_index)));
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
        facts.scalar_calls_held &= pending.is_empty();
        facts
    }
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
            || !roots.scalar_calls_held
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
                .debug_identity_bindings
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
