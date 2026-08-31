//! 这个文件负责把“稳定的建表片段”收回 `TableConstructor`。
//!
//! `NewTable + SetTable + SetList` 在 low-IR 里天然是分散的；如果 HIR 一直把它们保留成
//! 零散语句，后面 AST 虽然还能继续工作，但整层会长期带着明显的机械噪音。这里专门吃一类
//! 很稳的构造区域：
//! 1. 先出现一个空表构造器 seed；
//! 2. 后面紧跟一段 keyed write、简单值生产和 `table-set-list`；
//! 3. 这段时间里表值没有逃逸，也没有跨语句依赖还没落地的中间绑定。
//!
//! 非递归闭包字段可以作为 record 值进入构造器；如果闭包捕获的 binding 会因为本次重建
//! 被移除成孤儿，后面的 orphan-capture 检查会保留原形，避免破坏 upvalue 身份。
//!
//! 这样做的目的不是“尽可能多地猜源码”，而是把已经能够证明安全的构造片段收回更自然的
//! HIR 形状，为后续 AST 降低继续减负。
//! 全量 binding facts 只服务这些候选；没有 seed/SETLIST 根形状的 proto 先通过
//! statement/block 骨架门跳过，不递归扫描无关表达式。

mod bindings;
mod builder;
mod inline_value;
mod rebuild;
mod scan;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::ast::DecompileDialect;
use crate::hir::common::{
    HirAssign, HirExpr, HirLValue, HirProto, HirStmt, HirTableAccess, HirTableConstructor,
    HirTableField, HirTableKey, HirValuePack, LocalId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use self::bindings::{
    BindingFacts, BindingIndex, BindingOccurrenceIndex, BindingSlots, StmtBindingSummary,
    binding_from_expr, binding_from_lvalue, collect_binding_facts, collect_stmt_binding_summary,
    expr_uses_binding, table_key_from_expr,
};
use self::builder::expr_is_definitely_non_nil;
use self::rebuild::producer_value_can_be_dropped;
use self::scan::{
    ConstructorWriteIndex, constructor_seed, constructor_uses_binding, install_constructor_seed,
    seed_overwrite_delay_is_unobservable, try_rebuild_constructor_region,
};
use super::mention::{
    ReferenceCapturedBindings, stmts_reference_captured_bindings, stmts_value_captured_bindings,
};
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::simplify::visit::{HirVisitor, visit_stmts};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum TableBinding {
    Temp(TempId),
    Local(LocalId),
}

type BindingId = usize;

// Cross-statement fixed SETLIST folding is a readability optimization.  Its proof scans the
// producer interval and is deliberately disabled for very large blocks so a generated chunk
// with many SETLIST batches cannot turn the pass into a quadratic walk.  The immediate canonical
// NewTable path below remains available and is linear in the block size.
const MAX_GENERIC_SET_LIST_SCAN_STMTS: usize = 4096;

#[derive(Debug, Clone, Copy)]
enum RegionStep {
    Producer {
        stmt_index: usize,
        slot_index: usize,
    },
    ProducerGroup {
        stmt_index: usize,
    },
    Record {
        stmt_index: usize,
    },
    SetList {
        stmt_index: usize,
    },
}

#[derive(Debug, Clone)]
struct PendingProducer {
    binding: TableBinding,
    binding_id: BindingId,
    source: PendingProducerSource,
    group: Option<usize>,
}

#[derive(Debug, Clone)]
enum PendingProducerSource {
    Value {
        stmt_index: usize,
        value_index: usize,
    },
    Tail {
        stmt_index: usize,
    },
    Empty,
}

#[derive(Debug, Clone, Copy)]
struct ProducerGroupMeta {
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone, Copy)]
enum SegmentToken {
    Producer { producer_index: usize },
    Record { prepared_record_index: usize },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ConstructorEvalEvent {
    Producer(usize),
    Barrier,
}

#[derive(Debug, Clone)]
struct PreparedRecord {
    field: crate::hir::common::HirRecordField,
    eval_events: Range<usize>,
}

#[derive(Debug, Clone)]
struct RestoredPendingIntegerField {
    field_index: usize,
    key: i64,
    value: HirExpr,
}

#[derive(Debug, Clone)]
struct RestoredArrayField {
    field_index: usize,
    value: HirExpr,
}

#[derive(Debug, Clone, Default)]
struct RebuildScratch {
    pending_producers: Vec<PendingProducer>,
    producer_groups: Vec<ProducerGroupMeta>,
    tokens: Vec<SegmentToken>,
    prepared_records: Vec<PreparedRecord>,
    prepared_eval_events: Vec<ConstructorEvalEvent>,
    source_eval_events: Vec<ConstructorEvalEvent>,
    generated_eval_events: Vec<ConstructorEvalEvent>,
    producer_index_by_binding: Vec<Option<usize>>,
    consumed_bindings: Vec<bool>,
    consumed_groups: Vec<bool>,
    removed_materializations: Vec<u32>,
    touched_binding_ids: Vec<BindingId>,
    restored_pending_integer_fields: Vec<RestoredPendingIntegerField>,
    restored_array_fields: Vec<RestoredArrayField>,
}

pub(super) fn stabilize_table_constructors_in_proto(
    proto: &mut HirProto,
    dialect: DecompileDialect,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    if !block_has_table_constructor_candidate(&proto.body) {
        return false;
    }

    let temp_count = proto.temps.len();
    let first_new_local = proto.locals.len();
    let BindingFacts {
        materialized: materialized_bindings,
        reference_captured: reference_captured_bindings,
        reference_captured_home_slots,
    } = collect_binding_facts(&proto.body, promotion_facts, temp_count, first_new_local);
    let mut pass = TableConstructorPass {
        materialized_bindings,
        reference_captured_bindings,
        reference_captured_home_slots,
        debug_identity_bindings: BindingSlots::from_debug_hints(
            &proto.temp_debug_locals,
            &proto.local_debug_hints,
        ),
        promotion_facts,
        dialect,
        temp_count,
        next_local_index: first_new_local,
    };
    let changed = rewrite_proto(proto, &mut pass);
    proto
        .local_debug_hints
        .extend((first_new_local..pass.next_local_index).map(|_| None));
    proto
        .locals
        .extend((first_new_local..pass.next_local_index).map(LocalId));
    changed
}

struct TableConstructorPass<'a> {
    materialized_bindings: BindingSlots<u32>,
    reference_captured_bindings: BindingSlots<bool>,
    reference_captured_home_slots: std::collections::BTreeSet<HomeSlotKey>,
    debug_identity_bindings: BindingSlots<bool>,
    promotion_facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
    temp_count: usize,
    next_local_index: usize,
}

impl HirRewritePass for TableConstructorPass<'_> {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        if !block.stmts.iter().any(is_direct_constructor_candidate) {
            return false;
        }

        let mut changed = false;
        let mut scratch = RebuildScratch::default();
        // 稳定 stmt id 让 occurrence index 在删除已折叠 region 后仍能按源码顺序查询；
        // 每个 seed 只做当前位置之后的有序集合查找，不重建完整 suffix summary。
        let mut binding_index = BindingIndex::new(self.temp_count, self.next_local_index);
        let mut stmt_bindings: Vec<StmtBindingSummary> = block
            .stmts
            .iter()
            .map(|stmt| collect_stmt_binding_summary(stmt, &mut binding_index))
            .collect();
        let mut binding_occurrences = BindingOccurrenceIndex::new(
            &binding_index,
            &stmt_bindings,
            &self.reference_captured_bindings,
            &self.reference_captured_home_slots,
            &self.debug_identity_bindings,
            self.promotion_facts,
        );
        let mut stmt_ids = (0..block.stmts.len()).collect::<Vec<_>>();
        let constructor_writes = ConstructorWriteIndex::new(&block.stmts, &binding_index);
        let materialized_binding_counts =
            binding_index.materialized_counts(&self.materialized_bindings);
        let mut index = 0;
        while index < block.stmts.len() {
            let Some((binding, seed_ctor)) = constructor_seed(&block.stmts[index]) else {
                index += 1;
                continue;
            };
            let seed_ctor = seed_ctor.clone();

            let binding_id = binding_index
                .id_of(binding)
                .expect("constructor seed binding should be indexed");
            let seed_stmt_id = stmt_ids[index];
            let rebuilt = if constructor_writes.has_write_after(binding_id, seed_stmt_id) {
                let candidate = try_rebuild_constructor_region(
                    block,
                    index,
                    binding,
                    seed_ctor.clone(),
                    &binding_index,
                    &binding_occurrences,
                    &materialized_binding_counts,
                    &stmt_ids,
                    self.dialect,
                    &mut scratch,
                );
                candidate.filter(|(rebuilt_constructor, end_index)| {
                    let open_local_owner = rebuilt_constructor.trailing_multivalue.is_some()
                        && self.open_local_constructor_region_is_safe(
                            block,
                            index,
                            *end_index,
                            binding,
                            rebuilt_constructor,
                        );
                    let invalid_array_shape = constructor_has_nil_field(&seed_ctor)
                        || constructor_has_uncertain_array_field(&seed_ctor)
                        || constructor_has_uncertain_array_field(rebuilt_constructor)
                        || (rebuilt_constructor.trailing_multivalue.is_some()
                            && array_fields_contain_uncertain_value(&rebuilt_constructor.fields))
                        || region_has_direct_nil_field(block, index, *end_index)
                        || region_has_exact_width_tail(block, index, *end_index);
                    // Check the completed constructor as well as the original seed.  A seed
                    // whose last array value may be nil is safe only while it remains the last
                    // slot; appending a later definite value must stay as an indexed write.
                    // The standalone constructor `{ maybe_nil, 1 }` is unaffected because it
                    // never enters this cross-statement region in the first place.
                    // A non-scalar producer can be the only strong root for an object after
                    // its value is stored in the table.  If the table is mentioned after the
                    // folded region, a later clear/escape/call may observe that root; keep the
                    // producer declaration in that case.  When the table dies at the region
                    // boundary, dropping the temporary does not change its observable life.
                    let producer_root_is_observable =
                        region_has_non_drop_safe_producer(block, index, *end_index)
                            && !open_local_owner
                            && collect_range_binding_mentions(
                                block,
                                *end_index + 1,
                                block.stmts.len(),
                            )
                            .contains(&binding);
                    let has_followup_object_write =
                        region_has_followup_table_write_after_object_producer(
                            block, index, *end_index, binding,
                        );
                    // The constructor RHS is evaluated before an ordinary assignment stores
                    // its result.  Keep the explicit seed whenever the region does not prove
                    // that the original seed overwrite already precedes every observable RHS;
                    // direct NewTable provenance alone is not such proof.
                    let overwrite_timing_is_safe = open_local_owner
                        || seed_overwrite_delay_is_unobservable(block, index, *end_index, binding);
                    !invalid_array_shape
                        && !producer_root_is_observable
                        && (open_local_owner || !has_followup_object_write)
                        && overwrite_timing_is_safe
                })
            } else {
                None
            };
            let (constructor, end_index, rebuilt_region) = match rebuilt {
                Some((rebuilt_ctor, end_index)) => (rebuilt_ctor, end_index, true),
                None => (seed_ctor, index, false),
            };

            if !rebuilt_region {
                index += 1;
                continue;
            }

            install_constructor_seed(&mut block.stmts[index], constructor);
            let drain_end = end_index;
            if drain_end > index {
                for i in index + 1..=drain_end {
                    binding_occurrences.remove_stmt(stmt_ids[i], &stmt_bindings[i]);
                }
                block.stmts.drain(index + 1..=drain_end);
                stmt_bindings.drain(index + 1..=drain_end);
                stmt_ids.drain(index + 1..=drain_end);
            }
            changed = true;
            index += 1;
        }

        changed |= self.materialize_safe_fixed_set_lists(block);
        changed
    }
}

fn region_has_non_drop_safe_producer(
    block: &crate::hir::common::HirBlock,
    start_index: usize,
    end_index: usize,
) -> bool {
    block.stmts[start_index + 1..=end_index]
        .iter()
        .any(stmt_has_non_drop_safe_producer)
}

fn region_has_followup_table_write_after_object_producer(
    block: &crate::hir::common::HirBlock,
    start_index: usize,
    end_index: usize,
    binding: TableBinding,
) -> bool {
    if end_index <= start_index {
        return false;
    }
    let mut object_producer_seen = false;
    let mut first_table_write_after_producer = false;
    for stmt in &block.stmts[start_index + 1..=end_index] {
        if stmt_has_non_drop_safe_producer(stmt) {
            object_producer_seen = true;
        }
        if stmt_writes_table_binding(stmt, binding) && object_producer_seen {
            if first_table_write_after_producer {
                return true;
            }
            first_table_write_after_producer = true;
        }
    }
    false
}

fn stmt_has_non_drop_safe_producer(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(decl) => decl
            .values
            .fixed
            .iter()
            .any(|value| !producer_value_can_be_dropped(value)),
        // Keyed writes are constructor fields, not independent producer materializations.
        // Their object values remain rooted by the rebuilt table itself and must not make the
        // enclosing region look as if a removable local producer were still alive.
        _ => false,
    }
}

fn stmt_writes_table_binding(stmt: &HirStmt, binding: TableBinding) -> bool {
    match stmt {
        HirStmt::Assign(assign) => assign.targets.iter().any(|target| {
            matches!(
                target,
                HirLValue::TableAccess(access)
                    if binding_from_expr(&access.base) == Some(binding)
            )
        }),
        HirStmt::TableSetList(set_list) => binding_from_expr(&set_list.base) == Some(binding),
        _ => false,
    }
}

impl TableConstructorPass<'_> {
    /// Lower a fixed SETLIST to indexed writes only when an explicit fresh seed dominates it.
    /// Keeping the seed statement intact preserves its allocation point and avoids changing
    /// raw SETLIST writes on shared or metatable-bearing tables into ordinary assignments.
    fn materialize_safe_fixed_set_lists(
        &mut self,
        block: &mut crate::hir::common::HirBlock,
    ) -> bool {
        let mut changed = false;
        let mut index = 0;
        while index < block.stmts.len() {
            let Some(set_list) = (match &block.stmts[index] {
                HirStmt::TableSetList(set_list) => Some(set_list.clone()),
                _ => None,
            }) else {
                index += 1;
                continue;
            };
            let Some(binding) = binding_from_expr(&set_list.base) else {
                index += 1;
                continue;
            };

            // 相邻的源码 LocalDecl 与 fixed SETLIST 是 VM 对同一个构造器初始化的拆分编码。
            // direct-seed provenance 证明 allocation 仍在原声明位置，SETLIST start 又证明数组
            // 段连续，因此合并不会跨 producer，也不会改变字段求值、nil 槽或 fixed-call 宽度。
            // debug local 仍由同一 LocalDecl 持有，而且 Lua initializer 求值时该 binding 尚不可见；
            // 把 batch 放回 initializer 正好恢复这条词法边界。open tail 仍走更窄的独立证明。
            if let Some(seed_index) =
                self.find_adjacent_local_constructor_seed(block, index, binding, &set_list)
            {
                let Some((_, seed)) = constructor_seed(&block.stmts[seed_index]) else {
                    unreachable!("adjacent LocalDecl SETLIST seed must be a constructor");
                };
                let constructor = constructor_with_set_list(seed, &set_list);
                install_constructor_seed(&mut block.stmts[seed_index], constructor);
                block.stmts.remove(index);
                changed = true;
                continue;
            }

            // A fixed SETLIST immediately following the canonical NewTable definition is the
            // compiler's own constructor encoding, rather than a write into an existing table.
            // Rebuilding this narrow shape preserves the original allocation/evaluation point,
            // but only for data-only, definitely non-nil fixed values and a hole-free seed. Open
            // tails and uncertain/nil array shapes use the separate seed-anchored proof below.
            if let Some(seed_index) =
                self.find_direct_set_list_seed(block, index, binding, &set_list)
            {
                let Some((_, seed)) = constructor_seed(&block.stmts[seed_index]) else {
                    unreachable!("direct SETLIST seed must be a constructor");
                };
                let constructor = constructor_with_set_list(seed, &set_list);
                install_constructor_seed(&mut block.stmts[seed_index], constructor);
                block.stmts.remove(index);
                changed = true;
                continue;
            }

            // A canonical fresh seed with a fixed, data-only SETLIST can also be lowered to
            // ordinary indexed writes without moving the seed allocation.  This is deliberately
            // separate from constructor folding: unknown/nil values retain their original write
            // semantics, while the fresh seed proof rules out metatable dispatch.
            if let Some(seed_index) =
                self.find_direct_set_list_seed_for_indexed_writes(block, index, binding, &set_list)
            {
                let base = set_list.base.clone();
                let assignments = set_list
                    .values
                    .fixed
                    .iter()
                    .enumerate()
                    .map(|(offset, value)| {
                        let key = set_list
                            .start_index
                            .checked_add(u32::try_from(offset).expect("SETLIST offset fits u32"))
                            .expect("SETLIST index overflow");
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                                base: base.clone(),
                                key: HirExpr::Integer(i64::from(key)),
                            }))],
                            values: HirValuePack::fixed(vec![value.clone()]),
                        }))
                    })
                    .collect::<Vec<_>>();
                block.stmts.splice(index..=index, assignments);
                changed = true;
                // The replacement statements are already in final form; skip over them so the
                // loop does not immediately reconsider the same seed as a new region.
                index = seed_index + 1;
                continue;
            }

            // Source LocalDecl seeds can have harmless scalar/keyed setup statements between
            // the declaration and SETLIST. Preserve those statements and replace only the raw
            // fixed batch, so neither the table allocation nor a producer overwrite moves.
            if let Some(_seed_index) =
                self.find_local_set_list_seed_for_indexed_writes(block, index, binding, &set_list)
            {
                let base = set_list.base.clone();
                let fixed_len = set_list.values.fixed.len();
                let assignments = set_list
                    .values
                    .fixed
                    .iter()
                    .enumerate()
                    .map(|(offset, value)| {
                        let key = set_list
                            .start_index
                            .checked_add(u32::try_from(offset).expect("SETLIST offset fits u32"))
                            .expect("SETLIST index overflow");
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                                base: base.clone(),
                                key: HirExpr::Integer(i64::from(key)),
                            }))],
                            values: HirValuePack::fixed(vec![value.clone()]),
                        }))
                    })
                    .collect::<Vec<_>>();
                block.stmts.splice(index..=index, assignments);
                changed = true;
                index += fixed_len;
                continue;
            }

            if block.stmts.len() > MAX_GENERIC_SET_LIST_SCAN_STMTS {
                index += 1;
                continue;
            }

            // An open pack is only folded for the narrow, seed-anchored LocalDecl shape
            // proved above.  Do this before the fixed-list scanner: that scanner deliberately
            // rejects open tails and must not make this independent proof unreachable.
            if set_list.values.tail.is_some() {
                let seed_index = index.checked_sub(1);
                if seed_index.is_some_and(|seed_index| {
                    self.open_set_list_seed_is_safe(block, seed_index, binding, &set_list)
                }) {
                    let seed_index = seed_index.expect("checked adjacent SETLIST seed");
                    let Some((_, seed)) = constructor_seed(&block.stmts[seed_index]) else {
                        unreachable!("open SETLIST seed must be a constructor");
                    };
                    let constructor = constructor_with_set_list(seed, &set_list);
                    install_constructor_seed(&mut block.stmts[seed_index], constructor);
                    block.stmts.remove(index);
                    changed = true;
                    continue;
                }
                index += 1;
                continue;
            }

            let Some(seed_index) = self.find_fixed_set_list_seed(block, index, binding) else {
                index += 1;
                continue;
            };

            if let Some((constructor, removed)) =
                self.fold_fixed_set_list_into_seed(block, index, seed_index, binding, &set_list)
            {
                install_constructor_seed(&mut block.stmts[seed_index], constructor);
                for remove_index in removed.into_iter().rev() {
                    block.stmts.remove(remove_index);
                }
                changed = true;
                index = seed_index + 1;
                continue;
            }

            // A raw SETLIST is not generally equivalent to ordinary indexed assignment:
            // the former bypasses `__newindex` and has distinct nil-hole/array-part rules.
            // If the seed proof above did not let us rebuild it as a constructor, leave the
            // semantic node for a dialect-aware lowering instead of silently changing it.
            index += 1;
        }
        changed
    }

    fn find_adjacent_local_constructor_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<usize> {
        let seed_index = set_list_index.checked_sub(1)?;
        let TableBinding::Local(local) = binding else {
            return None;
        };
        let (seed_binding, seed) = constructor_seed(block.stmts.get(seed_index)?)?;
        let HirStmt::LocalDecl(local_decl) = block.stmts.get(seed_index)? else {
            return None;
        };
        let has_open_tail = set_list.values.tail.is_some();
        if seed_binding != binding
            || local_decl.bindings.as_slice() != [local]
            || seed.trailing_multivalue.is_some()
            || constructor_has_numeric_record(seed)
            || constructor_uses_binding(seed, binding)
            || self.binding_is_shared_before_seed(block, seed_index, binding)
            || self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || (has_open_tail
                && self
                    .debug_identity_bindings
                    .get(binding)
                    .copied()
                    .unwrap_or_default())
            || self.materialized_bindings.get(binding).copied() != Some(1)
            || self.promotion_facts.compacts_home_slots()
            || self
                .promotion_facts
                .trusted_local_home_slot(local)
                .is_none()
            || !self.promotion_facts.is_direct_table_seed_local(local)
            || (has_open_tail && !self.adjacent_set_list_array_shape_is_safe(seed, set_list))
            || (set_list.values.fixed.is_empty() && set_list.values.tail.is_none())
            || set_list.values.tail.as_ref().is_some_and(|tail| {
                tail.exact_width().is_some()
                    || !expr_is_open_tail_safe(tail.as_expr())
                    || expr_uses_binding(tail.as_expr(), binding)
                    || !set_list.values.fixed.iter().all(expr_is_definitely_non_nil)
            })
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_open_tail_safe(value) || expr_uses_binding(value, binding))
        {
            return None;
        }

        let array_len = seed
            .fields
            .iter()
            .filter(|field| matches!(field, HirTableField::Array(_)))
            .count();
        (set_list.start_index == u32::try_from(array_len).ok()?.checked_add(1)?)
            .then_some(seed_index)
    }

    fn adjacent_set_list_array_shape_is_safe(
        &self,
        seed: &HirTableConstructor,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> bool {
        let mut fields = seed.fields.clone();
        fields.extend(
            set_list
                .values
                .fixed
                .iter()
                .cloned()
                .map(HirTableField::Array),
        );
        array_fields_have_safe_nil_shape(&fields)
    }

    fn find_direct_set_list_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<usize> {
        let seed_index = set_list_index.checked_sub(1)?;
        let (seed_binding, seed) = constructor_seed(&block.stmts[seed_index])?;
        if seed_binding != binding
            || constructor_has_numeric_record(seed)
            || set_list.start_index
                != u32::try_from(
                    seed.fields
                        .iter()
                        .filter(|field| matches!(field, HirTableField::Array(_)))
                        .count(),
                )
                .ok()?
                .checked_add(1)?
            || seed.trailing_multivalue.is_some()
            || !constructor_is_data_only(seed)
            || !array_fields_have_safe_nil_shape(&seed.fields)
            || constructor_uses_binding(seed, binding)
            || (set_list.values.fixed.is_empty() && set_list.values.tail.is_none())
            || set_list.values.tail.is_some()
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_definitely_non_nil(value) || !expr_is_data_only(value))
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| expr_uses_binding(value, binding))
            || set_list
                .values
                .tail
                .as_ref()
                .is_some_and(|tail| tail.exact_width().is_some())
            || self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
        {
            return None;
        }

        // Direct origin is a single SSA def (or the corresponding source LocalDecl), and the
        // materialization count above excludes an earlier write.  Do not rescan the whole prefix
        // here; large compiler-generated tables can contain thousands of SETLIST batches.
        match binding {
            TableBinding::Temp(temp) => (self.promotion_facts.is_direct_table_seed_temp(temp)
                && !self.promotion_facts.compacts_home_slots()
                && self.promotion_facts.trusted_temp_home_slot(temp).is_some()
                && self.materialized_bindings.get(binding).copied() == Some(1))
            .then_some(seed_index),
            TableBinding::Local(local) => {
                (matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
                    && self.promotion_facts.is_direct_table_seed_local(local)
                    && !self.promotion_facts.compacts_home_slots()
                    && self
                        .promotion_facts
                        .trusted_local_home_slot(local)
                        .is_some()
                    && self.materialized_bindings.get(binding).copied() == Some(1))
                .then_some(seed_index)
            }
        }
    }

    fn find_direct_set_list_seed_for_indexed_writes(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<usize> {
        let seed_index = set_list_index.checked_sub(1)?;
        let (seed_binding, seed) = constructor_seed(&block.stmts[seed_index])?;
        if seed_binding != binding
            || !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
            || seed.trailing_multivalue.is_some()
            || set_list.values.tail.is_some()
            || set_list.values.fixed.is_empty()
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_indexed_set_list_value_safe(value))
            || self
                .debug_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || self.materialized_bindings.get(binding).copied() != Some(1)
            || self.promotion_facts.compacts_home_slots()
            || self
                .promotion_facts
                .trusted_local_home_slot(match binding {
                    TableBinding::Local(local) => local,
                    TableBinding::Temp(_) => return None,
                })
                .is_none()
            || !self
                .promotion_facts
                .is_direct_table_seed_local(match binding {
                    TableBinding::Local(local) => local,
                    TableBinding::Temp(_) => return None,
                })
            || set_list.start_index
                != u32::try_from(
                    seed.fields
                        .iter()
                        .filter(|field| matches!(field, HirTableField::Array(_)))
                        .count(),
                )
                .ok()?
                .checked_add(1)?
            || !array_fields_have_safe_nil_shape(&seed.fields)
            || constructor_uses_binding(seed, binding)
        {
            return None;
        }
        Some(seed_index)
    }

    fn find_local_set_list_seed_for_indexed_writes(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<usize> {
        let TableBinding::Local(_local) = binding else {
            return None;
        };
        if set_list.values.tail.is_some()
            || set_list.values.fixed.is_empty()
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_indexed_set_list_value_safe(value))
        {
            return None;
        }

        for seed_index in (0..set_list_index).rev() {
            let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
                continue;
            };
            if seed_binding != binding {
                continue;
            }

            let seed_array_len = seed
                .fields
                .iter()
                .filter(|field| matches!(field, HirTableField::Array(_)))
                .count();
            let set_list_can_overwrite_seed = usize::try_from(set_list.start_index)
                .ok()
                .is_some_and(|start| start >= 1 && start <= seed_array_len.saturating_add(1));
            let safe_seed = matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
                && seed.trailing_multivalue.is_none()
                && !constructor_uses_binding(seed, binding)
                && array_fields_have_safe_nil_shape(&seed.fields)
                && set_list_can_overwrite_seed;
            if !safe_seed {
                return None;
            }
            return self
                .fixed_set_list_prefix_is_safe(block, seed_index, set_list_index, binding)
                .then_some(seed_index);
        }
        None
    }

    /// Prove that the interval before a fixed SETLIST only touches fresh tables created inside
    /// that interval.  This keeps the indexed-write fallback from turning an assignment to an
    /// already escaped/metatable-bearing table into a raw SETLIST-equivalent operation.
    fn fixed_set_list_prefix_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        set_list_index: usize,
        binding: TableBinding,
    ) -> bool {
        let TableBinding::Local(seed_local) = binding else {
            return false;
        };
        let Some(seed_home) = self.promotion_facts.trusted_local_home_slot(seed_local) else {
            return false;
        };
        let debug_seed = self
            .debug_identity_bindings
            .get(binding)
            .copied()
            .unwrap_or_default();
        let prefix = &block.stmts[seed_index..set_list_index];
        if self.captures_may_share_seed_home(
            &stmts_reference_captured_bindings(prefix),
            seed_local,
            seed_home,
        ) || self.captures_may_share_seed_home(
            &stmts_value_captured_bindings(prefix),
            seed_local,
            seed_home,
        ) {
            return false;
        }
        // The LocalDecl at `seed_index` is the fresh owner whose allocation remains in place.
        // Prefix writes may target it directly; without seeding this set, the final membership
        // check could never accept the very owner the proof started from.
        let mut fresh_tables = BTreeSet::from([binding]);
        for (offset, stmt) in block.stmts[seed_index..set_list_index].iter().enumerate() {
            let stmt_index = seed_index + offset;
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    if debug_seed && !debug_prefix_stmt_is_inert(stmt) {
                        return false;
                    }
                    if decl.bindings.contains(&seed_local) && stmt_index != seed_index {
                        // A second declaration of the seed binding would create a new lexical
                        // owner, so the indexed-write proof must stop at that boundary.
                        return false;
                    }
                    if decl
                        .values
                        .iter()
                        .any(|value| expr_uses_binding(value, binding))
                    {
                        return false;
                    }
                    for local in &decl.bindings {
                        if *local == seed_local {
                            continue;
                        }
                        let Some(candidate_home) =
                            self.promotion_facts.trusted_local_home_slot(*local)
                        else {
                            return false;
                        };
                        if candidate_home == seed_home {
                            return false;
                        }
                    }
                    if let Some((candidate, constructor)) = constructor_seed(stmt) {
                        if !matches!(candidate, TableBinding::Local(_))
                            || !constructor_is_data_only(constructor)
                            || constructor_uses_binding(constructor, candidate)
                            || constructor_uses_binding(constructor, binding)
                        {
                            return false;
                        }
                        fresh_tables.insert(candidate);
                    }
                }
                HirStmt::ToBeClosed(_)
                | HirStmt::Close(_)
                | HirStmt::Goto(_)
                | HirStmt::Label(_) => {
                    return false;
                }
                HirStmt::Assign(assign) => {
                    if debug_seed && !debug_prefix_stmt_is_inert(stmt) {
                        return false;
                    }
                    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                        return false;
                    };
                    let [value] = assign.values.fixed.as_slice() else {
                        return false;
                    };
                    if assign.values.tail.is_some()
                        || expr_uses_binding(&access.key, binding)
                        || expr_uses_binding(value, binding)
                        || !expr_is_prefix_read_only(&access.key)
                        || !expr_is_prefix_read_only(value)
                    {
                        return false;
                    }
                    let Some(base) = binding_from_expr(&access.base) else {
                        return false;
                    };
                    if base != binding && !fresh_tables.contains(&base) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        fresh_tables.contains(&binding)
    }

    fn captures_may_share_seed_home(
        &self,
        captured: &ReferenceCapturedBindings,
        seed_local: LocalId,
        seed_home: HomeSlotKey,
    ) -> bool {
        captured.locals.iter().any(|local| {
            *local == seed_local
                || self
                    .promotion_facts
                    .trusted_local_home_slot(*local)
                    .is_none_or(|home| home == seed_home)
        }) || captured.temps.iter().any(|temp| {
            self.promotion_facts
                .trusted_temp_home_slot(*temp)
                .is_none_or(|home| home == seed_home)
        }) || captured.params.iter().any(|param| {
            self.promotion_facts
                .trusted_param_home_slot(*param)
                .is_none_or(|home| home == seed_home)
        })
    }

    fn find_fixed_set_list_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
    ) -> Option<usize> {
        for seed_index in (0..set_list_index).rev() {
            if let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) {
                if self.binding_is_shared_before_seed(block, seed_index, binding) {
                    return None;
                }
                if seed_binding == binding {
                    return (self.fixed_set_list_seed_is_safe(block, seed_index, binding)
                        && set_list_can_start_at(
                            seed,
                            current_set_list_start(block, set_list_index)?,
                        ))
                    .then_some(seed_index);
                }
                if !constructor_is_data_only(seed) || constructor_uses_binding(seed, binding) {
                    return None;
                }
                continue;
            }
            if !fixed_set_list_intermediate_is_safe(&block.stmts[seed_index], binding) {
                return None;
            }
        }
        None
    }

    fn open_set_list_seed_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> bool {
        let TableBinding::Local(local) = binding else {
            return false;
        };
        let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        seed_binding == binding
            && matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
            && seed.fields.is_empty()
            && seed.trailing_multivalue.is_none()
            && set_list.start_index == 1
            && set_list.values.tail.as_ref().is_some_and(|tail| {
                tail.exact_width().is_none()
                    && expr_is_open_tail_safe(tail.as_expr())
                    && !expr_uses_binding(tail.as_expr(), binding)
            })
            && set_list.values.fixed.iter().all(|value| {
                expr_is_data_only(value)
                    && expr_is_definitely_non_nil(value)
                    && !expr_uses_binding(value, binding)
            })
            && !self
                .debug_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            && !self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            // A branch-local LocalDecl may originate from a coalesced fixed temp rather than
            // retain the direct-SSA marker.  The declaration itself is still a fresh owner when
            // no earlier HIR statement mentions this LocalId; keep that lexical proof local to
            // the block instead of treating canonical temp coalescing as an alias.
            && !self.binding_is_shared_before_seed(block, seed_index, binding)
            && !self.promotion_facts.compacts_home_slots()
            && self
                .promotion_facts
                .trusted_local_home_slot(local)
                .is_some()
            && self.materialized_bindings.get(binding).copied() == Some(1)
    }

    /// Prove the one open-tail region whose allocation owner is an actual LocalDecl at block
    /// entry.  Scalar declarations may disappear into the constructor; named closure fields are
    /// retained only when no later write can replace the same field.  Keeping this proof local to
    /// HIR avoids treating an arbitrary raw/temp SETLIST as a normal table literal.
    fn open_local_constructor_region_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        end_index: usize,
        binding: TableBinding,
        constructor: &HirTableConstructor,
    ) -> bool {
        let TableBinding::Local(local) = binding else {
            return false;
        };
        let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        let Some(HirStmt::TableSetList(set_list)) = block.stmts.get(end_index) else {
            return false;
        };
        if seed_binding != binding
            || !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
            || seed.fields.iter().any(|field| match field {
                HirTableField::Array(value) => {
                    !expr_is_fixed_set_list_value_safe(value) || !expr_is_definitely_non_nil(value)
                }
                HirTableField::Record(record) => {
                    !record_key_is_data_only(&record.key)
                        || !expr_is_fixed_set_list_value_safe(&record.value)
                        || !expr_is_definitely_non_nil(&record.value)
                }
            })
            || seed.trailing_multivalue.is_some()
            || self
                .debug_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || binding_from_expr(&set_list.base) != Some(binding)
            || set_list.start_index == 0
            || set_list.start_index
                > u32::try_from(
                    seed.fields
                        .iter()
                        .filter(|field| matches!(field, HirTableField::Array(_)))
                        .count()
                        .saturating_add(1),
                )
                .unwrap_or(u32::MAX)
            || set_list.values.tail.is_none()
            || set_list.values.tail.as_ref().is_some_and(|tail| {
                tail.exact_width().is_some()
                    || !expr_is_open_tail_safe(tail.as_expr())
                    || expr_uses_binding(tail.as_expr(), binding)
            })
            || set_list.values.fixed.iter().any(|value| {
                !expr_is_fixed_set_list_value_safe(value) || expr_uses_binding(value, binding)
            })
            || set_list
                .values
                .tail
                .as_ref()
                .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
            || constructor.trailing_multivalue.is_none()
            || constructor_has_nil_field(constructor)
            || !array_fields_have_safe_nil_shape(&constructor.fields)
            || constructor_uses_binding(constructor, binding)
            || self.binding_is_shared_before_seed(block, seed_index, binding)
            || self.promotion_facts.compacts_home_slots()
            || self
                .promotion_facts
                .trusted_local_home_slot(local)
                .is_none()
            || self.materialized_bindings.get(binding).copied() != Some(1)
        {
            return false;
        }

        let mut object_record_names = BTreeSet::new();
        for stmt in &block.stmts[seed_index + 1..end_index] {
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    if decl.values.tail.is_some()
                        || decl
                            .bindings
                            .iter()
                            .any(|candidate| TableBinding::Local(*candidate) == binding)
                        || decl.bindings.iter().any(|candidate| {
                            let candidate = TableBinding::Local(*candidate);
                            self.debug_identity_bindings
                                .get(candidate)
                                .copied()
                                .unwrap_or_default()
                                || self
                                    .reference_captured_bindings
                                    .get(candidate)
                                    .copied()
                                    .unwrap_or_default()
                        })
                        || decl
                            .values
                            .fixed
                            .iter()
                            .any(|value| !expr_is_open_owner_snapshot(value))
                        || decl
                            .values
                            .fixed
                            .iter()
                            .any(|value| expr_uses_binding(value, binding))
                    {
                        return false;
                    }
                }
                HirStmt::Assign(assign) => {
                    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                        return false;
                    };
                    let [value] = assign.values.fixed.as_slice() else {
                        return false;
                    };
                    if assign.values.tail.is_some()
                        || binding_from_expr(&access.base) != Some(binding)
                        || expr_uses_binding(&access.key, binding)
                        || expr_uses_binding(value, binding)
                        || !expr_is_data_only(&access.key)
                        || !expr_is_fixed_set_list_value_safe(value)
                    {
                        return false;
                    }
                    if !producer_value_can_be_dropped(value) {
                        let HirTableKey::Name(name) =
                            table_key_from_expr(&access.key, self.dialect)
                        else {
                            return false;
                        };
                        if !object_record_names.insert(name) {
                            return false;
                        }
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn fixed_set_list_seed_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
    ) -> bool {
        let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        if seed_binding != binding
            || seed.trailing_multivalue.is_some()
            || seed.fields.iter().any(table_field_contains_nil)
            || !array_fields_have_safe_nil_shape(&seed.fields)
            || constructor_has_numeric_record(seed)
            || constructor_uses_binding(seed, binding)
            || self
                .debug_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
            || self
                .reference_captured_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
        {
            return false;
        }
        // Raw temps have no lexical declaration whose lifetime we can preserve. They are only
        // accepted by the separate canonical-adjacent path above; never let the generic scan
        // infer freshness from a home slot alone.
        if matches!(binding, TableBinding::Temp(_)) {
            return false;
        }
        // The LocalDecl remains the allocation owner. This fixed SETLIST fold only consumes
        // private data-only producer declarations, so it does not need the stronger direct-SSA
        // proof used when replacing a seed itself. Debug/capture identity is still a hard edge:
        // moving fields into the initializer changes what hooks or an escaped alias can observe.
        let ok = matches!(binding, TableBinding::Local(_)
            if matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
                && !self.promotion_facts.compacts_home_slots()
                && self.materialized_bindings.get(binding).copied() == Some(1));
        ok
    }

    fn fold_fixed_set_list_into_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        seed_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<(HirTableConstructor, Vec<usize>)> {
        if set_list.values.tail.is_some()
            || set_list.values.fixed.is_empty()
            || !self.fixed_set_list_seed_is_safe(block, seed_index, binding)
        {
            return None;
        }
        let (_, seed) = constructor_seed(&block.stmts[seed_index])?;
        if !set_list_can_start_at(seed, set_list.start_index) {
            return None;
        }

        let mut definitions = BTreeMap::<TableBinding, (usize, HirExpr)>::new();
        for stmt_index in seed_index + 1..set_list_index {
            let (defined_binding, value) = match &block.stmts[stmt_index] {
                HirStmt::LocalDecl(decl)
                    if decl.bindings.len() == 1
                        && decl.values.tail.is_none()
                        && decl.values.fixed.len() == 1 =>
                {
                    (
                        TableBinding::Local(decl.bindings[0]),
                        decl.values.fixed[0].clone(),
                    )
                }
                // An existing assignment owns the physical overwrite point of its target.
                // Moving it into the constructor can keep an old GC root alive (or change
                // parallel/lvalue evaluation), even when the assigned value is data-only.
                // The main region scanner already treats Assign as a hard producer barrier;
                // keep this fixed-SETLIST path on the same contract.
                _ => return None,
            };
            if defined_binding == binding
                || !expr_is_data_only(&value)
                || expr_uses_binding(&value, defined_binding)
                // Removing an intermediate source local changes its debug lifetime even when
                // its value is a scalar/reference expression.  Debug identity is not represented
                // in the constructor itself, so it must be a hard barrier here.
                || self
                    .debug_identity_bindings
                    .get(defined_binding)
                    .copied()
                    .unwrap_or_default()
                || self
                    .reference_captured_bindings
                    .get(defined_binding)
                    .copied()
                    .unwrap_or_default()
                || definitions
                    .insert(defined_binding, (stmt_index, value))
                    .is_some()
            {
                return None;
            }
        }

        // A producer can be removed only when it is private to this seed/SETLIST interval.
        // Build the prefix/suffix mention sets once: checking each producer by recursively
        // visiting the whole block made a large SETLIST quadratic in the number of producers.
        let prefix_mentions = collect_range_binding_mentions(block, 0, seed_index);
        let suffix_mentions =
            collect_range_binding_mentions(block, set_list_index + 1, block.stmts.len());
        if definitions
            .keys()
            .any(|binding| prefix_mentions.contains(binding) || suffix_mentions.contains(binding))
        {
            return None;
        }

        let mut resolved_values = Vec::with_capacity(set_list.values.fixed.len());
        for value in &set_list.values.fixed {
            let mut resolving = BTreeSet::new();
            let resolved = resolve_fold_expr(value, &definitions, &mut resolving)?;
            if expr_uses_binding(&resolved, binding) {
                return None;
            }
            resolved_values.push(resolved);
        }
        if !expressions_have_safe_nil_shape(&resolved_values) {
            return None;
        }

        let mut constructor = seed.clone();
        constructor
            .fields
            .extend(resolved_values.into_iter().map(HirTableField::Array));
        // The seed and the SETLIST values must be checked as one array run.  A final
        // maybe-nil seed slot is harmless only when it remains the final slot; appending a
        // definitely populated value changes `#t`/array-part semantics (for example,
        // `t[1] = x; t[2] = 1` with `x == nil` must not become `{ x, 1 }`).
        if !array_fields_have_safe_nil_shape(&constructor.fields) {
            return None;
        }
        let mut removed = definitions
            .values()
            .map(|(stmt_index, _)| *stmt_index)
            .collect::<Vec<_>>();
        removed.push(set_list_index);
        // `definitions` is keyed by binding identity, not source position.  The caller removes
        // these statements from the end so indices remain stable; sort by statement index
        // explicitly instead of relying on the unrelated binding ordering.
        removed.sort_unstable();
        Some((constructor, removed))
    }

    fn binding_is_shared_before_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
    ) -> bool {
        block_prefix_mentions_binding(block, seed_index, binding)
    }
}

fn constructor_with_set_list(
    seed: &HirTableConstructor,
    set_list: &crate::hir::common::HirTableSetList,
) -> HirTableConstructor {
    let mut constructor = seed.clone();
    constructor.fields.extend(
        set_list
            .values
            .fixed
            .iter()
            .cloned()
            .map(HirTableField::Array),
    );
    constructor.trailing_multivalue = set_list.values.tail.clone();
    constructor
}

fn block_prefix_mentions_binding(
    block: &crate::hir::common::HirBlock,
    end: usize,
    binding: TableBinding,
) -> bool {
    struct Probe {
        binding: TableBinding,
        found: bool,
    }
    impl HirVisitor for Probe {
        fn visit_expr(&mut self, expr: &HirExpr) {
            self.found |= expr_uses_binding(expr, self.binding);
        }

        fn visit_lvalue(&mut self, lvalue: &HirLValue) {
            self.found |= lvalue_uses_binding(lvalue, self.binding);
        }
    }
    let mut probe = Probe {
        binding,
        found: false,
    };
    visit_stmts(&block.stmts[..end], &mut probe);
    probe.found
}

fn collect_range_binding_mentions(
    block: &crate::hir::common::HirBlock,
    start: usize,
    end: usize,
) -> BTreeSet<TableBinding> {
    struct Probe {
        bindings: BTreeSet<TableBinding>,
    }

    impl HirVisitor for Probe {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            match stmt {
                HirStmt::NumericFor(numeric_for) => {
                    self.bindings
                        .insert(TableBinding::Local(numeric_for.binding));
                }
                HirStmt::GenericFor(generic_for) => {
                    self.bindings.extend(
                        generic_for
                            .bindings
                            .iter()
                            .copied()
                            .map(TableBinding::Local),
                    );
                }
                _ => {}
            }
        }

        fn visit_expr(&mut self, expr: &HirExpr) {
            if let Some(binding) = binding_from_expr(expr) {
                self.bindings.insert(binding);
            }
        }

        fn visit_lvalue(&mut self, lvalue: &HirLValue) {
            if let Some(binding) = binding_from_lvalue(lvalue) {
                self.bindings.insert(binding);
            }
        }
    }

    let mut probe = Probe {
        bindings: BTreeSet::new(),
    };
    if let Some(stmts) = block.stmts.get(start..end) {
        visit_stmts(stmts, &mut probe);
    }
    probe.bindings
}

fn current_set_list_start(block: &crate::hir::common::HirBlock, index: usize) -> Option<u32> {
    match block.stmts.get(index) {
        Some(HirStmt::TableSetList(set_list)) => Some(set_list.start_index),
        _ => None,
    }
}

fn set_list_can_start_at(seed: &HirTableConstructor, start_index: u32) -> bool {
    if seed.trailing_multivalue.is_some()
        || seed.fields.iter().any(table_field_contains_nil)
        || !array_fields_have_safe_nil_shape(&seed.fields)
        || seed.fields.iter().any(|field| {
            matches!(
                field,
                HirTableField::Record(record)
                    if !matches!(record.key, HirTableKey::Name(_))
            )
        })
    {
        return false;
    }
    let array_len = seed
        .fields
        .iter()
        .filter(|field| matches!(field, HirTableField::Array(_)))
        .count();
    u32::try_from(array_len)
        .ok()
        .and_then(|length| length.checked_add(1))
        == Some(start_index)
}

fn resolve_fold_expr(
    expr: &HirExpr,
    definitions: &BTreeMap<TableBinding, (usize, HirExpr)>,
    resolving: &mut BTreeSet<TableBinding>,
) -> Option<HirExpr> {
    if let Some(binding) = binding_from_expr(expr)
        && let Some((_, value)) = definitions.get(&binding)
    {
        if !resolving.insert(binding) {
            return None;
        }
        let resolved = resolve_fold_expr(value, definitions, resolving);
        resolving.remove(&binding);
        return resolved;
    }

    match expr {
        HirExpr::TableConstructor(constructor) => {
            if constructor.trailing_multivalue.is_some() {
                return None;
            }
            let mut resolved = HirTableConstructor::default();
            for field in &constructor.fields {
                resolved.fields.push(match field {
                    HirTableField::Array(value) => {
                        HirTableField::Array(resolve_fold_expr(value, definitions, resolving)?)
                    }
                    HirTableField::Record(record) => {
                        HirTableField::Record(crate::hir::common::HirRecordField {
                            key: match &record.key {
                                HirTableKey::Name(name) => HirTableKey::Name(name.clone()),
                                HirTableKey::Expr(key) => HirTableKey::Expr(resolve_fold_expr(
                                    key,
                                    definitions,
                                    resolving,
                                )?),
                            },
                            value: resolve_fold_expr(&record.value, definitions, resolving)?,
                        })
                    }
                });
            }
            Some(HirExpr::TableConstructor(Box::new(resolved)))
        }
        HirExpr::Closure(closure)
            if closure.captures.iter().all(|capture| {
                expr_is_data_only(&capture.value)
                    && definitions
                        .keys()
                        .all(|binding| !expr_uses_binding(&capture.value, *binding))
            }) =>
        {
            Some(expr.clone())
        }
        _ if expr_is_data_only(expr) => Some(expr.clone()),
        _ => None,
    }
}

fn fixed_set_list_intermediate_is_safe(stmt: &HirStmt, binding: TableBinding) -> bool {
    match stmt {
        HirStmt::LocalDecl(decl) => {
            !decl
                .bindings
                .iter()
                .copied()
                .map(TableBinding::Local)
                .any(|candidate| candidate == binding)
                && decl.values.tail.is_none()
                && decl.values.fixed.iter().all(expr_is_data_only)
                && !decl
                    .values
                    .fixed
                    .iter()
                    .any(|value| expr_uses_binding(value, binding))
        }
        HirStmt::Assign(assign) => {
            if assign.targets.iter().all(|target| {
                matches!(target, HirLValue::TableAccess(access)
                        if binding_from_expr(&access.base) == Some(binding)
                            && matches!(access.key, HirExpr::Integer(_)))
            }) && assign.values.tail.is_none()
                && assign.values.fixed.len() == assign.targets.len()
                && assign.values.fixed.iter().all(expr_is_data_only)
            {
                return true;
            }
            assign.targets.iter().all(|target| {
                binding_from_lvalue(target) != Some(binding)
                    && !lvalue_uses_binding(target, binding)
            }) && assign.values.tail.is_none()
                && assign.values.fixed.iter().all(expr_is_data_only)
                && !assign
                    .values
                    .fixed
                    .iter()
                    .any(|value| expr_uses_binding(value, binding))
        }
        HirStmt::TableSetList(set_list) => {
            binding_from_expr(&set_list.base) != Some(binding)
                && !expr_uses_binding(&set_list.base, binding)
                && set_list.values.tail.is_none()
                && set_list.values.fixed.iter().all(expr_is_data_only)
                && !set_list
                    .values
                    .fixed
                    .iter()
                    .any(|value| expr_uses_binding(value, binding))
        }
        _ => false,
    }
}

fn lvalue_uses_binding(lvalue: &HirLValue, binding: TableBinding) -> bool {
    match lvalue {
        HirLValue::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        _ => binding_from_lvalue(lvalue) == Some(binding),
    }
}

fn expr_is_data_only(expr: &HirExpr) -> bool {
    match expr {
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
        | HirExpr::LocalRef(_)
        | HirExpr::TempRef(_) => true,
        HirExpr::TableConstructor(constructor) => {
            constructor.fields.iter().all(|field| match field {
                HirTableField::Array(value) => expr_is_data_only(value),
                HirTableField::Record(record) => {
                    record_key_is_data_only(&record.key) && expr_is_data_only(&record.value)
                }
            }) && constructor
                .trailing_multivalue
                .as_ref()
                .is_none_or(|tail| expr_is_data_only(tail.as_expr()))
        }
        _ => false,
    }
}

fn expr_is_open_tail_safe(expr: &HirExpr) -> bool {
    // The LocalDecl/direct-owner proof keeps the allocation at the original seed statement, so
    // ordinary calls and lookups in the constructor tail retain their source evaluation point.
    // Unresolved/Decision nodes are different: they are unfinished HIR control and cannot be
    // moved into a normal constructor expression without a separate lowering proof.
    match expr {
        HirExpr::Decision(_) | HirExpr::Unresolved(_) => false,
        HirExpr::TableAccess(access) => {
            expr_is_open_tail_safe(&access.base) && expr_is_open_tail_safe(&access.key)
        }
        HirExpr::Unary(unary) => expr_is_open_tail_safe(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_open_tail_safe(&binary.lhs) && expr_is_open_tail_safe(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_open_tail_safe(&logical.lhs) && expr_is_open_tail_safe(&logical.rhs)
        }
        HirExpr::Call(call) => {
            expr_is_open_tail_safe(&call.callee) && call.args.iter().all(expr_is_open_tail_safe)
        }
        HirExpr::TableConstructor(constructor) => constructor.fields.iter().all(|field| match field
        {
            HirTableField::Array(value) => expr_is_open_tail_safe(value),
            HirTableField::Record(record) => {
                matches!(&record.key, HirTableKey::Name(_))
                    || matches!(&record.key, HirTableKey::Expr(key) if expr_is_open_tail_safe(key))
            }
        })
            && constructor
                .trailing_multivalue
                .as_ref()
                .is_none_or(|tail| expr_is_open_tail_safe(tail.as_expr())),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .all(|capture| expr_is_open_tail_safe(&capture.value)),
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
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg => true,
    }
}

/// A producer local may be removed from the narrow open-tail owner only when its initializer is
/// a direct snapshot read or an inert literal.  Calls, table access, constructors, and closures
/// remain explicit statements: moving those evaluations into the tail can change object roots or
/// observe a different binding even though the final constructor keeps the seed allocation point.
fn expr_is_open_owner_snapshot(expr: &HirExpr) -> bool {
    match expr {
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
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::TableAccess(access) => {
            expr_is_open_owner_snapshot(&access.base) && expr_is_open_owner_snapshot(&access.key)
        }
        HirExpr::Unary(unary) => expr_is_open_owner_snapshot(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_open_owner_snapshot(&binary.lhs) && expr_is_open_owner_snapshot(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_open_owner_snapshot(&logical.lhs) && expr_is_open_owner_snapshot(&logical.rhs)
        }
        HirExpr::Call(_)
        | HirExpr::Closure(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Decision(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

/// Prefix expressions may read an already-created table, but they must not execute a call,
/// decision, closure creation, or other user code while the fresh SETLIST owner is still private.
/// Keeping this separate from `expr_is_data_only` admits the field reads emitted by nested table
/// constructors without treating an arbitrary producer as inert.
fn expr_is_prefix_read_only(expr: &HirExpr) -> bool {
    expr_is_data_only(expr)
        || matches!(
            expr,
            HirExpr::TableAccess(access)
                if expr_is_prefix_read_only(&access.base)
                    && expr_is_prefix_read_only(&access.key)
        )
}

fn debug_prefix_stmt_is_inert(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(decl) => {
            decl.values.tail.is_none() && decl.values.fixed.iter().all(expr_is_data_only)
        }
        HirStmt::Assign(assign) => {
            assign.values.tail.is_none()
                && assign.values.fixed.iter().all(expr_is_data_only)
                && assign.targets.iter().all(|target| {
                    matches!(
                        target,
                        HirLValue::TableAccess(access)
                            if expr_is_data_only(&access.base)
                                && expr_is_data_only(&access.key)
                    )
                })
        }
        _ => false,
    }
}

/// Splitting raw SETLIST into indexed writes interleaves each write with evaluation of the next
/// value.  Scalar values and data-only nested constructors are safe: they cannot observe the
/// target table between writes, and the fresh-seed proof rules out metatable dispatch.
fn expr_is_indexed_set_list_value_safe(expr: &HirExpr) -> bool {
    if matches!(
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
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::TempRef(_)
    ) {
        return true;
    }
    let HirExpr::TableConstructor(constructor) = expr else {
        return false;
    };
    constructor.trailing_multivalue.is_none()
        && constructor.fields.iter().all(|field| match field {
            HirTableField::Array(value) => expr_is_indexed_set_list_value_safe(value),
            HirTableField::Record(record) => {
                record_key_is_data_only(&record.key)
                    && expr_is_indexed_set_list_value_safe(&record.value)
            }
        })
}

/// Values folded into one constructor may allocate as long as their expression order remains
/// unchanged and they execute no call/lookup/decision side effect.
fn expr_is_fixed_set_list_value_safe(expr: &HirExpr) -> bool {
    if expr_is_data_only(expr) {
        return true;
    }
    match expr {
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .all(|capture| expr_is_data_only(&capture.value)),
        HirExpr::TableConstructor(constructor) => {
            constructor.trailing_multivalue.is_none()
                && constructor.fields.iter().all(|field| match field {
                    HirTableField::Array(value) => expr_is_fixed_set_list_value_safe(value),
                    HirTableField::Record(record) => {
                        record_key_is_data_only(&record.key)
                            && expr_is_fixed_set_list_value_safe(&record.value)
                    }
                })
        }
        _ => false,
    }
}

fn constructor_is_data_only(constructor: &HirTableConstructor) -> bool {
    constructor.fields.iter().all(|field| match field {
        HirTableField::Array(value) => expr_is_data_only(value),
        HirTableField::Record(record) => {
            record_key_is_data_only(&record.key) && expr_is_data_only(&record.value)
        }
    }) && constructor
        .trailing_multivalue
        .as_ref()
        .is_none_or(|tail| expr_is_data_only(tail.as_expr()))
}

fn record_key_is_data_only(key: &crate::hir::common::HirTableKey) -> bool {
    match key {
        crate::hir::common::HirTableKey::Name(_) => true,
        crate::hir::common::HirTableKey::Expr(expr) => expr_is_data_only(expr),
    }
}

/// 只沿 statement/block 骨架查找本 pass 可能改写的根形状，不进入表达式子树。
fn block_has_table_constructor_candidate(block: &crate::hir::common::HirBlock) -> bool {
    block.stmts.iter().any(stmt_has_table_constructor_candidate)
}

fn stmt_has_table_constructor_candidate(stmt: &HirStmt) -> bool {
    if is_direct_constructor_candidate(stmt) {
        return true;
    }

    match stmt {
        HirStmt::If(if_stmt) => {
            block_has_table_constructor_candidate(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_has_table_constructor_candidate)
        }
        HirStmt::While(while_stmt) => block_has_table_constructor_candidate(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => block_has_table_constructor_candidate(&repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => {
            block_has_table_constructor_candidate(&numeric_for.body)
        }
        HirStmt::GenericFor(generic_for) => {
            block_has_table_constructor_candidate(&generic_for.body)
        }
        HirStmt::Block(block) => block_has_table_constructor_candidate(block),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn is_direct_constructor_candidate(stmt: &HirStmt) -> bool {
    constructor_seed(stmt).is_some()
}

fn region_has_direct_nil_field(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    end_index: usize,
) -> bool {
    block.stmts[(seed_index + 1)..=end_index]
        .iter()
        .any(|stmt| match stmt {
            HirStmt::Assign(assign) => assign.values.fixed.iter().any(expr_contains_nil),
            HirStmt::LocalDecl(local_decl) => local_decl.values.fixed.iter().any(expr_contains_nil),
            HirStmt::TableSetList(set_list) => set_list.values.fixed.iter().any(expr_contains_nil),
            _ => false,
        })
}

fn constructor_has_nil_field(constructor: &HirTableConstructor) -> bool {
    constructor.fields.iter().any(table_field_contains_nil)
        || constructor
            .trailing_multivalue
            .as_ref()
            .is_some_and(|tail| expr_contains_nil(tail.as_expr()))
}

fn constructor_has_numeric_record(constructor: &HirTableConstructor) -> bool {
    constructor.fields.iter().any(|field| {
        matches!(
            field,
            HirTableField::Record(record) if matches!(record.key, HirTableKey::Expr(_))
        )
    })
}

fn constructor_has_uncertain_array_field(constructor: &HirTableConstructor) -> bool {
    !array_fields_have_safe_nil_shape(&constructor.fields)
}

/// An array constructor may contain one value whose runtime nil-ness is unknown only when it
/// is the final array slot.  If a later slot is definitely populated, a preceding nil changes
/// the VM's array-part/length result (`t[1]=nil; t[2]=1` is not `{nil, 1}`).
fn expressions_have_safe_nil_shape(values: &[HirExpr]) -> bool {
    let mut saw_uncertain = false;
    for value in values {
        if expr_is_definitely_non_nil(value) {
            if saw_uncertain {
                return false;
            }
        } else if saw_uncertain {
            return false;
        } else {
            saw_uncertain = true;
        }
    }
    true
}

fn array_fields_have_safe_nil_shape(fields: &[HirTableField]) -> bool {
    let values = fields
        .iter()
        .filter_map(|field| match field {
            HirTableField::Array(value) => Some(value.clone()),
            HirTableField::Record(_) => None,
        })
        .collect::<Vec<_>>();
    expressions_have_safe_nil_shape(&values)
}

fn array_fields_contain_uncertain_value(fields: &[HirTableField]) -> bool {
    fields.iter().any(|field| {
        matches!(
            field,
            HirTableField::Array(value) if !expr_is_definitely_non_nil(value)
        )
    })
}

fn region_has_exact_width_tail(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    end_index: usize,
) -> bool {
    block.stmts[(seed_index + 1)..=end_index]
        .iter()
        .any(|stmt| {
            matches!(
                stmt,
                HirStmt::TableSetList(set_list)
                    if set_list
                        .values
                        .tail
                        .as_ref()
                        .is_some_and(|tail| tail.exact_width().is_some())
            )
        })
}

fn table_field_contains_nil(field: &HirTableField) -> bool {
    match field {
        HirTableField::Array(value) => expr_contains_nil(value),
        HirTableField::Record(record) => {
            record_key_contains_nil(&record.key) || expr_contains_nil(&record.value)
        }
    }
}

fn record_key_contains_nil(key: &crate::hir::common::HirTableKey) -> bool {
    match key {
        crate::hir::common::HirTableKey::Expr(expr) => expr_contains_nil(expr),
        crate::hir::common::HirTableKey::Name(_) => false,
    }
}

fn expr_contains_nil(expr: &HirExpr) -> bool {
    struct NilProbe {
        found: bool,
    }

    impl HirVisitor for NilProbe {
        fn visit_expr(&mut self, expr: &HirExpr) {
            self.found |= matches!(expr, HirExpr::Nil);
        }
    }

    let mut probe = NilProbe { found: false };
    crate::hir::simplify::visit::visit_expr(expr, &mut probe);
    probe.found
}
