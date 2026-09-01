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
//! fixed SETLIST 的非相邻 local 路径只改写 SETLIST 本身，producer LocalDecl 保持原位；
//! 该边界同时保留 initializer 的求值次数与独立 GC root，不用复制表达式来换取展示折叠。

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
    expr_uses_binding,
};
use self::builder::expr_is_definitely_non_nil;
use self::rebuild::producer_value_can_be_dropped;
use self::scan::{
    ConstructorWriteIndex, constructor_seed, constructor_uses_binding, install_constructor_seed,
    seed_delay_expr_is_unobservable, seed_overwrite_delay_is_unobservable,
    try_rebuild_constructor_region,
};
use super::boolean_shells::complete_possible_home_slots;
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

#[derive(Debug, Clone, Copy)]
enum RegionStep {
    Producer {
        stmt_index: usize,
        slot_index: usize,
        source_preservation: ProducerSourcePreservation,
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
    source_preservation: ProducerSourcePreservation,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ProducerSourcePreservation {
    Safe,
    InertWholeStatement,
    DebugIdentity,
    ObservableReplay,
    UnsupportedShape,
}

#[derive(Debug, Clone)]
enum PendingProducerSource {
    Value {
        stmt_index: usize,
        value_index: usize,
    },
    ImplicitNil {
        // Closed Lua assignments pad every target after the fixed RHS with nil.
        stmt_index: usize,
    },
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
    tokens: Vec<SegmentToken>,
    prepared_records: Vec<PreparedRecord>,
    prepared_eval_events: Vec<ConstructorEvalEvent>,
    source_eval_events: Vec<ConstructorEvalEvent>,
    generated_eval_events: Vec<ConstructorEvalEvent>,
    producer_index_by_binding: Vec<Option<usize>>,
    consumed_bindings: Vec<bool>,
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
        #[cfg(test)]
        direct_set_list_rebuilds: 0,
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
    #[cfg(test)]
    direct_set_list_rebuilds: usize,
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
                    &self.debug_identity_bindings,
                    &stmt_ids,
                    self.dialect,
                    &mut scratch,
                );
                candidate.filter(|(rebuilt_constructor, end_index, preserved_stmt_indices)| {
                    let open_local_owner = rebuilt_constructor.trailing_multivalue.is_some()
                        && self.open_local_constructor_region_is_safe(
                            block,
                            index,
                            *end_index,
                            binding,
                            rebuilt_constructor,
                            preserved_stmt_indices,
                        );
                    let open_capture_is_safe = rebuilt_constructor.trailing_multivalue.is_none()
                        || self.open_local_constructor_capture_region_is_safe(
                            block, index, *end_index, binding,
                        );
                    // Value-position nil is governed by the completed table shape, not by whether
                    // a nil literal happened to occur in a producer. A final absent array slot and
                    // a nil-valued record field preserve the same key set as the original writes.
                    let nil_shape_is_supported =
                        constructor_nil_shape_is_supported(&seed_ctor, rebuilt_constructor);
                    // Lua emits constructor array fields through a deferred SETLIST batch.  A
                    // later numeric record that aliases an earlier array field therefore cannot
                    // represent a later overwrite: `{ value, [1] = nil }` leaves `value` at key
                    // 1 on Lua 5.4/5.5.  Keep the explicit post-constructor write when rebuilding
                    // would introduce that source shape; lua54_01_close#13 observes the value.
                    // 候选拒绝[SemanticBarrier:TableShape]：constructor codegen 的 array batch
                    // 会覆盖源码中更晚的同键 record，不能表达原语句的最终 table 内容。
                    let adds_late_array_overwrite =
                        !constructor_has_late_record_overwriting_array(&seed_ctor)
                            && constructor_has_late_record_overwriting_array(rebuilt_constructor);
                    // 候选拒绝[SemanticBarrier:ValueArity]：`HirTableConstructor` 只有 open
                    // trailing pack，AST lowering 也拒绝 exact-width tail。若 `f()` 返回三个值，
                    // 原 SETLIST 的 exact width 2 只写两个槽，而 `{ f() }` 会写入三个槽。
                    let unsupported_exact_width =
                        region_has_exact_width_tail(block, index, *end_index);
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
                    // 候选拒绝[SemanticBarrier:Lifetime]：反例见
                    // tests/unit-case/lua54_01_close.lua#lua54_01_close#13/#14/#16。
                    let producer_root_is_observable = region_has_non_drop_safe_producer(
                        block,
                        index,
                        *end_index,
                        preserved_stmt_indices,
                    ) && collect_range_binding_mentions(
                        block,
                        *end_index + 1,
                        block.stmts.len(),
                    )
                    .contains(&binding);
                    // 候选拒绝[SemanticBarrier:Lifetime]：对象 producer 后再覆盖 table field
                    // 时，删除 producer 会提前释放最后一个强引用；反例同上。
                    let has_followup_object_write =
                        region_has_followup_table_write_after_object_producer(
                            block,
                            index,
                            *end_index,
                            binding,
                            preserved_stmt_indices,
                        );
                    // A source LocalDecl has no visible owner before its initializer completes;
                    // with no debug identity, folding later fields into that initializer cannot
                    // expose a delayed store.  Temp seeds do overwrite an existing VM slot, so an
                    // observable region must retain the explicit store before later evaluation.
                    // 候选拒绝[SemanticBarrier:EvalOrder]：lua54_01_close#8 通过调用观察 temp
                    // seed overwrite 被延后；eventless region 仍由下方精确 helper 放行。
                    let source_local_owner = matches!(binding, TableBinding::Local(_))
                        && matches!(block.stmts[index], HirStmt::LocalDecl(_))
                        && !self
                            .debug_identity_bindings
                            .get(binding)
                            .copied()
                            .unwrap_or_default();
                    let overwrite_timing_is_safe = open_local_owner
                        || source_local_owner
                        || seed_overwrite_delay_is_unobservable(block, index, *end_index, binding);
                    open_capture_is_safe
                        && nil_shape_is_supported
                        && !adds_late_array_overwrite
                        && !unsupported_exact_width
                        && !producer_root_is_observable
                        && !has_followup_object_write
                        && overwrite_timing_is_safe
                })
            } else {
                None
            };
            let (constructor, end_index, preserved_stmt_indices, rebuilt_region) = match rebuilt {
                Some((rebuilt_ctor, end_index, preserved_stmt_indices)) => {
                    (rebuilt_ctor, end_index, preserved_stmt_indices, true)
                }
                None => (seed_ctor, index, Vec::new(), false),
            };

            if !rebuilt_region {
                index += 1;
                continue;
            }

            install_constructor_seed(&mut block.stmts[index], constructor);
            let drain_end = end_index;
            if drain_end > index {
                for i in (index + 1..=drain_end).rev() {
                    if preserved_stmt_indices.binary_search(&i).is_ok() {
                        continue;
                    }
                    binding_occurrences.remove_stmt(stmt_ids[i], &stmt_bindings[i]);
                    block.stmts.remove(i);
                    stmt_bindings.remove(i);
                    stmt_ids.remove(i);
                }
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
    preserved_stmt_indices: &[usize],
) -> bool {
    block.stmts[start_index + 1..=end_index]
        .iter()
        .enumerate()
        .any(|(offset, stmt)| {
            let stmt_index = start_index + 1 + offset;
            preserved_stmt_indices.binary_search(&stmt_index).is_err()
                && stmt_has_non_drop_safe_producer(stmt)
        })
}

fn region_has_followup_table_write_after_object_producer(
    block: &crate::hir::common::HirBlock,
    start_index: usize,
    end_index: usize,
    binding: TableBinding,
    preserved_stmt_indices: &[usize],
) -> bool {
    if end_index <= start_index {
        return false;
    }
    let mut object_producer_seen = false;
    let mut first_table_write_after_producer = false;
    for (offset, stmt) in block.stmts[start_index + 1..=end_index].iter().enumerate() {
        let stmt_index = start_index + 1 + offset;
        if preserved_stmt_indices.binary_search(&stmt_index).is_err()
            && stmt_has_non_drop_safe_producer(stmt)
        {
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

            // 相邻的源码 LocalDecl 与 SETLIST 是 VM 对同一个构造器初始化的拆分编码。
            // direct-seed provenance 证明 allocation 仍在原声明位置，SETLIST start 又证明数组
            // 段连续，因此合并不会跨 producer，也不会改变字段求值、nil 槽或 fixed-call 宽度。
            // debug local 仍由同一 LocalDecl 持有，而且 Lua initializer 求值时该 binding 尚不可见；
            // 把 fixed/open batch 放回 initializer 正好恢复这条词法边界。
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
            // while the helper below separately proves value events and a hole-free seed.
            if let Some(seed_index) =
                self.find_direct_set_list_seed(block, index, binding, &set_list)
            {
                let Some((_, seed)) = constructor_seed(&block.stmts[seed_index]) else {
                    unreachable!("direct SETLIST seed must be a constructor");
                };
                let constructor = constructor_with_set_list(seed, &set_list);
                install_constructor_seed(&mut block.stmts[seed_index], constructor);
                block.stmts.remove(index);
                #[cfg(test)]
                {
                    self.direct_set_list_rebuilds += 1;
                }
                changed = true;
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

            // A raw SETLIST is not generally equivalent to ordinary indexed assignment:
            // the former bypasses `__newindex` and has distinct nil-hole/array-part rules.
            // If the seed proof above did not let us rebuild it as a constructor, leave the
            // semantic node for a dialect-aware lowering instead of silently changing it.
            // Every failed candidate was rejected by its provenance, shape, arity, or event guard
            // above; this branch only retains the already-classified residual node.
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
        if seed_binding != binding || local_decl.bindings.as_slice() != [local] {
            return None;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：已有 constructor open tail 之后不能再追加
        // SETLIST，后续隐式字段会被前一个多返回值覆盖；反例见 regress_52。
        if seed.trailing_multivalue.is_some() {
            return None;
        }
        // 候选拒绝[SemanticBarrier:Scope]：initializer 内读取 `local` owner 会解析到外层
        // binding；`local t = {}; t[1] = t` 不能写成 `local t = { t }`。
        if constructor_uses_binding(seed, binding)
            || set_list
                .values
                .iter()
                .any(|value| expr_uses_binding(value, binding))
        {
            return None;
        }
        // The adjacent LocalDecl is itself the value-provenance witness: no statement can
        // replace or publish the freshly allocated table between the seed and SETLIST.  A
        // trusted physical home is neither required nor sufficient for that value identity.
        if set_list.values.fixed.is_empty() && set_list.values.tail.is_none() {
            return None;
        }
        if let Some(tail) = &set_list.values.tail {
            // 候选拒绝[SemanticBarrier:ValueArity]：constructor/AST 只有 open tail；若
            // `f()` 返回三个值，exact width 2 只能取前两个，直接写成 `{ f() }` 会多写一槽。
            if tail.exact_width().is_some() {
                return None;
            }
            // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出的失败证据；
            // table pass 不把它埋进普通 constructor 表达式。
            if !expr_is_open_tail_safe(tail.as_expr()) {
                return None;
            }
        }
        // 候选拒绝[LayerBoundary]：fixed 值中的 Decision 由 decision/eliminate 消费。
        // 候选拒绝[PolicyBoundary]：fixed Unresolved 保留为 permissive 失败证据。
        if set_list
            .values
            .fixed
            .iter()
            .any(|value| !expr_is_open_tail_safe(value))
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

    fn find_direct_set_list_seed(
        &self,
        block: &crate::hir::common::HirBlock,
        set_list_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> Option<usize> {
        let seed_index = set_list_index.checked_sub(1)?;
        let (seed_binding, seed) = constructor_seed(&block.stmts[seed_index])?;
        if seed_binding != binding {
            return None;
        }
        let next_array_index = u32::try_from(
            seed.fields
                .iter()
                .filter(|field| matches!(field, HirTableField::Array(_)))
                .count(),
        )
        .ok()?
        .checked_add(1)?;
        // 候选拒绝[SemanticBarrier:TableShape]：raw SETLIST 起点不是下一个隐式数组键时，
        // 直接追加 constructor array field 会改变实际 key。
        if set_list.start_index != next_array_index {
            return None;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：已有 open constructor tail 后不能再追加 batch；
        // 反例见 regress_52_table_trailing_multivalue_boundary。
        if seed.trailing_multivalue.is_some() {
            return None;
        }
        // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
        // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。
        if set_list
            .values
            .fixed
            .iter()
            .any(|value| !expr_is_open_tail_safe(value))
        {
            return None;
        }
        if matches!(binding, TableBinding::Temp(_))
            && set_list
                .values
                .fixed
                .iter()
                .any(|value| !seed_delay_expr_is_unobservable(value))
        {
            // 候选拒绝[SemanticBarrier:EvalOrder]：把相邻 SETLIST value 收进 temp assignment
            // 会把 seed slot overwrite 延后到 value 求值之后；lua54_01_close#8 可观察该差异。
            return None;
        }
        // 候选拒绝[SemanticBarrier:TableShape]：seed 的不确定 nil 槽后追加确定 batch 会改变
        // 键集合/`#table`；反例见 lua54_01_close#15。
        if !array_fields_have_safe_nil_shape(&seed.fields) {
            return None;
        }
        // 候选拒绝[SemanticBarrier:Scope]：owner 自引用不能搬进自身 initializer。
        if constructor_uses_binding(seed, binding)
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| expr_uses_binding(value, binding))
        {
            return None;
        }
        if set_list.values.fixed.is_empty() && set_list.values.tail.is_none() {
            return None;
        }
        // 该 helper 只处理 fixed batch；open batch 由 open-owner 路径单独证明。
        if set_list.values.tail.is_some() {
            return None;
        }
        // seed 与 fixed 值仍在原求值点执行，且改写保留 seed binding/root；后续 capture 观察到的
        // 仍是同一个 table identity，不构成这条窄 direct path 的拒绝理由。
        // Syntactic adjacency plus direct origin identifies this exact fresh seed statement. Do not
        // rescan the whole prefix here; large compiler-generated tables can contain thousands of
        // SETLIST batches.
        match binding {
            TableBinding::Temp(temp) => {
                // 普通紧邻路径只把 direct raw allocation 且 home 未失效的 temp 纳入候选。
                (self.promotion_facts.is_direct_table_seed_temp(temp)
                    && self.promotion_facts.trusted_temp_home_slot(temp).is_some())
                .then_some(seed_index)
            }
            TableBinding::Local(local) => {
                if !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_)) {
                    return None;
                }
                // local 也必须仍对应 direct raw allocation 及其未失效的精确 home。
                (self.promotion_facts.is_direct_table_seed_local(local)
                    && self
                        .promotion_facts
                        .trusted_local_home_slot(local)
                        .is_some())
                .then_some(seed_index)
            }
        }
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
        if set_list.values.tail.is_some() || set_list.values.fixed.is_empty() {
            return None;
        }
        // 候选拒绝[SemanticBarrier:EvalOrder]：逐项写入会与后续值求值交错，而 raw
        // SETLIST 在所有值求完后才写表。
        if set_list
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
            if !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_)) {
                return None;
            }
            if seed.trailing_multivalue.is_some() {
                // 候选拒绝[TargetConstraint]：Lua constructor 语法只能让最后一个数组字段
                // 保留多返回值，无法表示 open seed 之后仍有 fixed batch。
                // 候选拒绝[SemanticBarrier:ValueArity]：强行标量化 open tail 会在它返回
                // 多值时丢槽，保留展开又会与后续 fixed key 产生不同覆盖关系。
                return None;
            }
            // 候选拒绝[SemanticBarrier:Scope]：owner 自引用不能参与 fresh-seed 证明。
            if constructor_uses_binding(seed, binding) {
                return None;
            }
            // 候选拒绝[SemanticBarrier:TableShape]：不确定 nil seed 或越过连续数组边界的
            // raw SETLIST 与逐项 SETTABLE 可能形成不同 array part/`#table`。
            if !array_fields_have_safe_nil_shape(&seed.fields) || !set_list_can_overwrite_seed {
                return None;
            }
            if !local_set_list_values_have_safe_nil_shape(
                block,
                seed_index,
                set_list_index,
                &set_list.values.fixed,
            ) {
                // 候选拒绝[SemanticBarrier:TableShape]：raw SETLIST 与逐项 SETTABLE 对中间
                // nil hole 的 array part/`#table` 不等价；官方 Lua 5.4 反例见 regress_337。
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
        // A fixed SETLIST rewrite keeps the seed declaration and every prefix statement in
        // place.  Home provenance therefore cannot by itself prove value aliasing (or an
        // overwrite): homes identify storage, not the value epoch in that storage.  Complete
        // possible-home facts are only used below to conservatively discover values which may
        // currently carry the seed into an observable context.
        let seed_homes = self.promotion_facts.possible_local_home_slots(seed_local);
        let debug_seed = self
            .debug_identity_bindings
            .get(binding)
            .copied()
            .unwrap_or_default();
        // The LocalDecl at `seed_index` is the fresh owner whose allocation remains in place.
        // Prefix writes may target it directly; without seeding this set, the final membership
        // check could never accept the very owner the proof started from.
        let mut fresh_tables = BTreeSet::from([binding]);
        let mut seed_aliases = BTreeSet::from([binding]);
        let mut seed_carriers = BTreeSet::new();
        let mut seed_tbc_active = false;
        for (offset, stmt) in block.stmts[seed_index..set_list_index].iter().enumerate() {
            let stmt_index = seed_index + offset;
            if stmt_index != seed_index && debug_seed && !debug_prefix_stmt_is_inert(stmt) {
                // 候选拒绝[SemanticBarrier:DebugScope]：effectful prefix 可通过
                // `debug.getlocal(2, 1)` 取得 source-visible seed 并安装 metatable；原始 raw
                // SETLIST 绕过 `__newindex`，拆成 indexed writes 后会触发它。
                return false;
            }
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    if decl.bindings.contains(&seed_local) && stmt_index != seed_index {
                        // A second declaration of the seed binding would create a new lexical
                        // owner, so the indexed-write proof must stop at that boundary.
                        // 候选拒绝[SemanticBarrier:Scope]：同 binding 的第二个 LocalDecl 已切换
                        // lexical owner，后续 SETLIST 不能归属于旧 seed。
                        return false;
                    }
                    let values_may_carry_seed = decl.values.iter().any(|value| {
                        self.expr_may_carry_seed(
                            value,
                            seed_homes.as_ref(),
                            &seed_aliases,
                            &seed_carriers,
                        )
                    });
                    if values_may_carry_seed
                        && !decl.values.iter().all(|value| {
                            self.expr_is_seed_transport_safe(value, &seed_aliases, &fresh_tables)
                        })
                    {
                        // 候选拒绝[SemanticBarrier:Metamethod]：call/operator/external lookup
                        // 若取得 seed，可在 raw SETLIST 前安装 `__newindex`；原操作绕过
                        // 元方法，而 indexed fallback 会触发它。
                        return false;
                    }
                    if values_may_carry_seed {
                        seed_carriers
                            .extend(decl.bindings.iter().copied().map(TableBinding::Local));
                        if decl.values.fixed.len() == 1
                            && decl.values.tail.is_none()
                            && binding_from_expr(&decl.values.fixed[0])
                                .is_some_and(|source| seed_aliases.contains(&source))
                        {
                            seed_aliases
                                .extend(decl.bindings.iter().copied().map(TableBinding::Local));
                        }
                    }
                    if let Some((candidate, _)) = constructor_seed(stmt) {
                        debug_assert!(matches!(candidate, TableBinding::Local(_)));
                        // A fresh local container may retain the seed as inert data.  It remains
                        // safe until that carrier is passed to an observable context, which the
                        // subsequent prefix scan rejects.
                        fresh_tables.insert(candidate);
                    }
                }
                HirStmt::Goto(_) | HirStmt::Label(_) => {
                    // 候选拒绝[SemanticBarrier:ControlFlow]：backward goto 可在首次 SETLIST 后
                    // 安装 metatable 再跳回 label；raw SETLIST 仍绕过 `__newindex`，indexed
                    // writes 则会触发它，因此必须先有单次执行/dominance 证明。
                    return false;
                }
                HirStmt::ToBeClosed(tbc) => {
                    if self.expr_may_carry_seed(
                        &tbc.value,
                        seed_homes.as_ref(),
                        &seed_aliases,
                        &seed_carriers,
                    ) {
                        if !self.expr_is_seed_transport_safe(
                            &tbc.value,
                            &seed_aliases,
                            &fresh_tables,
                        ) {
                            // 候选拒绝[SemanticBarrier:Metamethod]：resource 求值在
                            // call/lookup/operator 中暴露 seed，可在 SETLIST 前安装
                            // metatable。
                            return false;
                        }
                        // Merely registering a TBC value executes no cleanup.  The SETLIST still
                        // precedes the normal scope close, so only an explicit Close in the prefix
                        // can invalidate freshness.
                        seed_tbc_active = true;
                    }
                }
                HirStmt::Close(_) if seed_tbc_active => {
                    // 候选拒绝[SemanticBarrier:Close]：`__close` 获得 seed 并可在
                    // raw SETLIST 前安装 metatable；indexed writes 随后会触发
                    // `__newindex`，而 raw SETLIST 不会。
                    return false;
                }
                HirStmt::Close(_) => {}
                HirStmt::Assign(assign) => {
                    let values_may_carry_seed = assign.values.iter().any(|value| {
                        self.expr_may_carry_seed(
                            value,
                            seed_homes.as_ref(),
                            &seed_aliases,
                            &seed_carriers,
                        )
                    });
                    if values_may_carry_seed
                        && !assign.values.iter().all(|value| {
                            self.expr_is_seed_transport_safe(value, &seed_aliases, &fresh_tables)
                        })
                    {
                        // 候选拒绝[SemanticBarrier:Metamethod]：RHS 在 call/operator/lookup
                        // 中暴露 seed 时可安装 metatable，使 raw SETLIST 与 indexed writes
                        // 产生可观察差异。
                        return false;
                    }
                    for target in &assign.targets {
                        match target {
                            HirLValue::TableAccess(access) => {
                                let key_may_carry_seed = self.expr_may_carry_seed(
                                    &access.key,
                                    seed_homes.as_ref(),
                                    &seed_aliases,
                                    &seed_carriers,
                                );
                                if key_may_carry_seed
                                    && !self.expr_is_seed_transport_safe(
                                        &access.key,
                                        &seed_aliases,
                                        &fresh_tables,
                                    )
                                {
                                    // 候选拒绝[SemanticBarrier:Metamethod]：key 的 call/lookup/
                                    // operator 可在返回 key 前取得 seed 并安装 metatable。
                                    return false;
                                }
                                if let Some(base) = binding_from_expr(&access.base)
                                    && (seed_aliases.contains(&base)
                                        || fresh_tables.contains(&base))
                                {
                                    continue;
                                }
                                if values_may_carry_seed || key_may_carry_seed {
                                    // 候选拒绝[SemanticBarrier:Metamethod]：将 seed 作为 external
                                    // table 的 key/value 会把它交给 `__newindex`，回调可在
                                    // 后续 raw SETLIST 前安装 seed metatable。
                                    return false;
                                }
                                if self.expr_may_carry_seed(
                                    &access.base,
                                    seed_homes.as_ref(),
                                    &seed_aliases,
                                    &seed_carriers,
                                ) && !self.expr_is_seed_transport_safe(
                                    &access.base,
                                    &seed_aliases,
                                    &fresh_tables,
                                ) {
                                    // 候选拒绝[SemanticBarrier:Metamethod]：复合 base 可在
                                    // 求值时经 lookup/operator 把 seed 交给用户代码，不具备 direct
                                    // fresh-owner 的元方法空集证明。
                                    return false;
                                }
                            }
                            HirLValue::Local(local) if *local == seed_local => {
                                // 候选拒绝[SemanticBarrier:Metamethod]：直接重写 owner 后，
                                // SETLIST 可面向已有 metatable 的表；raw 与 indexed 路径不等价。
                                return false;
                            }
                            HirLValue::Param(_) | HirLValue::Upvalue(_) | HirLValue::Global(_)
                                if values_may_carry_seed =>
                            {
                                // 候选拒绝[SemanticBarrier:Escape]：把 seed 发布到非本地
                                // binding 后，区间内回调可安装 metatable；当前线性
                                // fallback 不再具备 fresh-owner 不变量。
                                return false;
                            }
                            _ => {}
                        }
                    }
                    if values_may_carry_seed
                        && assign.targets.iter().all(|target| {
                            matches!(target, HirLValue::Local(_) | HirLValue::Temp(_))
                        })
                    {
                        for target in &assign.targets {
                            let Some(target) = binding_from_lvalue(target) else {
                                continue;
                            };
                            seed_carriers.insert(target);
                        }
                        if assign.targets.len() == 1
                            && assign.values.fixed.len() == 1
                            && assign.values.tail.is_none()
                            && binding_from_expr(&assign.values.fixed[0])
                                .is_some_and(|source| seed_aliases.contains(&source))
                            && let Some(target) = binding_from_lvalue(&assign.targets[0])
                        {
                            seed_aliases.insert(target);
                        }
                    }
                }
                HirStmt::If(_)
                | HirStmt::While(_)
                | HirStmt::Repeat(_)
                | HirStmt::NumericFor(_)
                | HirStmt::GenericFor(_)
                | HirStmt::Block(_)
                | HirStmt::Return(_)
                | HirStmt::Break
                | HirStmt::Continue => {
                    if seed_tbc_active && stmt_contains_close(stmt) {
                        // 候选拒绝[SemanticBarrier:Close]：嵌套 block 的显式 Close
                        // 可在回到 SETLIST 前经 seed-bearing TBC resource 安装
                        // metatable。
                        return false;
                    }
                    let Some(structured_carriers) = self.structured_stmt_seed_carriers(
                        stmt,
                        binding,
                        seed_homes.as_ref(),
                        &seed_aliases,
                        &seed_carriers,
                        &fresh_tables,
                    ) else {
                        // 候选拒绝[SemanticBarrier:Escape]：结构化分支/循环内可重写
                        // owner，或将 seed 发布后调用回调安装 metatable；例如
                        // `if c then owner = existing end` 或 `alias = seed;
                        // install(alias)`。完全 disjoint 或仅在纯数据上传递 seed 的控制
                        // 保持原位，可直接穿过。
                        return false;
                    };
                    // The structured statement remains in place, but carriers assigned on a
                    // fallthrough arm are visible to following prefix statements.  Commit the
                    // path-union so a later call/store cannot lose the escape relation.
                    seed_carriers.extend(structured_carriers);
                }
                HirStmt::GlobalDecl(_)
                | HirStmt::TableSetList(_)
                | HirStmt::ErrNil(_)
                | HirStmt::CallStmt(_) => {
                    if self.stmt_may_carry_seed(
                        stmt,
                        seed_homes.as_ref(),
                        &seed_aliases,
                        &seed_carriers,
                    ) {
                        // 候选拒绝[SemanticBarrier:Escape]：call/capture/external store 直接
                        // 发布 seed，用户代码可在 raw SETLIST 前安装 metatable。
                        return false;
                    }
                }
            }
        }
        fresh_tables.contains(&binding)
    }

    fn expr_may_carry_seed(
        &self,
        expr: &HirExpr,
        seed_homes: Option<&BTreeSet<HomeSlotKey>>,
        seed_aliases: &BTreeSet<TableBinding>,
        seed_carriers: &BTreeSet<TableBinding>,
    ) -> bool {
        struct Probe<'a> {
            promotion_facts: &'a ProtoPromotionFacts,
            seed_homes: Option<&'a BTreeSet<HomeSlotKey>>,
            seed_aliases: &'a BTreeSet<TableBinding>,
            seed_carriers: &'a BTreeSet<TableBinding>,
            found: bool,
        }

        impl HirVisitor for Probe<'_> {
            fn visit_expr(&mut self, expr: &HirExpr) {
                self.found |= match expr {
                    HirExpr::LocalRef(local) => {
                        self.seed_aliases.contains(&TableBinding::Local(*local))
                            || self.seed_carriers.contains(&TableBinding::Local(*local))
                            || self.seed_homes.is_some_and(|seed_homes| {
                                !seed_homes.is_empty()
                                    && self
                                        .promotion_facts
                                        .possible_local_home_slots(*local)
                                        .is_none_or(|homes| {
                                            homes.iter().any(|home| seed_homes.contains(home))
                                        })
                            })
                    }
                    HirExpr::TempRef(temp) => {
                        self.seed_aliases.contains(&TableBinding::Temp(*temp))
                            || self.seed_carriers.contains(&TableBinding::Temp(*temp))
                            || self.seed_homes.is_some_and(|seed_homes| {
                                !seed_homes.is_empty()
                                    && self
                                        .promotion_facts
                                        .possible_temp_home_slots(*temp)
                                        .is_none_or(|homes| {
                                            homes.iter().any(|home| seed_homes.contains(home))
                                        })
                            })
                    }
                    HirExpr::ParamRef(param) => self.seed_homes.is_some_and(|seed_homes| {
                        !seed_homes.is_empty()
                            && self
                                .promotion_facts
                                .possible_param_home_slots(*param)
                                .is_none_or(|homes| {
                                    homes.iter().any(|home| seed_homes.contains(home))
                                })
                    }),
                    _ => false,
                };
            }
        }

        let mut probe = Probe {
            promotion_facts: self.promotion_facts,
            seed_homes,
            seed_aliases,
            seed_carriers,
            found: false,
        };
        crate::hir::simplify::visit::visit_expr(expr, &mut probe);
        probe.found
    }

    fn captures_may_share_seed_home(
        &self,
        captured: &ReferenceCapturedBindings,
        seed_local: LocalId,
        seed_homes: &BTreeSet<HomeSlotKey>,
    ) -> bool {
        captured.locals.iter().any(|local| {
            *local == seed_local
                || !complete_possible_home_slots(
                    self.promotion_facts.possible_local_home_slots(*local),
                    self.promotion_facts,
                )
                .is_disjoint(seed_homes)
        }) || captured.temps.iter().any(|temp| {
            !complete_possible_home_slots(
                self.promotion_facts.possible_temp_home_slots(*temp),
                self.promotion_facts,
            )
            .is_disjoint(seed_homes)
        }) || captured.params.iter().any(|param| {
            !complete_possible_home_slots(
                self.promotion_facts.possible_param_home_slots(*param),
                self.promotion_facts,
            )
            .is_disjoint(seed_homes)
        })
    }

    fn open_local_constructor_capture_region_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        end_index: usize,
        binding: TableBinding,
    ) -> bool {
        let TableBinding::Local(local) = binding else {
            return false;
        };
        let seed_homes = complete_possible_home_slots(
            self.promotion_facts.possible_local_home_slots(local),
            self.promotion_facts,
        );
        // 候选拒绝[SemanticBarrier:Capture]：ByReference closure 可持续观察 owner cell，
        // ByValue closure 则在 producer 原位置冻结该 cell；把 producer 移入 LocalDecl
        // initializer 会把两者都放到 owner store 之前。complete possible-home 相交时，
        // captured binding 可指向该 cell，不能改变 snapshot/后续读取到的 table 值。
        block.stmts[seed_index + 1..end_index].iter().all(|stmt| {
            let stmt_slice = std::slice::from_ref(stmt);
            !self.captures_may_share_seed_home(
                &stmts_reference_captured_bindings(stmt_slice),
                local,
                &seed_homes,
            ) && !self.captures_may_share_seed_home(
                &stmts_value_captured_bindings(stmt_slice),
                local,
                &seed_homes,
            )
        })
    }

    fn stmt_may_carry_seed(
        &self,
        stmt: &HirStmt,
        seed_homes: Option<&BTreeSet<HomeSlotKey>>,
        seed_aliases: &BTreeSet<TableBinding>,
        seed_carriers: &BTreeSet<TableBinding>,
    ) -> bool {
        struct Probe<'pass, 'facts> {
            pass: &'pass TableConstructorPass<'facts>,
            seed_homes: Option<&'pass BTreeSet<HomeSlotKey>>,
            seed_aliases: &'pass BTreeSet<TableBinding>,
            seed_carriers: &'pass BTreeSet<TableBinding>,
            found: bool,
        }

        impl HirVisitor for Probe<'_, '_> {
            fn visit_expr(&mut self, expr: &HirExpr) {
                self.found |= self.pass.expr_may_carry_seed(
                    expr,
                    self.seed_homes,
                    self.seed_aliases,
                    self.seed_carriers,
                );
            }

            fn visit_lvalue(&mut self, lvalue: &HirLValue) {
                let HirLValue::TableAccess(access) = lvalue else {
                    return;
                };
                self.found |= self.pass.expr_may_carry_seed(
                    &access.base,
                    self.seed_homes,
                    self.seed_aliases,
                    self.seed_carriers,
                ) || self.pass.expr_may_carry_seed(
                    &access.key,
                    self.seed_homes,
                    self.seed_aliases,
                    self.seed_carriers,
                );
            }
        }

        let mut probe = Probe {
            pass: self,
            seed_homes,
            seed_aliases,
            seed_carriers,
            found: false,
        };
        crate::hir::simplify::visit::visit_stmts(std::slice::from_ref(stmt), &mut probe);
        probe.found
    }

    fn structured_stmt_seed_carriers(
        &self,
        stmt: &HirStmt,
        seed_owner: TableBinding,
        seed_homes: Option<&BTreeSet<HomeSlotKey>>,
        seed_aliases: &BTreeSet<TableBinding>,
        seed_carriers: &BTreeSet<TableBinding>,
        fresh_tables: &BTreeSet<TableBinding>,
    ) -> Option<BTreeSet<TableBinding>> {
        struct CarrierPropagation<'pass, 'facts> {
            pass: &'pass TableConstructorPass<'facts>,
            seed_homes: Option<&'pass BTreeSet<HomeSlotKey>>,
            seed_aliases: &'pass BTreeSet<TableBinding>,
            seed_carriers: &'pass BTreeSet<TableBinding>,
            discovered: BTreeSet<TableBinding>,
        }

        impl HirVisitor for CarrierPropagation<'_, '_> {
            fn visit_stmt(&mut self, stmt: &HirStmt) {
                let (targets, values) = match stmt {
                    HirStmt::LocalDecl(decl) => (
                        decl.bindings
                            .iter()
                            .copied()
                            .map(TableBinding::Local)
                            .collect::<Vec<_>>(),
                        &decl.values,
                    ),
                    HirStmt::Assign(assign) => (
                        assign
                            .targets
                            .iter()
                            .filter_map(binding_from_lvalue)
                            .collect::<Vec<_>>(),
                        &assign.values,
                    ),
                    _ => return,
                };
                if values.iter().any(|value| {
                    self.pass.expr_may_carry_seed(
                        value,
                        self.seed_homes,
                        self.seed_aliases,
                        self.seed_carriers,
                    )
                }) {
                    self.discovered.extend(targets);
                }
            }
        }

        let mut nested_carriers = seed_carriers.clone();
        loop {
            let mut propagation = CarrierPropagation {
                pass: self,
                seed_homes,
                seed_aliases,
                seed_carriers: &nested_carriers,
                discovered: BTreeSet::new(),
            };
            visit_stmts(std::slice::from_ref(stmt), &mut propagation);
            let before = nested_carriers.len();
            nested_carriers.extend(propagation.discovered);
            if nested_carriers.len() == before {
                break;
            }
        }

        struct HazardProbe<'pass, 'facts> {
            pass: &'pass TableConstructorPass<'facts>,
            seed_homes: Option<&'pass BTreeSet<HomeSlotKey>>,
            seed_aliases: &'pass BTreeSet<TableBinding>,
            seed_carriers: &'pass BTreeSet<TableBinding>,
            fresh_tables: &'pass BTreeSet<TableBinding>,
            seed_owner: TableBinding,
            carrier_tbc: bool,
            unsafe_use: bool,
        }

        impl HirVisitor for HazardProbe<'_, '_> {
            fn visit_stmt(&mut self, stmt: &HirStmt) {
                self.unsafe_use |= match stmt {
                    HirStmt::LocalDecl(decl) => matches!(
                        self.seed_owner,
                        TableBinding::Local(local) if decl.bindings.contains(&local)
                    ),
                    HirStmt::Assign(assign) => assign
                        .targets
                        .iter()
                        .any(|target| binding_from_lvalue(target) == Some(self.seed_owner)),
                    HirStmt::NumericFor(numeric_for) => {
                        self.seed_owner == TableBinding::Local(numeric_for.binding)
                    }
                    HirStmt::GenericFor(generic_for) => matches!(
                        self.seed_owner,
                        TableBinding::Local(local) if generic_for.bindings.contains(&local)
                    ),
                    _ => false,
                };
                match stmt {
                    HirStmt::Assign(assign)
                        if assign.values.iter().any(|value| {
                            self.pass.expr_may_carry_seed(
                                value,
                                self.seed_homes,
                                self.seed_aliases,
                                self.seed_carriers,
                            )
                        }) =>
                    {
                        self.unsafe_use |= assign.targets.iter().any(|target| match target {
                            HirLValue::Local(_) | HirLValue::Temp(_) => false,
                            HirLValue::TableAccess(access) => binding_from_expr(&access.base)
                                .is_none_or(|base| {
                                    !self.seed_aliases.contains(&base)
                                        && !self.fresh_tables.contains(&base)
                                }),
                            HirLValue::Param(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
                                true
                            }
                        });
                    }
                    HirStmt::GlobalDecl(decl) => {
                        self.unsafe_use |= decl.values.iter().any(|value| {
                            self.pass.expr_may_carry_seed(
                                value,
                                self.seed_homes,
                                self.seed_aliases,
                                self.seed_carriers,
                            )
                        });
                    }
                    HirStmt::TableSetList(set_list) => {
                        self.unsafe_use |=
                            set_list.values.iter().any(|value| {
                                self.pass.expr_may_carry_seed(
                                    value,
                                    self.seed_homes,
                                    self.seed_aliases,
                                    self.seed_carriers,
                                )
                            }) && binding_from_expr(&set_list.base).is_none_or(|base| {
                                !self.seed_aliases.contains(&base)
                                    && !self.fresh_tables.contains(&base)
                            });
                    }
                    HirStmt::ToBeClosed(tbc) => {
                        self.carrier_tbc |= self.pass.expr_may_carry_seed(
                            &tbc.value,
                            self.seed_homes,
                            self.seed_aliases,
                            self.seed_carriers,
                        );
                    }
                    HirStmt::Close(_) => self.unsafe_use |= self.carrier_tbc,
                    HirStmt::Goto(_) | HirStmt::Label(_) => self.unsafe_use = true,
                    _ => {}
                }
            }

            fn visit_expr(&mut self, expr: &HirExpr) {
                if self.pass.expr_may_carry_seed(
                    expr,
                    self.seed_homes,
                    self.seed_aliases,
                    self.seed_carriers,
                ) {
                    self.unsafe_use |= !self.pass.expr_is_seed_transport_safe(
                        expr,
                        self.seed_aliases,
                        self.fresh_tables,
                    );
                }
            }
        }

        let mut hazards = HazardProbe {
            pass: self,
            seed_homes,
            seed_aliases,
            seed_carriers: &nested_carriers,
            fresh_tables,
            seed_owner,
            carrier_tbc: false,
            unsafe_use: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut hazards);
        (!hazards.unsafe_use).then_some(nested_carriers)
    }

    fn expr_is_seed_transport_safe(
        &self,
        expr: &HirExpr,
        seed_aliases: &BTreeSet<TableBinding>,
        fresh_tables: &BTreeSet<TableBinding>,
    ) -> bool {
        if expr_is_fixed_set_list_value_safe(expr) {
            return true;
        }
        match expr {
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.expr_is_seed_transport_safe(&logical.lhs, seed_aliases, fresh_tables)
                    && self.expr_is_seed_transport_safe(&logical.rhs, seed_aliases, fresh_tables)
            }
            HirExpr::TableAccess(access) => {
                binding_from_expr(&access.base).is_some_and(|base| {
                    seed_aliases.contains(&base) || fresh_tables.contains(&base)
                }) && self.expr_is_seed_transport_safe(&access.key, seed_aliases, fresh_tables)
            }
            _ => false,
        }
    }

    fn open_set_list_seed_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
        set_list: &crate::hir::common::HirTableSetList,
    ) -> bool {
        let TableBinding::Local(_) = binding else {
            return false;
        };
        let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        if seed_binding != binding || !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_)) {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：已有 open tail 后再追加 open SETLIST 会改变
        // 多返回值占用的数组槽；反例见 regress_52。
        if seed.trailing_multivalue.is_some() {
            return false;
        }
        let next_array_index = u32::try_from(
            seed.fields
                .iter()
                .filter(|field| matches!(field, HirTableField::Array(_)))
                .count(),
        )
        .ok()
        .and_then(|array_len| array_len.checked_add(1));
        // 候选拒绝[SemanticBarrier:TableShape]：raw SETLIST 必须从 seed 的下一个隐式数组键
        // 开始；否则直接追加 constructor array field 会改变实际 key 或覆盖关系。
        if Some(set_list.start_index) != next_array_index {
            return false;
        }
        let Some(tail) = &set_list.values.tail else {
            return false;
        };
        // 候选拒绝[SemanticBarrier:ValueArity]：constructor/AST 只有 open tail；若
        // `f()` 返回三个值，exact width 2 只能取前两个，直接写成 `{ f() }` 会多写一槽。
        if tail.exact_width().is_some() {
            return false;
        }
        // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
        // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。fixed 与
        // open 值仍按原 SETLIST 顺序留在同一个 constructor batch，不需要 data-only 白名单。
        if !expr_is_open_tail_safe(tail.as_expr())
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_open_tail_safe(value))
        {
            return false;
        }
        // 候选拒绝[SemanticBarrier:Scope]：`local t = { ..., t }` 中的 t 属于外层作用域，
        // 不能由后置 SETLIST 的 owner 引用直接搬入 initializer。
        if expr_uses_binding(tail.as_expr(), binding)
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| expr_uses_binding(value, binding))
        {
            return false;
        }
        let rebuilt = constructor_with_set_list(seed, set_list);
        // 候选拒绝[SemanticBarrier:TableShape]：合并前后 SETLIST batch 的 array
        // preallocation/边界可能不同；seed 尾部或 open tail 前的运行时 nil 会让 `#table`
        // 观察到不同边界。复用 completed-constructor shape proof，而不是按表达式种类猜测。
        if !constructor_nil_shape_is_supported(seed, &rebuilt) {
            return false;
        }
        // 候选拒绝[SemanticBarrier:DebugScope]：把后置 SETLIST 收进 LocalDecl initializer
        // 会改变 debug hook 在声明行可观察到的初始化内容。
        if self
            .debug_identity_bindings
            .get(binding)
            .copied()
            .unwrap_or_default()
        {
            return false;
        }
        // The exact source LocalDecl is retained and the SETLIST is adjacent, so the rewritten
        // interval contains no independent owner use, capture, overwrite, or lifetime boundary.
        // Earlier mentions cannot resolve to this lexical definition, and later re-materializations
        // remain after the folded batch. Physical-home provenance cannot affect this local proof.
        true
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
        preserved_stmt_indices: &[usize],
    ) -> bool {
        let TableBinding::Local(_) = binding else {
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
            || binding_from_expr(&set_list.base) != Some(binding)
            || set_list.values.tail.is_none()
            || constructor.trailing_multivalue.is_none()
        {
            return false;
        }
        // Seed fields stay in their original constructor and evaluation order. The region rebuild
        // transaction only appends later fields, so no expression-class whitelist is needed here.
        // 候选拒绝[SemanticBarrier:TableShape]：不确定 nil seed/结果或越界 SETLIST 起点会
        // 改变键集合、覆盖关系或 `#table`；反例见 regress_237、lua54_01_close#10/#11/#15。
        if seed.fields.iter().any(|field| match field {
            HirTableField::Array(value) => !expr_is_definitely_non_nil(value),
            HirTableField::Record(record) => !expr_is_definitely_non_nil(&record.value),
        }) || set_list.start_index == 0
            || set_list.start_index
                > u32::try_from(
                    seed.fields
                        .iter()
                        .filter(|field| matches!(field, HirTableField::Array(_)))
                        .count()
                        .saturating_add(1),
                )
                .unwrap_or(u32::MAX)
            || constructor_has_nil_field(constructor)
            || !array_fields_have_safe_nil_shape(&constructor.fields)
        {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：已有 seed open tail 之后不能再接新 batch。
        if seed.trailing_multivalue.is_some() {
            return false;
        }
        // 候选拒绝[SemanticBarrier:DebugScope]：把区间写入收进 LocalDecl initializer 会改变
        // debug hook 在声明行可观察到的初始化内容。
        if self
            .debug_identity_bindings
            .get(binding)
            .copied()
            .unwrap_or_default()
        {
            return false;
        }
        // owner 的 LocalDecl/LocalId 不会被删除；capture/home 已由独立 commit gate 按完整
        // possible-home 集合证明。下方逐句拒绝 drain 区间内读取 owner 的 producer、key 或
        // value，因此区间后的 reference capture 仍捕获同一个 table owner。
        let tail = set_list.values.tail.as_ref().expect("checked open tail");
        // 候选拒绝[SemanticBarrier:ValueArity]：constructor/AST 只有 open tail；若
        // `f()` 返回三个值，exact width 2 只能取前两个，直接写成 `{ f() }` 会多写一槽。
        if tail.exact_width().is_some() {
            return false;
        }
        // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
        // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。
        if !expr_is_open_tail_safe(tail.as_expr()) {
            return false;
        }
        // 候选拒绝[SemanticBarrier:Scope]：owner 自引用搬进 LocalDecl initializer 会解析到
        // 外层 binding；`local t = {}; t[1] = t` 与 `local t = { t }` 不等价。
        if expr_uses_binding(tail.as_expr(), binding)
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| expr_uses_binding(value, binding))
            || constructor_uses_binding(constructor, binding)
        {
            return false;
        }
        // `try_rebuild_constructor_region` already compared the complete source/generated event
        // sequences, including every fixed SETLIST value and the open tail. The exact LocalDecl is
        // retained; earlier mentions cannot resolve to it, while later materializations remain
        // outside the committed region. Home identity matters only for captures created inside the
        // drained interval, so use the complete may-home set instead of requiring one exact home.
        for (offset, stmt) in block.stmts[seed_index + 1..end_index].iter().enumerate() {
            let stmt_index = seed_index + 1 + offset;
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    assert!(
                        decl.values.tail.is_none(),
                        "successful constructor region must contain only closed producer packs",
                    );
                    // 候选拒绝[SemanticBarrier:Scope]：区间内重新声明 owner binding 会切换
                    // lexical owner，不能继续写回原 seed。
                    if decl
                        .bindings
                        .iter()
                        .any(|candidate| TableBinding::Local(*candidate) == binding)
                    {
                        return false;
                    }
                    if decl.bindings.iter().any(|candidate| {
                        let candidate = TableBinding::Local(*candidate);
                        self.debug_identity_bindings
                            .get(candidate)
                            .copied()
                            .unwrap_or_default()
                    }) {
                        // 候选拒绝[PolicyBoundary]：删除 source-visible producer declaration，
                        // 或把其消费写提前到声明行之前，会改变 debug hook 观察到的 local/table。
                        return false;
                    }
                    let has_reference_capture = decl.bindings.iter().any(|candidate| {
                        self.reference_captured_bindings
                            .get(TableBinding::Local(*candidate))
                            .copied()
                            .unwrap_or_default()
                    });
                    assert!(
                        !has_reference_capture
                            || preserved_stmt_indices.binary_search(&stmt_index).is_ok(),
                        "reference-captured producer source must be preserved by the rebuild plan",
                    );
                    // Eventful snapshots are admitted only after rebuild proves identical source
                    // and generated event sequences. Removed object roots are checked by the
                    // enclosing region lifetime transaction; preserved sources stay in place.
                    // 候选拒绝[SemanticBarrier:Scope]：producer 读取 owner 后搬入 initializer
                    // 会越过 owner 的词法生效点。
                    if decl
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
                        unreachable!(
                            "successful open region must contain only scanner-approved record assignments"
                        )
                    };
                    let [value] = assign.values.fixed.as_slice() else {
                        unreachable!("successful record step must project exactly one fixed value")
                    };
                    assert!(
                        assign.values.tail.is_none()
                            && binding_from_expr(&access.base) == Some(binding),
                        "successful record step must be a closed write to the region owner",
                    );
                    // 候选拒绝[SemanticBarrier:Scope]：key/value 中的 owner 自引用不能搬进
                    // owner 的 LocalDecl initializer。
                    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding)
                    {
                        return false;
                    }
                    // `prepare_record_step` collected key then value source events and the inline
                    // transaction emitted the generated events in exactly that order. Dynamic
                    // calls/lookups are therefore safe here. Independent object roots are owned by
                    // the enclosing removed-producer lifetime checks, not by expression syntax.
                }
                HirStmt::TableSetList(prefix_set_list) => {
                    // scanner/rebuild 已证明每个 SETLIST 的精确起点与 table shape；这里只补
                    // open-owner 特有的词法 owner、value effect 和 open-pack 边界。前置 open
                    // pack 不可能再接末尾 batch，而 owner 自引用不能搬进其 LocalDecl initializer。
                    if binding_from_expr(&prefix_set_list.base) != Some(binding)
                        || prefix_set_list.values.tail.is_some()
                        || prefix_set_list.values.fixed.iter().any(|value| {
                            expr_uses_binding(value, binding)
                                || !expr_is_fixed_set_list_value_safe(value)
                        })
                    {
                        return false;
                    }
                }
                _ => unreachable!(
                    "constructor region scanner only admits local declarations, assignments, and SETLIST"
                ),
            }
        }
        true
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
                (matches!(&record.key, HirTableKey::Name(_))
                    || matches!(&record.key, HirTableKey::Expr(key) if expr_is_open_tail_safe(key)))
                    && expr_is_open_tail_safe(&record.value)
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

fn stmt_contains_close(stmt: &HirStmt) -> bool {
    struct CloseProbe {
        found: bool,
    }

    impl HirVisitor for CloseProbe {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            self.found |= matches!(stmt, HirStmt::Close(_));
        }
    }

    let mut probe = CloseProbe { found: false };
    visit_stmts(std::slice::from_ref(stmt), &mut probe);
    probe.found
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
        | HirStmt::GlobalDecl(_)
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

fn constructor_has_nil_field(constructor: &HirTableConstructor) -> bool {
    constructor.fields.iter().any(table_field_contains_nil)
        || constructor
            .trailing_multivalue
            .as_ref()
            .is_some_and(|tail| expr_contains_nil(tail.as_expr()))
}

fn constructor_has_uncertain_array_field(constructor: &HirTableConstructor) -> bool {
    !array_fields_have_safe_nil_shape(&constructor.fields)
}

fn constructor_has_late_record_overwriting_array(constructor: &HirTableConstructor) -> bool {
    let mut array_fields = 0_i64;
    for field in &constructor.fields {
        match field {
            HirTableField::Array(_) => array_fields += 1,
            HirTableField::Record(record) => {
                let matches_prior_array = match &record.key {
                    HirTableKey::Expr(HirExpr::Integer(index)) => {
                        (1..=array_fields).contains(index)
                    }
                    HirTableKey::Expr(HirExpr::Number(index)) => {
                        index.is_finite()
                            && index.fract() == 0.0
                            && *index >= 1.0
                            && *index <= array_fields as f64
                    }
                    _ => false,
                };
                if matches_prior_array {
                    return true;
                }
            }
        }
    }
    false
}

fn constructor_nil_shape_is_supported(
    seed: &HirTableConstructor,
    rebuilt: &HirTableConstructor,
) -> bool {
    // 候选拒绝[SemanticBarrier:TableShape]：不确定 nil 槽之后再出现确定数组值，
    // 或 open tail 覆盖不确定前缀，会改变键集合/`#table`；反例见
    // lua54_01_close#10/#11/#15 与 regress_237。
    if constructor_has_uncertain_array_field(seed)
        || constructor_has_uncertain_array_field(rebuilt)
        || (rebuilt.trailing_multivalue.is_some()
            && array_fields_contain_uncertain_value(&rebuilt.fields))
    {
        return false;
    }

    // 候选拒绝[SemanticBarrier:EvalOrder]：`t = {}; t[nil] = value` 先保存 fresh owner
    // 再因 nil key 抛错；`t = { [nil] = value }` 则在保存 owner 前抛错。只识别静态必为
    // nil 的 key；例如 `[nil or "key"]` 并不属于这个反例。
    !constructor_adds_definite_nil_record_key(seed, rebuilt)
}

fn constructor_adds_definite_nil_record_key(
    seed: &HirTableConstructor,
    rebuilt: &HirTableConstructor,
) -> bool {
    !constructor_has_definite_nil_record_key(seed)
        && constructor_has_definite_nil_record_key(rebuilt)
}

fn constructor_has_definite_nil_record_key(constructor: &HirTableConstructor) -> bool {
    constructor.fields.iter().any(|field| {
        matches!(
            field,
            HirTableField::Record(record)
                if matches!(&record.key, HirTableKey::Expr(HirExpr::Nil))
        )
    })
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

/// 这里只沿 exact local producer 槽追踪 nil 性；producer 语句保持原位，因此不会继承 generic
/// fold transaction 的表达式 clone 或 root lifetime 风险。
fn local_set_list_values_have_safe_nil_shape(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    set_list_index: usize,
    values: &[HirExpr],
) -> bool {
    let mut definitions = BTreeMap::new();
    for stmt in &block.stmts[seed_index + 1..set_list_index] {
        let HirStmt::LocalDecl(decl) = stmt else {
            continue;
        };
        if decl.values.tail.is_some() || decl.bindings.len() != decl.values.fixed.len() {
            continue;
        }
        for (local, value) in decl.bindings.iter().zip(&decl.values.fixed) {
            if definitions
                .insert(TableBinding::Local(*local), value)
                .is_some()
            {
                return false;
            }
        }
    }

    let mut saw_uncertain = false;
    for value in values {
        let mut resolving = BTreeSet::new();
        if expr_is_definitely_non_nil_from_local_definitions(value, &definitions, &mut resolving) {
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

fn expr_is_definitely_non_nil_from_local_definitions(
    expr: &HirExpr,
    definitions: &BTreeMap<TableBinding, &HirExpr>,
    resolving: &mut BTreeSet<TableBinding>,
) -> bool {
    if expr_is_definitely_non_nil(expr) {
        return true;
    }
    let Some(binding) = binding_from_expr(expr) else {
        return false;
    };
    if !resolving.insert(binding) {
        return false;
    }
    let result = definitions.get(&binding).is_some_and(|definition| {
        expr_is_definitely_non_nil_from_local_definitions(definition, definitions, resolving)
    });
    resolving.remove(&binding);
    result
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::{
        HirBlock, HirCallExpr, HirCallStmt, HirCapture, HirCaptureMode, HirClose, HirClosureExpr,
        HirGlobalRef, HirIf, HirLocalDecl, HirPackTail, HirProtoRef, HirRecordField,
        HirTableSetList, HirToBeClosed,
    };
    use crate::transformer::InstrRef;

    use super::*;

    fn call(name: &str) -> HirExpr {
        HirExpr::Call(Box::new(HirCallExpr {
            callee: HirExpr::GlobalRef(HirGlobalRef { name: name.into() }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_name: None,
        }))
    }

    fn local_table(local: LocalId, constructor: HirTableConstructor) -> HirStmt {
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::new(constructor))]),
        }))
    }

    fn table_pass<'a>(
        block: &HirBlock,
        promotion_facts: &'a ProtoPromotionFacts,
        local_debug_hints: &[Option<String>],
    ) -> TableConstructorPass<'a> {
        let BindingFacts {
            materialized,
            reference_captured,
            reference_captured_home_slots,
        } = collect_binding_facts(block, promotion_facts, 0, local_debug_hints.len());
        TableConstructorPass {
            materialized_bindings: materialized,
            reference_captured_bindings: reference_captured,
            reference_captured_home_slots,
            debug_identity_bindings: BindingSlots::from_debug_hints(&[], local_debug_hints),
            promotion_facts,
            dialect: DecompileDialect::Lua54,
            temp_count: 0,
            next_local_index: local_debug_hints.len(),
            direct_set_list_rebuilds: 0,
        }
    }

    #[test]
    fn nil_values_are_supported_when_the_completed_array_shape_is_stable() {
        let seed = HirTableConstructor::default();
        let rebuilt = HirTableConstructor {
            fields: vec![
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Name("absent".into()),
                    value: HirExpr::Nil,
                }),
                HirTableField::Array(HirExpr::Nil),
            ],
            trailing_multivalue: None,
        };

        assert!(constructor_nil_shape_is_supported(&seed, &rebuilt));
    }

    #[test]
    fn pass_folds_nil_record_value_into_the_seed_constructor() {
        let owner = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(owner)],
                    values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::default())]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::TempRef(owner),
                        key: HirExpr::String("missing".into()),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let BindingFacts {
            materialized,
            reference_captured,
            reference_captured_home_slots,
        } = collect_binding_facts(&block, &promotion_facts, 1, 0);
        let mut pass = TableConstructorPass {
            materialized_bindings: materialized,
            reference_captured_bindings: reference_captured,
            reference_captured_home_slots,
            debug_identity_bindings: BindingSlots::from_debug_hints(&[None], &[]),
            promotion_facts: &promotion_facts,
            dialect: DecompileDialect::Lua54,
            temp_count: 1,
            next_local_index: 0,
            direct_set_list_rebuilds: 0,
        };

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 1);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert_eq!(
            constructor.fields,
            vec![HirTableField::Record(HirRecordField {
                key: HirTableKey::Name("missing".into()),
                value: HirExpr::Nil,
            })]
        );
    }

    #[test]
    fn pass_consumes_every_slot_of_a_closed_short_pack() {
        let owner = TempId(0);
        let record = |key: &str, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                    base: HirExpr::TempRef(owner),
                    key: HirExpr::String(key.into()),
                }))],
                values: HirValuePack::fixed(vec![value]),
            }))
        };
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(owner)],
                    values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::default())]),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0), LocalId(1)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                })),
                record("first", HirExpr::LocalRef(LocalId(0))),
                record("second", HirExpr::LocalRef(LocalId(1))),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let BindingFacts {
            materialized,
            reference_captured,
            reference_captured_home_slots,
        } = collect_binding_facts(&block, &promotion_facts, 1, 2);
        let mut pass = TableConstructorPass {
            materialized_bindings: materialized,
            reference_captured_bindings: reference_captured,
            reference_captured_home_slots,
            debug_identity_bindings: BindingSlots::from_debug_hints(&[None], &[None, None]),
            promotion_facts: &promotion_facts,
            dialect: DecompileDialect::Lua54,
            temp_count: 1,
            next_local_index: 2,
            direct_set_list_rebuilds: 0,
        };

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 1);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert_eq!(
            constructor.fields,
            vec![
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Name("first".into()),
                    value: HirExpr::Integer(7),
                }),
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Name("second".into()),
                    value: HirExpr::Nil,
                }),
            ]
        );
    }

    #[test]
    fn nil_shape_rejects_holes_and_new_definite_nil_keys() {
        let seed = HirTableConstructor::default();
        let array_hole = HirTableConstructor {
            fields: vec![
                HirTableField::Array(HirExpr::Nil),
                HirTableField::Array(HirExpr::Integer(1)),
            ],
            trailing_multivalue: None,
        };
        let nil_key = HirTableConstructor {
            fields: vec![HirTableField::Record(HirRecordField {
                key: HirTableKey::Expr(HirExpr::Nil),
                value: HirExpr::Integer(1),
            })],
            trailing_multivalue: None,
        };

        assert!(!constructor_nil_shape_is_supported(&seed, &array_hole));
        assert!(!constructor_nil_shape_is_supported(&seed, &nil_key));
    }

    #[test]
    fn late_numeric_record_cannot_overwrite_constructor_array_batch() {
        let constructor = HirTableConstructor {
            fields: vec![
                HirTableField::Array(HirExpr::LocalRef(LocalId(0))),
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Expr(HirExpr::Integer(1)),
                    value: HirExpr::Nil,
                }),
            ],
            trailing_multivalue: None,
        };

        assert!(constructor_has_late_record_overwriting_array(&constructor));
    }

    #[test]
    fn exact_width_set_list_tail_remains_unrepresentable() {
        let owner = LocalId(0);
        let block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![owner],
                    values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::default())]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::expanding(
                        Vec::new(),
                        HirPackTail::exact(HirExpr::VarArg, 2),
                    ),
                })),
            ],
        };

        assert!(region_has_exact_width_tail(&block, 0, 1));
    }

    #[test]
    fn source_local_seed_accepts_effectful_record_region() {
        let owner = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(owner),
                        key: HirExpr::String("value".into()),
                    }))],
                    values: HirValuePack::fixed(vec![call("make_value")]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None]);

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 1);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [HirTableField::Record(HirRecordField {
                key: HirTableKey::Name(key),
                value: HirExpr::Call(_),
            })] if key == "value"
        ));
    }

    #[test]
    fn direct_temp_set_list_accepts_numeric_record_under_compaction_and_reuse() {
        let owner = TempId(0);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(owner)],
                    values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::new(
                        HirTableConstructor {
                            fields: vec![HirTableField::Record(HirRecordField {
                                key: HirTableKey::Expr(HirExpr::Integer(1)),
                                value: HirExpr::Integer(10),
                            })],
                            trailing_multivalue: None,
                        },
                    ))]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::TempRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Nil, HirExpr::Integer(20)]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(owner)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(30)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_temp_home_slot_for_test(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_direct_table_seed_for_test(owner);
        promotion_facts.enable_home_slot_compaction();
        let BindingFacts {
            materialized,
            reference_captured,
            reference_captured_home_slots,
        } = collect_binding_facts(&block, &promotion_facts, 1, 0);
        let mut pass = TableConstructorPass {
            materialized_bindings: materialized,
            reference_captured_bindings: reference_captured,
            reference_captured_home_slots,
            debug_identity_bindings: BindingSlots::from_debug_hints(&[None], &[]),
            promotion_facts: &promotion_facts,
            dialect: DecompileDialect::Lua54,
            temp_count: 1,
            next_local_index: 0,
            direct_set_list_rebuilds: 0,
        };
        assert!(promotion_facts.compacts_home_slots());
        assert_eq!(
            pass.materialized_bindings
                .get(TableBinding::Temp(owner))
                .copied(),
            Some(2)
        );

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(pass.direct_set_list_rebuilds, 1);
        assert_eq!(block.stmts.len(), 2);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Expr(HirExpr::Integer(1)),
                    value: HirExpr::Integer(10),
                }),
                HirTableField::Array(HirExpr::Nil),
                HirTableField::Array(HirExpr::Integer(20)),
            ]
        ));
        assert!(matches!(
            block.stmts[1],
            HirStmt::Assign(ref assign)
                if matches!(assign.values.fixed.as_slice(), [HirExpr::Integer(30)])
        ));
    }

    #[test]
    fn open_local_fallback_accepts_self_reference_without_trusted_home() {
        let owner = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_table(
                    owner,
                    HirTableConstructor {
                        fields: vec![
                            HirTableField::Array(HirExpr::Integer(10)),
                            HirTableField::Record(HirRecordField {
                                key: HirTableKey::Name("self".into()),
                                value: HirExpr::LocalRef(owner),
                            }),
                        ],
                        trailing_multivalue: None,
                    },
                ),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 2,
                    values: HirValuePack::expanding(
                        vec![HirExpr::TableConstructor(Box::new(HirTableConstructor {
                            fields: vec![HirTableField::Array(call("fixed_value"))],
                            trailing_multivalue: None,
                        }))],
                        HirPackTail::open(call("open_tail")),
                    ),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(owner)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(30)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts
            .record_local_home_merge(owner, Some(BTreeSet::from([HomeSlotKey::new(1, 0)])));
        promotion_facts.enable_home_slot_compaction();
        let mut pass = table_pass(&block, &promotion_facts, &[None]);
        assert!(!promotion_facts.is_direct_table_seed_local(owner));
        assert_eq!(promotion_facts.trusted_local_home_slot(owner), None);
        assert_eq!(
            pass.materialized_bindings
                .get(TableBinding::Local(owner))
                .copied(),
            Some(2)
        );

        assert!(pass.materialize_safe_fixed_set_lists(&mut block));
        assert_eq!(block.stmts.len(), 2);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [
                HirTableField::Array(HirExpr::Integer(10)),
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Name(name),
                    value: HirExpr::LocalRef(local),
                }),
                HirTableField::Array(HirExpr::TableConstructor(_)),
            ] if name == "self" && *local == owner
        ));
        assert!(
            constructor
                .trailing_multivalue
                .as_ref()
                .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
        );
        assert!(matches!(block.stmts[1], HirStmt::Assign(_)));
    }

    #[test]
    fn open_region_rebuild_uses_event_and_interval_facts_under_compaction() {
        let owner = LocalId(0);
        let producer = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(
                    owner,
                    HirTableConstructor {
                        fields: vec![HirTableField::Array(HirExpr::Integer(10))],
                        trailing_multivalue: None,
                    },
                ),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![producer],
                    values: HirValuePack::fixed(vec![HirExpr::TableConstructor(Box::new(
                        HirTableConstructor {
                            fields: vec![HirTableField::Array(HirExpr::Integer(20))],
                            trailing_multivalue: None,
                        },
                    ))]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 2,
                    values: HirValuePack::expanding(
                        vec![
                            HirExpr::LocalRef(producer),
                            HirExpr::TableConstructor(Box::new(HirTableConstructor {
                                fields: vec![HirTableField::Array(call("fixed_value"))],
                                trailing_multivalue: None,
                            })),
                        ],
                        HirPackTail::open(call("open_tail")),
                    ),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(producer, HomeSlotKey::new(1, 0));
        promotion_facts.enable_home_slot_compaction();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 1);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [
                HirTableField::Array(HirExpr::Integer(10)),
                HirTableField::Array(HirExpr::TableConstructor(_)),
                HirTableField::Array(HirExpr::TableConstructor(_)),
            ]
        ));
        assert!(
            constructor
                .trailing_multivalue
                .as_ref()
                .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
        );
    }

    #[test]
    fn open_region_uses_complete_owner_homes_for_capture_aliases() {
        fn rewrite_with_capture(capture_mode: HirCaptureMode, capture_home: HomeSlotKey) -> bool {
            let owner = LocalId(0);
            let captured_alias = LocalId(1);
            let closure = LocalId(2);
            let mut block = HirBlock {
                stmts: vec![
                    local_table(owner, HirTableConstructor::default()),
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![closure],
                        values: HirValuePack::fixed(vec![HirExpr::Closure(Box::new(
                            HirClosureExpr {
                                proto: HirProtoRef(1),
                                captures: vec![HirCapture {
                                    mode: capture_mode,
                                    value: HirExpr::LocalRef(captured_alias),
                                }],
                            },
                        ))]),
                    })),
                    HirStmt::TableSetList(Box::new(HirTableSetList {
                        base: HirExpr::LocalRef(owner),
                        start_index: 1,
                        values: HirValuePack::expanding(
                            vec![HirExpr::LocalRef(closure)],
                            HirPackTail::open(call("open_tail")),
                        ),
                    })),
                ],
            };
            let first_owner_home = HomeSlotKey::new(0, 0);
            let merged_owner_home = HomeSlotKey::new(1, 0);
            let mut promotion_facts = ProtoPromotionFacts::default();
            promotion_facts.record_local_home_slot(owner, first_owner_home);
            promotion_facts
                .record_local_home_merge(owner, Some(BTreeSet::from([merged_owner_home])));
            promotion_facts.record_local_home_slot(captured_alias, capture_home);
            promotion_facts.record_local_home_slot(closure, HomeSlotKey::new(3, 0));
            assert_eq!(promotion_facts.trusted_local_home_slot(owner), None);
            let mut pass = table_pass(&block, &promotion_facts, &[None, None, None]);

            let changed = pass.rewrite_block(&mut block);
            assert_eq!(
                block
                    .stmts
                    .iter()
                    .any(|stmt| matches!(stmt, HirStmt::TableSetList(_))),
                !changed
            );
            changed
        }

        for capture_mode in [HirCaptureMode::ByReference, HirCaptureMode::ByValue] {
            assert!(rewrite_with_capture(capture_mode, HomeSlotKey::new(2, 0)));
            assert!(!rewrite_with_capture(capture_mode, HomeSlotKey::new(1, 0)));
        }
    }

    #[test]
    fn open_region_accepts_complex_dynamic_record_events() {
        let owner = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(owner),
                        key: call("make_key"),
                    }))],
                    values: HirValuePack::fixed(vec![call("make_value")]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::expanding(
                        vec![HirExpr::TableConstructor(Box::new(HirTableConstructor {
                            fields: vec![HirTableField::Array(HirExpr::Integer(10))],
                            trailing_multivalue: None,
                        }))],
                        HirPackTail::open(call("open_tail")),
                    ),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None]);

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 1);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Expr(HirExpr::Call(_)),
                    value: HirExpr::Call(_),
                }),
                HirTableField::Array(HirExpr::TableConstructor(_)),
            ]
        ));
        assert!(constructor.trailing_multivalue.is_some());
    }

    #[test]
    fn open_region_preserves_reference_captured_producer_source() {
        let owner = LocalId(0);
        let producer = LocalId(1);
        let closure = LocalId(2);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![producer],
                    values: HirValuePack::fixed(vec![HirExpr::String("key".into())]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(owner),
                        key: HirExpr::LocalRef(producer),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::expanding(
                        vec![HirExpr::TableConstructor(Box::default())],
                        HirPackTail::open(call("open_tail")),
                    ),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![closure],
                    values: HirValuePack::fixed(vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: HirProtoRef(1),
                        captures: vec![HirCapture {
                            mode: HirCaptureMode::ByReference,
                            value: HirExpr::LocalRef(producer),
                        }],
                    }))]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(producer, HomeSlotKey::new(1, 0));
        promotion_facts.record_local_home_slot(closure, HomeSlotKey::new(2, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None, None]);

        assert!(
            pass.reference_captured_bindings
                .get(TableBinding::Local(producer))
                .copied()
                .unwrap_or_default()
        );
        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 3);
        let (_, constructor) = constructor_seed(&block.stmts[0]).expect("rewritten seed");
        assert!(matches!(
            constructor.fields.as_slice(),
            [
                HirTableField::Record(HirRecordField {
                    key: HirTableKey::Name(name),
                    value: HirExpr::Integer(7),
                }),
                HirTableField::Array(HirExpr::TableConstructor(_)),
            ] if name == "key"
        ));
        assert!(constructor.trailing_multivalue.is_some());
        assert!(matches!(
            block.stmts[1],
            HirStmt::LocalDecl(ref decl) if decl.bindings == [producer]
        ));
        assert!(matches!(
            block.stmts[2],
            HirStmt::LocalDecl(ref decl) if decl.bindings == [closure]
        ));
    }

    #[test]
    fn open_region_keeps_parallel_open_assignment_outside_scanner_grammar() {
        let owner = LocalId(0);
        let side = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![
                        HirLValue::TableAccess(Box::new(HirTableAccess {
                            base: HirExpr::LocalRef(owner),
                            key: HirExpr::String("value".into()),
                        })),
                        HirLValue::Local(side),
                    ],
                    values: HirValuePack::expanding(
                        vec![HirExpr::Integer(1)],
                        HirPackTail::open(call("parallel_tail")),
                    ),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::expanding(
                        vec![HirExpr::TableConstructor(Box::default())],
                        HirPackTail::open(call("open_tail")),
                    ),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(side, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[1], HirStmt::Assign(ref assign) if assign.targets.len() == 2));
        assert!(matches!(block.stmts[2], HirStmt::TableSetList(_)));
    }

    #[test]
    fn dynamic_record_key_keeps_removed_object_root_before_later_batch() {
        let owner = LocalId(0);
        let producer = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                local_table(
                    producer,
                    HirTableConstructor {
                        fields: vec![HirTableField::Array(HirExpr::Integer(20))],
                        trailing_multivalue: None,
                    },
                ),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(owner),
                        key: call("dynamic_key"),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(producer)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::expanding(
                        vec![HirExpr::TableConstructor(Box::default())],
                        HirPackTail::open(call("observe_lifetime")),
                    ),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(producer, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(region_has_followup_table_write_after_object_producer(
            &block,
            0,
            3,
            TableBinding::Local(owner),
            &[],
        ));
        assert!(!pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 4);
        assert!(matches!(block.stmts[3], HirStmt::TableSetList(_)));
    }

    #[test]
    fn indexed_fallback_keeps_unrepresentable_open_seed_tail_raw() {
        let owner = LocalId(0);
        let prefix = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(
                    owner,
                    HirTableConstructor {
                        fields: Vec::new(),
                        trailing_multivalue: Some(HirPackTail::open(HirExpr::VarArg)),
                    },
                ),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![prefix],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(prefix, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.materialize_safe_fixed_set_lists(&mut block));
        assert!(matches!(block.stmts[2], HirStmt::TableSetList(_)));
    }

    #[test]
    fn fixed_set_list_accepts_effectful_prefix_on_disjoint_complete_homes() {
        let owner = LocalId(0);
        let nested = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                local_table(
                    nested,
                    HirTableConstructor {
                        fields: vec![HirTableField::Array(call("make_nested_value"))],
                        trailing_multivalue: None,
                    },
                ),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(nested),
                        key: call("make_key"),
                    }))],
                    values: HirValuePack::fixed(vec![call("make_value")]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10), HirExpr::Integer(20)]),
                })),
            ],
        };
        let owner_home = HomeSlotKey::new(0, 0);
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, owner_home);
        promotion_facts.record_local_home_slot(nested, HomeSlotKey::new(1, 0));
        promotion_facts
            .record_local_home_merge(nested, Some(BTreeSet::from([HomeSlotKey::new(2, 0)])));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 4);
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
        assert!(matches!(
            &block.stmts[1],
            HirStmt::LocalDecl(decl)
                if matches!(decl.values.fixed.as_slice(), [HirExpr::TableConstructor(constructor)]
                    if matches!(constructor.fields.as_slice(), [
                        HirTableField::Array(HirExpr::Call(_)),
                        HirTableField::Record(HirRecordField {
                            key: HirTableKey::Expr(HirExpr::Call(_)),
                            value: HirExpr::Call(_),
                        }),
                    ]))
        ));
    }

    #[test]
    fn debug_visible_seed_rejects_effectful_prefix_before_fixed_set_list() {
        let owner = LocalId(0);
        let producer = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![producer],
                    values: HirValuePack::fixed(vec![call("inspect_owner")]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(producer, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[Some("owner".into()), None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[2], HirStmt::TableSetList(_)));
    }

    #[test]
    fn debug_visible_seed_accepts_its_own_effectful_initializer() {
        let owner = LocalId(0);
        let inert_prefix = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(
                    owner,
                    HirTableConstructor {
                        fields: vec![HirTableField::Array(call("make_initial_value"))],
                        trailing_multivalue: None,
                    },
                ),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![inert_prefix],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(inert_prefix, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[Some("owner".into()), None]);

        assert!(pass.materialize_safe_fixed_set_lists(&mut block));
        assert!(matches!(block.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn possible_home_alias_snapshot_allows_fixed_set_list_rewrite() {
        let owner = LocalId(0);
        let merged_alias = LocalId(1);
        let snapshot = LocalId(2);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![snapshot],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(merged_alias)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let owner_home = HomeSlotKey::new(0, 0);
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, owner_home);
        promotion_facts.record_local_home_slot(merged_alias, HomeSlotKey::new(1, 0));
        promotion_facts.record_local_home_merge(merged_alias, Some(BTreeSet::from([owner_home])));
        promotion_facts.record_local_home_slot(snapshot, HomeSlotKey::new(2, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
    }

    #[test]
    fn missing_home_provenance_allows_seed_disjoint_fixed_prefix() {
        let owner = LocalId(0);
        let scratch = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![scratch],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
    }

    #[test]
    fn seed_disjoint_structured_prefix_allows_fixed_set_list_rewrite() {
        let owner = LocalId(0);
        let scratch = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
                            bindings: vec![scratch],
                            values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                        }))],
                    },
                    else_block: None,
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
    }

    #[test]
    fn structured_prefix_may_read_seed_without_publishing_it() {
        let owner = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::LocalRef(owner),
                    then_block: HirBlock::default(),
                    else_block: None,
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None]);

        assert!(pass.rewrite_block(&mut block));
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
    }

    #[test]
    fn structured_prefix_owner_overwrite_keeps_raw_set_list() {
        let owner = LocalId(0);
        let replacement = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(owner)],
                            values: HirValuePack::fixed(vec![HirExpr::LocalRef(replacement)]),
                        }))],
                    },
                    else_block: None,
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[2], HirStmt::TableSetList(_)));
    }

    #[test]
    fn structured_alias_reaching_later_call_keeps_raw_set_list_without_homes() {
        let owner = LocalId(0);
        let alias = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![alias],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(alias)],
                            values: HirValuePack::fixed(vec![HirExpr::LocalRef(owner)]),
                        }))],
                    },
                    else_block: None,
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "install_metatable".into(),
                        }),
                        args: HirValuePack::fixed(vec![HirExpr::LocalRef(alias)]),
                        method: false,
                        fastcall: None,
                        method_name: None,
                    },
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[4], HirStmt::TableSetList(_)));
    }

    #[test]
    fn seed_bearing_tbc_without_prefix_close_allows_fixed_set_list_rewrite() {
        let owner = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                    origin: InstrRef(0),
                    reg_index: 0,
                    value: HirExpr::LocalRef(owner),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None]);

        assert!(pass.rewrite_block(&mut block));
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
    }

    #[test]
    fn fixed_set_list_prefix_accepts_seed_disjoint_preserved_statements() {
        let owner = LocalId(0);
        let left = LocalId(1);
        let right = LocalId(2);
        let resource = LocalId(3);
        let external_base = HirExpr::TableAccess(Box::new(HirTableAccess {
            base: HirExpr::GlobalRef(HirGlobalRef {
                name: "registry".into(),
            }),
            key: HirExpr::String("target".into()),
        }));
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![left],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![right],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![resource],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(left), HirLValue::Local(right)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::Integer(2)]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: external_base,
                        key: HirExpr::String("value".into()),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(3)]),
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: match call("tick") {
                        HirExpr::Call(call) => *call,
                        _ => unreachable!("call helper returns a call"),
                    },
                })),
                HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                    origin: InstrRef(0),
                    reg_index: 3,
                    value: HirExpr::LocalRef(resource),
                })),
                HirStmt::Close(Box::new(HirClose { from_reg: 3 })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        for (local, slot) in [(owner, 0), (left, 1), (right, 2), (resource, 3)] {
            promotion_facts.record_local_home_slot(local, HomeSlotKey::new(slot, 0));
        }
        let mut pass = table_pass(&block, &promotion_facts, &[None, None, None, None]);

        assert!(pass.rewrite_block(&mut block));
        assert_eq!(block.stmts.len(), 10);
        assert!(
            !block
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::TableSetList(_)))
        );
        assert!(matches!(block.stmts[4], HirStmt::Assign(ref assign) if assign.targets.len() == 2));
        assert!(matches!(block.stmts[6], HirStmt::CallStmt(_)));
        assert!(matches!(block.stmts[8], HirStmt::Close(_)));
    }

    #[test]
    fn escaped_seed_keeps_raw_set_list_before_metamethod_capable_call() {
        let owner = LocalId(0);
        let alias = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![alias],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(owner)]),
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "install_metatable".into(),
                        }),
                        args: HirValuePack::fixed(vec![HirExpr::LocalRef(alias)]),
                        method: false,
                        fastcall: None,
                        method_name: None,
                    },
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                })),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(owner, HomeSlotKey::new(0, 0));
        promotion_facts.record_local_home_slot(alias, HomeSlotKey::new(1, 0));
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[3], HirStmt::TableSetList(_)));
    }

    #[test]
    fn seed_alias_as_external_table_key_keeps_raw_set_list() {
        let owner = LocalId(0);
        let alias = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![alias],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(owner)]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::GlobalRef(HirGlobalRef {
                            name: "registry".into(),
                        }),
                        key: HirExpr::LocalRef(alias),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[3], HirStmt::TableSetList(_)));
    }

    #[test]
    fn seed_alias_in_fresh_table_key_call_keeps_raw_set_list() {
        let owner = LocalId(0);
        let alias = LocalId(1);
        let mut block = HirBlock {
            stmts: vec![
                local_table(owner, HirTableConstructor::default()),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![alias],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(owner)]),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                        base: HirExpr::LocalRef(owner),
                        key: HirExpr::Call(Box::new(HirCallExpr {
                            callee: HirExpr::GlobalRef(HirGlobalRef {
                                name: "install_and_key".into(),
                            }),
                            args: HirValuePack::fixed(vec![HirExpr::LocalRef(alias)]),
                            method: false,
                            fastcall: None,
                            method_name: None,
                        })),
                    }))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(owner),
                    start_index: 1,
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                })),
            ],
        };
        let promotion_facts = ProtoPromotionFacts::default();
        let mut pass = table_pass(&block, &promotion_facts, &[None, None]);

        assert!(!pass.rewrite_block(&mut block));
        assert!(matches!(block.stmts[3], HirStmt::TableSetList(_)));
    }
}
