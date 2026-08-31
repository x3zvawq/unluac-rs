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

#[derive(Debug, Clone, Copy)]
enum RegionStep {
    Producer {
        stmt_index: usize,
        slot_index: usize,
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
}

#[derive(Debug, Clone)]
enum PendingProducerSource {
    Value {
        stmt_index: usize,
        value_index: usize,
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
                    // 候选拒绝[SemanticBarrier:TableShape]：不确定 nil 槽之后再出现确定数组值，
                    // 或 open tail 覆盖不确定前缀，会改变键集合/`#table`；反例见
                    // lua54_01_close#10/#11/#15 与 regress_237。
                    let invalid_array_shape = constructor_has_uncertain_array_field(&seed_ctor)
                        || constructor_has_uncertain_array_field(rebuilt_constructor)
                        || (rebuilt_constructor.trailing_multivalue.is_some()
                            && array_fields_contain_uncertain_value(&rebuilt_constructor.fields));
                    // 候选拒绝[ProofIncomplete]：当前对任意嵌套/direct nil 与 exact-width tail
                    // 整体停用；其中存在等价形状，应按实际 array slot 与 pack width 建模。
                    let unsupported_nil_or_width = constructor_has_nil_field(&seed_ctor)
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
                    // 候选拒绝[SemanticBarrier:Lifetime]：反例见
                    // tests/unit-case/lua54_01_close.lua#lua54_01_close#13/#14/#16。
                    let producer_root_is_observable =
                        region_has_non_drop_safe_producer(block, index, *end_index)
                            && !open_local_owner
                            && collect_range_binding_mentions(
                                block,
                                *end_index + 1,
                                block.stmts.len(),
                            )
                            .contains(&binding);
                    // 候选拒绝[SemanticBarrier:Lifetime]：对象 producer 后再覆盖 table field
                    // 时，删除 producer 会提前释放最后一个强引用；反例同上。
                    let has_followup_object_write =
                        region_has_followup_table_write_after_object_producer(
                            block, index, *end_index, binding,
                        );
                    // The constructor RHS is evaluated before an ordinary assignment stores
                    // its result.  Keep the explicit seed whenever the region does not prove
                    // that the original seed overwrite already precedes every observable RHS;
                    // direct NewTable provenance alone is not such proof.
                    // 候选拒绝[ProofIncomplete]：当前 `seed_overwrite_delay_is_unobservable`
                    // 是表达式白名单；其中确有覆盖延后反例（lua54_01_close#8），但 false
                    // 也包含保持顺序的安全子集，应改为精确 overwrite/eval-event 证明。
                    let overwrite_timing_is_safe = open_local_owner
                        || seed_overwrite_delay_is_unobservable(block, index, *end_index, binding);
                    !invalid_array_shape
                        && !unsupported_nil_or_width
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
            // but only for data-only, definitely non-nil fixed values and a hole-free seed.
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
            // 候选拒绝[ProofIncomplete]：当前没有后续 owner 能消费剩余 TableSetList；保留
            // residual 只暴露缺口，不构成等价性证明，必须继续逐 guard 收敛。
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
        // 候选拒绝[LayerBoundary]：direct seed/trusted home provenance 应由 promotion 提供；
        // 事实缺失时本 pass 不从局部语法重新猜测 owner。
        if self
            .promotion_facts
            .trusted_local_home_slot(local)
            .is_none()
            || !self.promotion_facts.is_direct_table_seed_local(local)
        {
            return None;
        }
        if set_list.values.fixed.is_empty() && set_list.values.tail.is_none() {
            return None;
        }
        if let Some(tail) = &set_list.values.tail {
            // 候选拒绝[ProofIncomplete]：exact-width tail 还没有到 constructor multivalue 的
            // 精确表示映射；不能把 carrier 缺失描述成不等价证明。
            if tail.exact_width().is_some() {
                return None;
            }
            // 候选拒绝[LayerBoundary]：Decision/Unresolved 必须先由 decision/eliminate owner
            // 收敛，table pass 不把未完成控制节点塞进普通 constructor 表达式。
            if !expr_is_open_tail_safe(tail.as_expr()) {
                return None;
            }
        }
        // 候选拒绝[LayerBoundary]：fixed 值中的 Decision/Unresolved 尚未由其 owner 消费。
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
        // 候选拒绝[ProofIncomplete]：numeric record 与后续 array key 的别名关系尚未复用
        // builder 精确分析，当前 direct path 整体停用。
        if constructor_has_numeric_record(seed) {
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
        // 候选拒绝[ProofIncomplete]：seed/fixed 值的 data-only 与 definitely-non-nil 要求宽于
        // 实际等价条件；相邻 direct encoding 保持 allocation 和求值点，应继续扩展事件证明。
        if !constructor_is_data_only(seed)
            || set_list
                .values
                .fixed
                .iter()
                .any(|value| !expr_is_definitely_non_nil(value) || !expr_is_data_only(value))
        {
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
        // 候选拒绝[ProofIncomplete]：capture 是 proto 全局事实；相邻 batch 保持 LocalDecl/
        // seed 时点，不能假设任意后续 capture 都受影响，应改为区间化 provenance。
        if self
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
            TableBinding::Temp(temp) => {
                // 候选拒绝[ProofIncomplete]：home compaction/多次 materialization 当前整体
                // 拒绝，尚未按该 seed 的精确 def-use 与 root lifetime 区分安全子集。
                if self.promotion_facts.compacts_home_slots()
                    || self.materialized_bindings.get(binding).copied() != Some(1)
                {
                    return None;
                }
                // 候选拒绝[LayerBoundary]：direct seed 与 trusted home 由 promotion owner 提供。
                (self.promotion_facts.is_direct_table_seed_temp(temp)
                    && self.promotion_facts.trusted_temp_home_slot(temp).is_some())
                .then_some(seed_index)
            }
            TableBinding::Local(local) => {
                if !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_)) {
                    return None;
                }
                // 候选拒绝[ProofIncomplete]：同上，compaction/多 materialization 需要区间化证明。
                if self.promotion_facts.compacts_home_slots()
                    || self.materialized_bindings.get(binding).copied() != Some(1)
                {
                    return None;
                }
                // 候选拒绝[LayerBoundary]：direct seed 与 trusted home 由 promotion owner 提供。
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
            // 候选拒绝[ProofIncomplete]：该路径只替换 SETLIST、并不移动 seed；已有 open
            // tail 当前仍整项停用，缺少的是对后续批量写入的 array-shape 证明。
            if seed.trailing_multivalue.is_some() {
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
        // 候选拒绝[LayerBoundary]：seed home provenance 由 promotion owner 提供。
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
            // 候选拒绝[ProofIncomplete]：capture/home-slot 的全局相交只是别名可能性；应证明
            // 该 capture 是否在 SETLIST 区间可观察 owner，而不是整段停用。
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
                        // 候选拒绝[ProofIncomplete]：debug identity 尚未按具体可观察点建模；
                        // 前缀语句保持原位，复杂形状本身不是不等价反例。
                        return false;
                    }
                    if decl.bindings.contains(&seed_local) && stmt_index != seed_index {
                        // A second declaration of the seed binding would create a new lexical
                        // owner, so the indexed-write proof must stop at that boundary.
                        // 候选拒绝[SemanticBarrier:Scope]：同 binding 的第二个 LocalDecl 已切换
                        // lexical owner，后续 SETLIST 不能归属于旧 seed。
                        return false;
                    }
                    if decl
                        .values
                        .iter()
                        .any(|value| expr_uses_binding(value, binding))
                    {
                        // 候选拒绝[ProofIncomplete]：前缀读取 owner 可能形成 alias/escape，但
                        // 当前未区分仅快照读取与真正使后续 indexed writes 可观察的逃逸。
                        return false;
                    }
                    for local in &decl.bindings {
                        if *local == seed_local {
                            continue;
                        }
                        let Some(candidate_home) =
                            self.promotion_facts.trusted_local_home_slot(*local)
                        else {
                            // 候选拒绝[LayerBoundary]：candidate home 由 promotion owner 提供。
                            return false;
                        };
                        if candidate_home == seed_home {
                            // 候选拒绝[SemanticBarrier:Lifetime]：区间内复用 seed 的物理 home
                            // 会覆盖 owner；不能再把 SETLIST 证明为对原 fresh table 的写入。
                            return false;
                        }
                    }
                    if let Some((candidate, constructor)) = constructor_seed(stmt) {
                        if !matches!(candidate, TableBinding::Local(_))
                            || !constructor_is_data_only(constructor)
                            || constructor_uses_binding(constructor, candidate)
                            || constructor_uses_binding(constructor, binding)
                        {
                            // 候选拒绝[ProofIncomplete]：嵌套 constructor 当前仅接受 data-only
                            // fresh seed；需要独立的 escape/effect 事实后再放宽。
                            return false;
                        }
                        fresh_tables.insert(candidate);
                    }
                }
                HirStmt::ToBeClosed(_)
                | HirStmt::Close(_)
                | HirStmt::Goto(_)
                | HirStmt::Label(_) => {
                    // 候选拒绝[ProofIncomplete]：控制/关闭语句保持原位，但当前前缀证明没有
                    // 路径与资源状态，无法证明末尾 SETLIST 仍由同一 owner 支配。
                    return false;
                }
                HirStmt::Assign(assign) => {
                    if debug_seed && !debug_prefix_stmt_is_inert(stmt) {
                        // 候选拒绝[ProofIncomplete]：同上，缺少 debug 可观察点的区间证明。
                        return false;
                    }
                    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                        // 候选拒绝[ProofIncomplete]：前缀证明只建模单 table write，其他保持
                        // 原位的 assignment 尚未通过 effect/escape summary 判定。
                        return false;
                    };
                    let [value] = assign.values.fixed.as_slice() else {
                        // 候选拒绝[ProofIncomplete]：parallel/open assignment 尚无区间 effect
                        // summary，不能仅凭语法证明 owner 未逃逸。
                        return false;
                    };
                    if assign.values.tail.is_some()
                        || expr_uses_binding(&access.key, binding)
                        || expr_uses_binding(value, binding)
                        || !expr_is_prefix_read_only(&access.key)
                        || !expr_is_prefix_read_only(value)
                    {
                        // 候选拒绝[ProofIncomplete]：key/value 的只读白名单过窄；需要证明的是
                        // 是否改变或泄露 seed，而非表达式是否 data-only。
                        return false;
                    }
                    let Some(base) = binding_from_expr(&access.base) else {
                        // 候选拒绝[ProofIncomplete]：复合 base 尚无 fresh-table alias 事实。
                        return false;
                    };
                    if base != binding && !fresh_tables.contains(&base) {
                        // 候选拒绝[ProofIncomplete]：外部 base 可能触发 metamethod，但该写入
                        // 保持原位；仍需 effect summary 证明它不改变/泄露 seed。
                        return false;
                    }
                }
                _ => {
                    // 候选拒绝[ProofIncomplete]：未建模前缀语句缺少 owner escape/effect 摘要。
                    return false;
                }
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
        if seed_binding != binding || !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_)) {
            return false;
        }
        // 候选拒绝[ProofIncomplete]：该 fallback 只支持空 seed；非空连续 seed 已有安全子集，
        // 应与 adjacent path 共用精确 overlap 证明。
        if !seed.fields.is_empty() {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：已有 open tail 后再追加 open SETLIST 会改变
        // 多返回值占用的数组槽；反例见 regress_52。
        if seed.trailing_multivalue.is_some() {
            return false;
        }
        // 候选拒绝[SemanticBarrier:TableShape]：空 seed 的 open batch 只能从数组键 1 开始。
        if set_list.start_index != 1 {
            return false;
        }
        let Some(tail) = &set_list.values.tail else {
            return false;
        };
        // 候选拒绝[ProofIncomplete]：exact-width carrier 尚未精确映射到 constructor tail。
        if tail.exact_width().is_some() {
            return false;
        }
        // 候选拒绝[LayerBoundary]：Decision/Unresolved 由各自 owner 先收敛。
        if !expr_is_open_tail_safe(tail.as_expr()) {
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
        // 候选拒绝[ProofIncomplete]：fixed 前缀的 data-only/definitely-non-nil 白名单宽于
        // 实际等价条件；应按事件顺序和 array slot 精确证明。
        if !set_list
            .values
            .fixed
            .iter()
            .all(|value| expr_is_data_only(value) && expr_is_definitely_non_nil(value))
        {
            return false;
        }
        // 候选拒绝[ProofIncomplete]：debug/capture 全局事实尚未按该相邻区间证明可观察性。
        if self
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
        // A branch-local LocalDecl may originate from a coalesced fixed temp rather than retain
        // the direct-SSA marker. The declaration is fresh only when no earlier statement mentions
        // this LocalId; eventually this should consume precise promotion provenance.
        // 候选拒绝[ProofIncomplete]：prefix mention、home compaction 与多 materialization 仍是
        // 全局近似，需改成 seed 区间的 def-use/lifetime 证明。
        if self.binding_is_shared_before_seed(block, seed_index, binding)
            || self.promotion_facts.compacts_home_slots()
            || self.materialized_bindings.get(binding).copied() != Some(1)
        {
            return false;
        }
        // 候选拒绝[LayerBoundary]：trusted home 由 promotion owner 提供。
        self.promotion_facts
            .trusted_local_home_slot(local)
            .is_some()
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
            || binding_from_expr(&set_list.base) != Some(binding)
            || set_list.values.tail.is_none()
            || constructor.trailing_multivalue.is_none()
        {
            return false;
        }
        // 候选拒绝[ProofIncomplete]：seed 字段表达式白名单尚未复用 rebuild 的事件证明。
        if seed.fields.iter().any(|field| match field {
            HirTableField::Array(value) => !expr_is_fixed_set_list_value_safe(value),
            HirTableField::Record(record) => {
                !record_key_is_data_only(&record.key)
                    || !expr_is_fixed_set_list_value_safe(&record.value)
            }
        }) {
            return false;
        }
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
        // 候选拒绝[ProofIncomplete]：debug/capture 仍是 proto 级 blanket gate，尚未证明该
        // open-owner 区间是否改变可观察身份。
        if self
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
        let tail = set_list.values.tail.as_ref().expect("checked open tail");
        // 候选拒绝[ProofIncomplete]：exact-width carrier 尚无 constructor-tail 精确表示。
        if tail.exact_width().is_some() {
            return false;
        }
        // 候选拒绝[LayerBoundary]：Decision/Unresolved 由各自 owner 先收敛。
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
        // 候选拒绝[ProofIncomplete]：fixed SETLIST value 白名单未复用完整 eval-event 证明。
        if set_list
            .values
            .fixed
            .iter()
            .any(|value| !expr_is_fixed_set_list_value_safe(value))
        {
            return false;
        }
        // 候选拒绝[ProofIncomplete]：prefix mention、home compaction 与 materialization count
        // 仍是全局 freshness 近似，应改成该 seed 区间的 provenance/lifetime 证明。
        if self.binding_is_shared_before_seed(block, seed_index, binding)
            || self.promotion_facts.compacts_home_slots()
            || self.materialized_bindings.get(binding).copied() != Some(1)
        {
            return false;
        }
        // 候选拒绝[LayerBoundary]：trusted home 由 promotion owner 提供。
        if self
            .promotion_facts
            .trusted_local_home_slot(local)
            .is_none()
        {
            return false;
        }

        let mut object_record_names = BTreeSet::new();
        for stmt in &block.stmts[seed_index + 1..end_index] {
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    // 候选拒绝[ProofIncomplete]：producer 的 open pack 尚未按每个目标槽位
                    // 建模，当前只消费 fixed 单值快照。
                    if decl.values.tail.is_some() {
                        return false;
                    }
                    // 候选拒绝[SemanticBarrier:Scope]：区间内重新声明 owner binding 会切换
                    // lexical owner，不能继续写回原 seed。
                    if decl
                        .bindings
                        .iter()
                        .any(|candidate| TableBinding::Local(*candidate) == binding)
                    {
                        return false;
                    }
                    // 候选拒绝[ProofIncomplete]：producer debug/capture 的 blanket gate 尚未按
                    // 本次删除是否真的改变可观察 identity 分类。
                    if decl.bindings.iter().any(|candidate| {
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
                    }) {
                        return false;
                    }
                    // 候选拒绝[ProofIncomplete]：snapshot 白名单替代了事件与 root-lifetime
                    // 证明；call/closure/constructor 中仍存在可安全内联的子集。
                    if decl
                        .values
                        .fixed
                        .iter()
                        .any(|value| !expr_is_open_owner_snapshot(value))
                    {
                        return false;
                    }
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
                        // 候选拒绝[ProofIncomplete]：open-owner proof 尚未建模 parallel/非 table
                        // assignment；需要复用 rebuild 的 lvalue/event summary。
                        return false;
                    };
                    let [value] = assign.values.fixed.as_slice() else {
                        // 候选拒绝[ProofIncomplete]：多值/open assignment 尚无精确 value-pack
                        // 与目标槽位映射。
                        return false;
                    };
                    // 候选拒绝[ProofIncomplete]：非目标 base 或 open tail 表明 scanner/rebuild
                    // 尚未提供本区间需要的精确 write/value-pack 事实。
                    if assign.values.tail.is_some()
                        || binding_from_expr(&access.base) != Some(binding)
                    {
                        return false;
                    }
                    // 候选拒绝[SemanticBarrier:Scope]：key/value 中的 owner 自引用不能搬进
                    // owner 的 LocalDecl initializer。
                    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding)
                    {
                        return false;
                    }
                    // 候选拒绝[ProofIncomplete]：key/value 白名单尚未复用完整 eval-event 与
                    // effect 证明，存在可安全的复杂表达式子集。
                    if !expr_is_data_only(&access.key) || !expr_is_fixed_set_list_value_safe(value)
                    {
                        return false;
                    }
                    if !producer_value_can_be_dropped(value) {
                        let HirTableKey::Name(name) =
                            table_key_from_expr(&access.key, self.dialect)
                        else {
                            // 候选拒绝[ProofIncomplete]：有 root 的对象值目前只跟踪静态字段
                            // 名；动态 key 需要精确 alias/overwrite 集合。
                            return false;
                        };
                        if !object_record_names.insert(name) {
                            // 候选拒绝[SemanticBarrier:Lifetime]：同名字段后写覆盖前一个对象时，
                            // 合入 constructor 并删除 producer 可能提前释放旧对象；反例见
                            // lua54_01_close#13/#14/#16。
                            return false;
                        }
                    }
                }
                _ => {
                    // 分析停用[ProofIncomplete]：open-owner region 只建模 LocalDecl/Assign，
                    // 其他语句缺少路径、effect 与资源生命周期摘要。
                    return false;
                }
            }
        }
        true
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
