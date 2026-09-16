//! 把连续的建表、字段写和 SETLIST 片段恢复为 HIR TableConstructor。
//!
//! scanner 提供带类型的构造步骤，binding/root 分析验证使用与保留要求，rebuild/commit
//! 消费同一计划完成改写；不会根据最终字段外形重新猜分配方式或原暂存槽。
//! 例如 t={}; t.x=1; t.y=2 在表未逃逸、依赖及身份证明成立时可收成 t={x=1,y=2}。
//! record key 保持 HIR 表达式，命名字段语法由后层决定。

mod bindings;
mod builder;
mod inline_value;
mod rebuild;
mod roots;
mod scan;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::hir::common::{
    HirAssign, HirExpr, HirLValue, HirProto, HirStmt, HirTableAccess, HirTableConstructor,
    HirTableField, HirValuePack, LocalId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use self::bindings::{
    BindingFacts, BindingIndex, BindingOccurrenceIndex, BindingSlots, StmtBindingSummary,
    binding_from_expr, binding_from_identity, binding_from_lvalue, collect_binding_facts,
    collect_stmt_binding_summary, expr_uses_binding,
};
use self::rebuild::producer_value_can_be_dropped;
use self::roots::RegionRootFacts;
pub(super) use self::scan::constructor_write;
use self::scan::{
    ConstructorWriteIndex, constructor_seed, constructor_uses_binding, install_constructor_seed,
    seed_delay_expr_is_unobservable, seed_overwrite_delay_is_unobservable,
    try_rebuild_constructor_region,
};
use super::mention::{
    BindingWriteCollector, ReferenceCapturedBindings, stmts_reference_captured_bindings,
    stmts_value_captured_bindings,
};
use super::object_flow::{PrivateAllocationFacts, ReturnValueFacts, RootAnalysisContext};
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::value_facts::value_facts;
use crate::hir::visit::{HirVisitor, any_stmt_structure, visit_stmts};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum TableBinding {
    Temp(TempId),
    Local(LocalId),
}

/// 构造器 owner 已核对无自引用的原字段/批次角色；完整帧事务只补原槽和事件证明。
#[derive(Clone, Copy)]
pub(super) enum ConstructorWrite<'a> {
    Record {
        binding: TableBinding,
        access: &'a HirTableAccess,
        value: &'a HirExpr,
    },
    Batch {
        binding: TableBinding,
        batch: &'a crate::hir::common::HirTableSetList,
    },
}

impl ConstructorWrite<'_> {
    pub(super) fn binding(&self) -> TableBinding {
        match self {
            Self::Record { binding, .. } | Self::Batch { binding, .. } => *binding,
        }
    }
}

type BindingId = usize;

#[derive(Debug, Clone, Copy)]
enum RegionStep<'a> {
    Producer {
        binding: TableBinding,
        source: PendingProducerSource,
        value: &'a HirExpr,
        scalar_result: bool,
        source_gc_inert: bool,
        source_preservation: ProducerSourcePreservation,
    },
    Record {
        stmt_index: usize,
        write_sources: &'a crate::hir::common::HirOperationSources,
        key: &'a HirExpr,
        value: &'a HirExpr,
    },
    SetList {
        stmt_index: usize,
        batch: &'a crate::hir::common::HirTableSetList,
    },
}

impl RegionStep<'_> {
    fn stmt_index(&self) -> usize {
        match self {
            Self::Producer { source, .. } => source.stmt_index(),
            Self::Record { stmt_index, .. } | Self::SetList { stmt_index, .. } => *stmt_index,
        }
    }
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
    PreservedIdentity,
    ObservableReplay,
    UnsupportedShape,
}

#[derive(Debug, Clone, Copy)]
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

impl PendingProducerSource {
    fn stmt_index(self) -> usize {
        match self {
            Self::Value { stmt_index, .. } | Self::ImplicitNil { stmt_index } => stmt_index,
        }
    }

    /// source 在 scanner 冻结，缺失槽的 nil 投影不再由各消费者重算。
    fn value(self, block: &crate::hir::common::HirBlock) -> Option<&HirExpr> {
        match self {
            Self::Value {
                stmt_index,
                value_index,
            } => match block.stmts.get(stmt_index)? {
                HirStmt::LocalDecl(decl) => decl.values.fixed.get(value_index),
                HirStmt::Assign(assign) => assign.values.fixed.get(value_index),
                _ => None,
            },
            Self::ImplicitNil { .. } => Some(&HirExpr::Nil),
        }
    }
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
    write_sources: crate::hir::common::HirOperationSources,
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum TableConstructorStage {
    Rebuild,
    LowerFixedBatches,
}

pub(super) fn stabilize_table_constructors_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    context: RootAnalysisContext<'_>,
    stage: TableConstructorStage,
) -> bool {
    if !block_has_table_constructor_candidate(&proto.body) {
        return false;
    }

    let temp_count = proto.temp_count;
    let first_new_local = proto.local_count;
    let BindingFacts {
        materialized: materialized_bindings,
        reference_captured: reference_captured_bindings,
        reference_captured_home_slots,
        observed_before_exit,
    } = collect_binding_facts(&proto.body, promotion_facts, temp_count, first_new_local);
    let mut pass = TableConstructorPass {
        stage,
        value_facts: &context.effects.values,
        debug_scopes: proto
            .temp_debug_scopes
            .iter()
            .enumerate()
            .filter_map(|(index, scope)| {
                scope.map(|scope| (TableBinding::Temp(TempId(index)), scope))
            })
            .chain(
                proto
                    .local_debug_scopes
                    .iter()
                    .enumerate()
                    .filter_map(|(index, scope)| {
                        scope.map(|scope| (TableBinding::Local(LocalId(index)), scope))
                    }),
            )
            .collect(),
        private_allocations: PrivateAllocationFacts::analyze(&proto.body, context, promotion_facts),
        has_cleanup: proto_has_cleanup(proto),
        materialized_bindings,
        reference_captured_bindings,
        reference_captured_home_slots,
        observed_before_exit,
        debug_identity_bindings: BindingSlots::from_debug_hints(
            &proto.temp_debug_locals,
            &proto.local_debug_hints,
        ),
        preserved_identity_bindings: BindingSlots::from_preserved_identities(proto),
        call_frame_prefix: (0..proto.local_count).map(LocalId).filter(|local| {
            matches!(proto.inline_dispositions.local(*local), crate::hir::HirInlineDisposition::Preserve(reasons)
                if reasons.contains(&crate::hir::HirInlineRetentionReason::PhysicalFramePrefix))
        }).collect(),
        promotion_facts,
        temp_count,
        next_local_index: first_new_local,
    };
    let changed = rewrite_proto(proto, &mut pass);
    proto
        .local_debug_hints
        .extend((first_new_local..pass.next_local_index).map(|_| None));
    proto.local_count = pass.next_local_index;
    proto
        .local_debug_scopes
        .extend((first_new_local..pass.next_local_index).map(|_| None));
    for index in first_new_local..pass.next_local_index {
        proto.inline_dispositions.preserve_local(
            LocalId(index),
            crate::hir::HirInlineRetentionReason::TableInitialization,
        );
    }
    changed
}

struct TableConstructorPass<'a> {
    stage: TableConstructorStage,
    value_facts: &'a ReturnValueFacts,
    debug_scopes: BTreeMap<TableBinding, usize>,
    has_cleanup: bool,
    materialized_bindings: BindingSlots<u32>,
    reference_captured_bindings: BindingSlots<bool>,
    reference_captured_home_slots: std::collections::BTreeSet<HomeSlotKey>,
    observed_before_exit: BindingSlots<bool>,
    private_allocations: PrivateAllocationFacts,
    debug_identity_bindings: BindingSlots<bool>,
    preserved_identity_bindings: BindingSlots<bool>,
    call_frame_prefix: BTreeSet<LocalId>,
    promotion_facts: &'a ProtoPromotionFacts,
    temp_count: usize,
    next_local_index: usize,
}

impl HirRewritePass for TableConstructorPass<'_> {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        if !block.stmts.iter().any(is_direct_constructor_candidate) {
            return false;
        }
        if self.stage == TableConstructorStage::LowerFixedBatches {
            return self.materialize_safe_fixed_set_lists(block);
        }

        let mut changed = false;
        let mut scratch = RebuildScratch::default();
        let mut rewritten_seeds = BTreeSet::new();
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
            &self.preserved_identity_bindings,
            self.promotion_facts,
            &self.private_allocations,
        );
        let mut stmt_ids = (0..block.stmts.len()).collect::<Vec<_>>();
        let private_overwrites: BTreeSet<_> = block
            .stmts
            .iter()
            .enumerate()
            .filter_map(|(id, stmt)| {
                self.private_allocations
                    .permits_initializer_overwrite(stmt)
                    .then_some(id)
            })
            .collect();
        let constructor_writes =
            ConstructorWriteIndex::new(&block.stmts, &binding_index, self.promotion_facts);
        let materialized_binding_counts =
            binding_index.materialized_counts(&self.materialized_bindings);
        // 先消费子构造器，父候选才能在原SETLIST角色物化前看到完整子值。
        let mut index = block.stmts.len();
        while index > 0 {
            index -= 1;
            let Some((binding, seed_ctor)) = constructor_seed(&block.stmts[index]) else {
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
                    &stmt_bindings,
                    &materialized_binding_counts,
                    &self.preserved_identity_bindings,
                    self.promotion_facts,
                    &stmt_ids,
                    &private_overwrites,
                    constructor_writes.fixed_batch_producers(binding_id),
                    self.value_facts,
                    &mut scratch,
                );
                candidate.filter(|region| {
                    let scan::ConstructorRegion {
                        constructor: rebuilt_constructor,
                        end_index,
                        preserved_stmt_indices,
                        steps,
                    } = region;
                    if matches!(seed_ctor.allocation,
                        crate::hir::HirTableAllocation::Luau(_)
                            | crate::hir::HirTableAllocation::LuauTemplate { .. })
                        && steps.iter().any(|step| match step {
                            RegionStep::SetList { batch, .. } => self.promotion_facts
                                .native_table_batch_layout(batch)
                                .is_some_and(|layout| layout.buffer.slot() > layout.base.slot() + 1),
                            RegionStep::Record { stmt_index, .. }
                                if matches!(seed_ctor.allocation, crate::hir::HirTableAllocation::LuauTemplate { .. }) => {
                                matches!(scan::constructor_write(&block.stmts[*stmt_index]),
                                    Some(ConstructorWrite::Record { access, .. })
                                    if self.promotion_facts.native_table_write_layout(access)
                                        .is_some_and(|layout| layout.key.is_none()
                                            && layout.value.is_some_and(|value|
                                                value.slot() > layout.base.slot() + 1)))
                            }
                            _ => false,
                        })
                    {
                        // 候选拒绝[LayerBoundary]：高于相邻槽的共享准备区由 native 的完整
                        // 声明/调用帧消费；先折叠单个 RHS 会丢掉组内原 SETLIST/record 角色。
                        return false;
                    }
                    let roots = RegionRootFacts::new(steps, preserved_stmt_indices);
                    let runtime_operands = crate::hir::table_layout::runtime_table_operand_requirements(rebuilt_constructor);
                    if runtime_operands.keys {
                        // 候选拒绝[ReadabilityCost:RuntimeKeys]：原模板外的静态字段需要额外
                        // key local 才能保持分配；保留原字段赋值，避免为合并凭空增加声明。
                        return false;
                    }
                    if matches!(binding, TableBinding::Local(local) if self.call_frame_prefix.contains(&local))
                        && runtime_operands.any()
                    {
                        // 候选拒绝[SemanticBarrier:PhysicalFramePrefix]：运行时常量需在 seed 前新增
                        // local；原 CALL 已依赖该声明前缀，不能再改变实际源码调用基址。
                        return false;
                    }
                    let returned_batch = self.returned_batch_is_safe(block, index, binding, region);
                    let indexed_owner =
                        self.returned_indexed_region_is_safe(block, index, binding, region, &roots);
                    let source_initializer =
                        self.source_debug_initializer_is_safe(block, index, binding, region);
                    let private_owner = !self.has_cleanup
                        && roots.removed_roots_are_inert_tables
                        && (!self
                            .observed_before_exit
                            .get(binding)
                            .copied()
                            .unwrap_or_default()
                            || steps.iter().all(|step| match step {
                                RegionStep::Producer {
                                    binding,
                                    source_gc_inert: false,
                                    source,
                                    ..
                                } if preserved_stmt_indices
                                    .binary_search(&source.stmt_index())
                                    .is_err() =>
                                {
                                    self.private_allocations
                                        .contains(binding_identity(*binding))
                                }
                                _ => true,
                            }))
                        && (!binding_occurrences.has_source_identity(binding_id)
                            || source_initializer);
                    let open_owner = rebuilt_constructor.trailing_multivalue.is_some()
                        && self
                            .open_constructor_region_is_safe(block, index, binding, region, &roots);
                    if !indexed_owner
                        && !private_owner
                        && roots.temp_producers.iter().any(|temp| {
                            !open_owner
                                || !self
                                    .promotion_facts
                                    .call_result_root_ends_after_value_use(*temp)
                        })
                    {
                        // 原始标量结果须由完整 indexed/open-owner 事务消费；不能先提交字段前缀，
                        // 再让后缀重建已经删除的 physical root 身份。
                        return false;
                    }
                    let open_capture_is_safe = rebuilt_constructor.trailing_multivalue.is_none()
                        || self.open_constructor_capture_region_is_safe(
                            block, index, *end_index, binding,
                        );
                    // Value-position nil is governed by the completed table shape, not by whether
                    // a nil literal happened to occur in a producer. A final absent array slot and
                    // a nil-valued record field preserve the same key set as the original writes.
                    let nil_shape_is_supported = returned_batch
                        || constructor_nil_shape_is_supported(&seed_ctor, rebuilt_constructor);
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
                    let unsupported_exact_width = roots.has_exact_width_tail;
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
                    // 已通过 `open_constructor_region_is_safe` 的 LocalDecl owner 是
                    // 更精确的整区间证明：producer 只为该 initializer 的最终 open tail
                    // 服务，不能再让通用“后续仍提到 table”近似覆盖这项结论。
                    // 候选拒绝[SemanticBarrier:Lifetime]：反例见
                    // tests/case_lifetime/close_23_close.lua#lua54_01_close#13/#14/#16。
                    let producer_root_is_observable = !indexed_owner
                        && !private_owner
                        && !open_owner
                        && !returned_batch
                        && roots.has_removed_object_producer
                        && binding_occurrences.has_mention_after(binding_id, stmt_ids[*end_index]);
                    // 候选拒绝[SemanticBarrier:Lifetime]：对象 producer 后再覆盖 table field
                    // 时，删除 producer 会提前释放最后一个强引用；反例同上。
                    let has_followup_object_write = !indexed_owner
                        && !private_owner
                        && !(open_owner
                            && rebuilt_constructor
                                .allocation
                                .indexed_array_capacity()
                                .is_some())
                        && roots.has_followup_object_write;
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
                    let overwrite_timing_is_safe = indexed_owner
                        || open_owner
                        || source_initializer
                        || source_local_owner
                        || self.seed_overwrites_unobservable_entry_nil(binding)
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
            let Some(scan::ConstructorRegion {
                constructor,
                end_index,
                preserved_stmt_indices,
                ..
            }) = rebuilt
            else {
                continue;
            };
            rewritten_seeds.insert(seed_stmt_id);
            install_constructor_seed(&mut block.stmts[index], constructor);
            let summary = collect_stmt_binding_summary(&block.stmts[index], &mut binding_index);
            binding_occurrences.replace_stmt(seed_stmt_id, &stmt_bindings[index], &summary);
            stmt_bindings[index] = summary;
            let drain_end = end_index;
            if drain_end > index {
                // 三表按同一原始坐标稳定压缩；只在整段处理后搬移尾部，避免每个字段
                // 删除都移动其后的全部语句。稳定 stmt_id 仍用于撤销旧 occurrence。
                let mut write = index + 1;
                for read in index + 1..=drain_end {
                    let retain_identity = preserved_stmt_indices.binary_search(&read).is_err()
                        && matches!(&block.stmts[read], HirStmt::LocalDecl(decl)
                            if decl.bindings.iter().any(|local|
                                binding_index.id_of(TableBinding::Local(*local)).is_some_and(|id|
                                    binding_occurrences.has_mention_after(id, stmt_ids[drain_end]))));
                    if retain_identity {
                        let HirStmt::LocalDecl(decl) = &mut block.stmts[read] else {
                            unreachable!()
                        };
                        // 只移走已通过完整private窗口的initializer；原local身份/声明位置仍保留。
                        decl.values = HirValuePack::default();
                        let summary =
                            collect_stmt_binding_summary(&block.stmts[read], &mut binding_index);
                        binding_occurrences.replace_stmt(
                            stmt_ids[read],
                            &stmt_bindings[read],
                            &summary,
                        );
                        stmt_bindings[read] = summary;
                    }
                    if preserved_stmt_indices.binary_search(&read).is_ok() || retain_identity {
                        block.stmts.swap(write, read);
                        stmt_bindings.swap(write, read);
                        stmt_ids.swap(write, read);
                        write += 1;
                    } else {
                        binding_occurrences.remove_stmt(stmt_ids[read], &stmt_bindings[read]);
                    }
                }
                drop(block.stmts.drain(write..drain_end + 1));
                drop(stmt_bindings.drain(write..drain_end + 1));
                drop(stmt_ids.drain(write..drain_end + 1));
            }
            changed = true;
        }

        if !rewritten_seeds.is_empty() {
            // runtime常量只在最终存活seed上物化；子region继续归入父initializer时，不提前
            // 制造一个父表达式尚不可见的operand local。分配事实仍随完整constructor保留。
            let stmts = std::mem::take(&mut block.stmts);
            for (mut stmt, id) in stmts.into_iter().zip(stmt_ids) {
                if rewritten_seeds.contains(&id)
                    && let Some((_, constructor)) = constructor_seed(&stmt)
                {
                    let mut constructor = constructor.clone();
                    block.stmts.extend(
                        crate::hir::table_layout::materialize_runtime_table_operands(
                            &mut constructor,
                            &mut self.next_local_index,
                        ),
                    );
                    install_constructor_seed(&mut stmt, constructor);
                }
                block.stmts.push(stmt);
            }
        }
        changed |= self.materialize_safe_fixed_set_lists(block);
        changed
    }
}

fn binding_identity(binding: TableBinding) -> crate::hir::common::HirBinding {
    match binding {
        TableBinding::Temp(temp) => crate::hir::common::HirBinding::Temp(temp),
        TableBinding::Local(local) => crate::hir::common::HirBinding::Local(local),
    }
}

/// scope 来自 seed 的实际 binding；这里只证明尚未开始的 debug initializer 及原 home。
/// 原 Batch 和 seed 必须仍配对，GC/字段事件与 capture/资源边界由调用 owner 另外核对。
pub(super) fn debug_initializer_home(
    seed: &HirStmt,
    batch: &crate::hir::common::HirTableSetList,
    debug_scope: Option<usize>,
    facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    let (binding, constructor) = constructor_seed(seed)?;
    if debug_scope.is_none()
        || batch.initializer_debug_scope != debug_scope
        || binding_from_expr(&batch.base) != Some(binding)
    {
        return None;
    }
    let home = match binding {
        TableBinding::Temp(temp) if facts.is_direct_table_seed_temp(temp) => {
            facts.trusted_temp_home_slot(temp)?
        }
        TableBinding::Local(local)
            if matches!(seed, HirStmt::LocalDecl(_)) && facts.is_direct_table_seed_local(local) =>
        {
            facts.trusted_local_home_slot(local)?
        }
        _ => return None,
    };
    // 声明身份在 batch 后开始，但 NEWTABLE 在 initializer 起点就写入目标 home。
    // 此处证明原分配仍写同槽，不能用“覆盖入口 nil”替代它；前面的 CALL 可以已用过此槽。
    (facts.allocation_result_home(constructor) == Some(home)).then_some(home)
}

impl TableConstructorPass<'_> {
    /// Structure 的 scope 身份与 lowering 的批次位置共同证明字段属于尚未开始的声明。
    /// GC/求值序仍走同一 region guard；这里仅撤销对 initializer 的过宽 debug 身份拒绝。
    fn source_debug_initializer_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
        region: &scan::ConstructorRegion<'_>,
    ) -> bool {
        let Some(RegionStep::SetList { batch, .. }) = region.steps.last() else {
            return false;
        };
        if self
            .reference_captured_bindings
            .get(binding)
            .copied()
            .unwrap_or_default()
        {
            return false;
        }
        let home = debug_initializer_home(
            &block.stmts[seed_index],
            batch,
            self.debug_scopes.get(&binding).copied(),
            self.promotion_facts,
        );
        home.is_some_and(|home| !self.reference_captured_home_slots.contains(&home))
    }

    /// 一次 raw 数组批次直接离开无 cleanup 的函数时，槽根与结果构造器同时结束当前 frame。
    /// scanner/rebuild 已证明 producer 消费和事件序；这里只证明提交所需的批次/出口身份，
    /// 不把可能含 nil 的原始 SETLIST 误当作逐项 SETTABLE，也不跨过后续 root 观察点。
    fn returned_batch_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
        region: &scan::ConstructorRegion<'_>,
    ) -> bool {
        let scan::ConstructorRegion {
            constructor,
            end_index,
            preserved_stmt_indices: preserved,
            steps,
        } = region;
        let end_index = *end_index;
        if self.has_cleanup || !preserved.is_empty() {
            return false;
        }
        let Some((_, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        let Some(RegionStep::SetList { batch, .. }) = steps.last() else {
            return false;
        };
        let [HirStmt::Return(ret)] = &block.stmts[end_index + 1..] else {
            return false;
        };
        if !matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
            || !seed.fields.is_empty()
            || seed.trailing_multivalue.is_some()
            || batch.start_index != 1
            || batch.values.tail.is_some() != constructor.trailing_multivalue.is_some()
            || binding_from_expr(&batch.base) != Some(binding)
            || ret.values.tail.is_some()
            || ret.values.fixed.len() != 1
            || binding_from_expr(&ret.values.fixed[0]) != Some(binding)
            || constructor.fields.len() != batch.values.fixed.len()
            || !constructor
                .fields
                .iter()
                .all(|field| matches!(field, HirTableField::Array(_)))
            || self
                .preserved_identity_bindings
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
        steps[..steps.len() - 1].iter().all(|step| {
            let RegionStep::Producer {
                binding: TableBinding::Local(local),
                ..
            } = step
            else {
                return false;
            };
            let binding = TableBinding::Local(*local);
            !self
                .preserved_identity_bindings
                .get(binding)
                .copied()
                .unwrap_or_default()
                && !self
                    .reference_captured_bindings
                    .get(binding)
                    .copied()
                    .unwrap_or_default()
        }) && self.open_constructor_capture_region_is_safe(block, seed_index, end_index, binding)
    }

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

            if self.fold_fixed_batch_across_root_copy(block, index, binding, &set_list) {
                changed = true;
                continue;
            }

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
                changed = true;
                continue;
            }

            // Fresh local seeds can have harmless scalar/keyed setup statements between the
            // allocation and SETLIST. Preserve those statements and replace only the raw fixed
            // batch, so neither the table allocation nor a physical-root overwrite moves.
            if self.stage == TableConstructorStage::LowerFixedBatches
                && let Some(_seed_index) = self
                    .find_local_set_list_seed_for_indexed_writes(block, index, binding, &set_list)
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
                                sources: Default::default(),
                                metamethod_free: false,
                                base: base.clone(),
                                key: HirExpr::Integer(i64::from(key)),
                                method_setup_protocol: None,
                            }))],
                            values: HirValuePack::fixed(vec![value.clone()]),
                            initializer_merge_transaction: None,
                            generic_for_initializer_producer: None,
                            generic_for_dispatch_release: None,
                            method_rewrite_transaction: None,
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
            let residuals = expr_open_tail_residuals(tail.as_expr());
            if residuals.decision {
                // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
                return None;
            }
            if residuals.unresolved {
                // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出的失败证据；
                // table pass 不把它埋进普通 constructor 表达式。
                return None;
            }
        }
        let residuals = exprs_open_tail_residuals(&set_list.values.fixed);
        if residuals.decision {
            // 候选拒绝[LayerBoundary]：fixed 值中的 Decision 由 decision/eliminate 消费。
            return None;
        }
        if residuals.unresolved {
            // 候选拒绝[PolicyBoundary]：fixed Unresolved 保留为 permissive 失败证据。
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

    /// 入口 nil 槽没有旧 collectable root；且无人能通过 capture/debug 观察 seed store。
    /// Dataflow 已排除回边旧值，不能凭“首个 PC 定义”推断这里可以延后覆盖。
    fn seed_overwrites_unobservable_entry_nil(&self, binding: TableBinding) -> bool {
        let TableBinding::Temp(temp) = binding else {
            return false;
        };
        self.promotion_facts.overwrites_entry_nil(temp)
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
            && self
                .promotion_facts
                .trusted_temp_home_slot(temp)
                .is_some_and(|home| !self.reference_captured_home_slots.contains(&home))
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
        let residuals = exprs_open_tail_residuals(&set_list.values.fixed);
        if residuals.decision {
            // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
            return None;
        }
        if residuals.unresolved {
            // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。
            return None;
        }
        if matches!(binding, TableBinding::Temp(_))
            && !self.seed_overwrites_unobservable_entry_nil(binding)
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
            if !matches!(
                block.stmts[seed_index],
                HirStmt::LocalDecl(_) | HirStmt::Assign(_)
            ) {
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
        // The seed at `seed_index` installs a fresh value epoch whose allocation remains in place.
        // It may be a LocalDecl or an assignment that deliberately overwrites an older physical
        // root before evaluating the SETLIST values; the indexed rewrite preserves that timing.
        // Prefix writes may target it directly; without seeding this set, the final membership
        // check could never accept the very owner the proof started from.
        let mut fresh_tables = BTreeSet::from([binding]);
        let mut seed_aliases = BTreeSet::from([binding]);
        let mut seed_carriers = BTreeSet::new();
        let mut seed_tbc_active = false;
        for (offset, stmt) in block.stmts[seed_index..set_list_index].iter().enumerate() {
            let stmt_index = seed_index + offset;
            if stmt_index == seed_index {
                continue;
            }
            if stmt_index != seed_index && debug_seed && !debug_prefix_stmt_is_inert(stmt) {
                // 候选拒绝[SemanticBarrier:DebugScope]：effectful prefix 可通过
                // `debug.getlocal(2, 1)` 取得 source-visible seed 并安装 metatable；原始 raw
                // SETLIST 绕过 `__newindex`，拆成 indexed writes 后会触发它。
                return false;
            }
            match stmt {
                HirStmt::LocalRootRelease(local) => {
                    let released = TableBinding::Local(*local);
                    seed_aliases.remove(&released);
                    seed_carriers.remove(&released);
                    fresh_tables.remove(&released);
                }
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
                            seed_homes.as_deref(),
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
                        seed_homes.as_deref(),
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
                            seed_homes.as_deref(),
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
                                    seed_homes.as_deref(),
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
                                    seed_homes.as_deref(),
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
                        seed_homes.as_deref(),
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
                        seed_homes.as_deref(),
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

        impl HirVisitor<'_> for Probe<'_> {
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
        crate::hir::visit::visit_expr(expr, &mut probe);
        probe.found
    }

    fn captures_may_share_seed_home(
        &self,
        captured: &ReferenceCapturedBindings,
        seed_binding: TableBinding,
        seed_homes: &BTreeSet<HomeSlotKey>,
    ) -> bool {
        captured.locals.iter().any(|local| {
            TableBinding::Local(*local) == seed_binding
                || !self
                    .promotion_facts
                    .complete_local_home_slots(*local)
                    .is_disjoint(seed_homes)
        }) || captured.temps.iter().any(|temp| {
            TableBinding::Temp(*temp) == seed_binding
                || !self
                    .promotion_facts
                    .complete_temp_home_slots(*temp)
                    .is_disjoint(seed_homes)
        }) || captured.params.iter().any(|param| {
            !self
                .promotion_facts
                .complete_param_home_slots(*param)
                .is_disjoint(seed_homes)
        })
    }

    fn open_constructor_capture_region_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        end_index: usize,
        binding: TableBinding,
    ) -> bool {
        let seed_homes = match binding {
            TableBinding::Local(local) => self.promotion_facts.complete_local_home_slots(local),
            TableBinding::Temp(temp) => self.promotion_facts.complete_temp_home_slots(temp),
        };
        // 候选拒绝[SemanticBarrier:Capture]：ByReference closure 可持续观察 owner cell，
        // ByValue closure 则在 producer 原位置冻结该 cell；把 producer 移入 LocalDecl
        // initializer 会把两者都放到 owner store 之前。complete possible-home 相交时，
        // captured binding 可指向该 cell，不能改变 snapshot/后续读取到的 table 值。
        block.stmts[seed_index + 1..end_index].iter().all(|stmt| {
            let stmt_slice = std::slice::from_ref(stmt);
            !self.captures_may_share_seed_home(
                &stmts_reference_captured_bindings(stmt_slice),
                binding,
                &seed_homes,
            ) && !self.captures_may_share_seed_home(
                &stmts_value_captured_bindings(stmt_slice),
                binding,
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

        impl HirVisitor<'_> for Probe<'_, '_> {
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
        crate::hir::visit::visit_stmts(std::slice::from_ref(stmt), &mut probe);
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

        impl HirVisitor<'_> for CarrierPropagation<'_, '_> {
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

        impl HirVisitor<'_> for HazardProbe<'_, '_> {
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
        let residuals = expr_open_tail_residuals(tail.as_expr())
            .union(exprs_open_tail_residuals(&set_list.values.fixed));
        if residuals.decision {
            // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
            return false;
        }
        if residuals.unresolved {
            // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。fixed 与
            // open 值仍按原 SETLIST 顺序留在同一个 constructor batch。
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

    /// open constructor 保留原 allocation；LocalDecl 使用词法 owner，原始 Temp seed
    /// 则必须覆盖入口 nil 并在无 cleanup 的出口交出整张表。原始 producer 的覆盖终点
    /// 与独立字段持有共同证明根的转交，不能仅凭同 home 把值身份合并成一个 mutable local。
    fn open_constructor_region_is_safe(
        &self,
        block: &crate::hir::common::HirBlock,
        seed_index: usize,
        binding: TableBinding,
        region: &scan::ConstructorRegion<'_>,
        roots: &RegionRootFacts,
    ) -> bool {
        let scan::ConstructorRegion {
            constructor,
            end_index,
            preserved_stmt_indices,
            steps,
        } = region;
        let end_index = *end_index;
        let consumes_temp_producer = !roots.temp_producers.is_empty();
        if matches!(binding, TableBinding::Temp(_)) || consumes_temp_producer {
            let [HirStmt::Return(ret)] = &block.stmts[end_index + 1..] else {
                return false;
            };
            if self.has_cleanup
                || matches!(binding, TableBinding::Temp(_))
                    && !self.seed_overwrites_unobservable_entry_nil(binding)
                || ret.values.tail.is_some()
                || ret.values.fixed.len() != 1
                || binding_from_expr(&ret.values.fixed[0]) != Some(binding)
            {
                return false;
            }
        }
        let Some((seed_binding, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        let Some(RegionStep::SetList {
            batch: set_list, ..
        }) = steps.last()
        else {
            return false;
        };
        if seed_binding != binding
            || !(matches!(block.stmts[seed_index], HirStmt::LocalDecl(_))
                || matches!(binding, TableBinding::Temp(_)))
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
        let indexed_layout = seed.allocation == constructor.allocation
            && constructor.matches_indexed_array_capacity(
                constructor
                    .fields
                    .iter()
                    .filter(|field| matches!(field, HirTableField::Array(_)))
                    .count(),
            );
        if consumes_temp_producer && !indexed_layout {
            return false;
        }
        if (!indexed_layout
            && seed.fields.iter().any(|field| match field {
                HirTableField::Array(value) => !value_facts(value).is_non_nil(),
                HirTableField::Record(record) => !value_facts(&record.value).is_non_nil(),
            }))
            || set_list.start_index == 0
            || (!indexed_layout
                && set_list.start_index
                    > u32::try_from(
                        seed.fields
                            .iter()
                            .filter(|field| matches!(field, HirTableField::Array(_)))
                            .count()
                            .saturating_add(1),
                    )
                    .unwrap_or(u32::MAX))
            || (!indexed_layout
                && (constructor_has_nil_field(constructor)
                    || !array_fields_have_safe_nil_shape(&constructor.fields)))
        {
            return false;
        }
        if indexed_layout {
            // indexed 前缀写与末尾 open batch 必须不重叠，才可把 producer 的独立根
            // 交给同值字段持有；重复 key 或覆盖数组前缀仍保留原事务。
            let mut integer_keys = BTreeSet::new();
            let mut string_keys = BTreeSet::new();
            for step in steps {
                let RegionStep::Record { key, .. } = step else {
                    continue;
                };
                let unique = match key {
                    HirExpr::Integer(key) if *key < i64::from(set_list.start_index) => {
                        integer_keys.insert(*key)
                    }
                    HirExpr::String(key) => string_keys.insert(key),
                    _ => false,
                };
                if !unique {
                    return false;
                }
            }
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
        let residuals = expr_open_tail_residuals(tail.as_expr());
        if residuals.decision {
            // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化。
            return false;
        }
        if residuals.unresolved {
            // 候选拒绝[PolicyBoundary]：Unresolved 保留为 permissive 失败证据。
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
        // scanner 已冻结 owner 独立性、逐槽投影和角色；rebuild 已证明事件序与完整消费。
        // 此处只补 open-owner 的 debug/capture 和前置固定批次约束，不重认原语句语法。
        for step in steps.iter().filter(|step| step.stmt_index() < end_index) {
            match step {
                RegionStep::Producer {
                    binding: producer,
                    source,
                    ..
                } => match producer {
                    TableBinding::Temp(temp) => {
                        if !self
                            .promotion_facts
                            .call_result_root_ends_after_value_use(*temp)
                        {
                            return false;
                        }
                    }
                    TableBinding::Local(_) => {
                        if self
                            .debug_identity_bindings
                            .get(*producer)
                            .copied()
                            .unwrap_or_default()
                        {
                            return false;
                        }
                        assert!(
                            !self
                                .reference_captured_bindings
                                .get(*producer)
                                .copied()
                                .unwrap_or_default()
                                || preserved_stmt_indices
                                    .binary_search(&source.stmt_index())
                                    .is_ok(),
                            "reference-captured producer source must be preserved by the rebuild plan",
                        );
                    }
                },
                RegionStep::SetList { batch, .. } => {
                    if batch.values.tail.is_some()
                        || batch
                            .values
                            .fixed
                            .iter()
                            .any(|value| !expr_is_fixed_set_list_value_safe(value))
                    {
                        return false;
                    }
                }
                RegionStep::Record { .. } => {}
            }
        }
        true
    }

    /// 根 holder 的纯 copy 可以留在完整初始化之后；分配仍先发生，SETLIST 不执行用户代码。
    /// `seed={}; root=source; SETLIST seed(root)` 变为 `seed={source}; root=source`，
    /// 保留显式 root 的覆盖与释放，避免为恢复构造器而删除前层签发的生命周期事务。
    fn fold_fixed_batch_across_root_copy(
        &self,
        block: &mut crate::hir::common::HirBlock,
        index: usize,
        binding: TableBinding,
        batch: &crate::hir::common::HirTableSetList,
    ) -> bool {
        let Some(mut seed_index) = index.checked_sub(2) else {
            return false;
        };
        // 显式 root release 仅写 nil；保留原语句，允许它跨过无事件的 copy/预分配写入。
        // 表分配仍在 release 之前；下方拒绝 source/owner 被该区间清空的情况。
        while matches!(block.stmts[seed_index], HirStmt::LocalRootRelease(_)) {
            let Some(previous) = seed_index.checked_sub(1) else {
                return false;
            };
            seed_index = previous;
        }
        let Some((owner, seed)) = constructor_seed(&block.stmts[seed_index]) else {
            return false;
        };
        let HirStmt::Assign(copy) = &block.stmts[index - 1] else {
            return false;
        };
        let ([HirLValue::Local(root)], [source], None) = (
            copy.targets.as_slice(),
            copy.values.fixed.as_slice(),
            &copy.values.tail,
        ) else {
            return false;
        };
        if owner != binding
            || !seed.fields.is_empty()
            || seed.trailing_multivalue.is_some()
            || batch.start_index != 1
            || batch.values.tail.is_some()
            || !matches!(batch.values.fixed.as_slice(), [HirExpr::LocalRef(value)] if value == root)
            || !matches!(
                source,
                HirExpr::ParamRef(_)
                    | HirExpr::LocalRef(_)
                    | HirExpr::UpvalueRef(_)
                    | HirExpr::TempRef(_)
            )
            || expr_uses_binding(source, binding)
            || binding == TableBinding::Local(*root)
            || block.stmts[seed_index + 1..index - 1].iter().any(|stmt| {
                let HirStmt::LocalRootRelease(local) = stmt else {
                    unreachable!("only root releases separate the seed from its copy")
                };
                let released = TableBinding::Local(*local);
                released == binding || expr_uses_binding(source, released)
            })
        {
            return false;
        }
        let mut rewritten_batch = batch.clone();
        rewritten_batch.values.fixed[0] = source.clone();
        let constructor = constructor_with_set_list(seed, &rewritten_batch);
        if !constructor_nil_shape_is_supported(seed, &constructor) {
            // 候选拒绝[SemanticBarrier:TableShape]：容量不符时 SETLIST 可能扩容，不能当作无事件写。
            return false;
        }
        // 候选接受[EvalOrderProof]：空表分配保持原位；随后仅复制同一引用并完成预分配写入，
        // 没有调用、分配或元方法可改变 source。root 赋值仍保留，旧值也只多跨过无事件 SETLIST。
        install_constructor_seed(&mut block.stmts[seed_index], constructor);
        block.stmts.remove(index);
        true
    }
}

/// 完整原帧已核对各 record 的事件和槽；字段角色及模板隐式初始化仍由同一 builder 消费。
pub(super) fn constructor_with_native_records(
    seed: &HirTableConstructor,
    records: Vec<crate::hir::common::HirRecordField>,
) -> Option<HirTableConstructor> {
    use crate::value_semantics::table::TableExpression;
    let mut builder = builder::ConstructorBuilder::from_constructor(seed.clone());
    for record in records {
        builder.push_record_field(record);
    }
    let constructor = builder.into_constructor();
    let allocation_matches = match constructor.allocation {
        crate::hir::HirTableAllocation::LuauTemplate { .. } => constructor.fields.len() <= 32,
        crate::hir::HirTableAllocation::Template { .. } => {
            constructor.matches_allocation_capacity(0)
        }
        _ => false,
    };
    (allocation_matches
        && constructor.fields.iter().all(|field| {
            matches!(field,
            HirTableField::Record(record)
                if constructor.allocation.permits_record_key(record.key.table_key()))
        })
        && constructor.implicit_template_fields.is_empty()
        && !crate::hir::table_layout::runtime_table_operand_requirements(&constructor).any())
    .then_some(constructor)
}

/// 完整原帧已证明 producer 时序后，字段 owner 统一处理开放覆盖、容量和初始化约束。
pub(super) fn constructor_with_native_batch(
    seed: &HirTableConstructor,
    batch: &crate::hir::common::HirTableSetList,
) -> Option<HirTableConstructor> {
    let mut builder = builder::ConstructorBuilder::from_constructor(seed.clone());
    builder.append_batch(batch, &mut RebuildScratch::default())?;
    let constructor = builder.into_constructor();
    let arrays = constructor
        .fields
        .iter()
        .filter(|field| matches!(field, HirTableField::Array(_)))
        .count();
    (constructor.matches_allocation_capacity(arrays)
        && !crate::hir::table_layout::runtime_table_operand_requirements(&constructor).any())
    .then_some(constructor)
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

fn expr_is_data_only(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Unary(_) => seed_delay_expr_is_unobservable(expr),
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

#[derive(Clone, Copy, Default)]
struct OpenTailResiduals {
    decision: bool,
    unresolved: bool,
}

impl OpenTailResiduals {
    fn union(self, other: Self) -> Self {
        Self {
            decision: self.decision || other.decision,
            unresolved: self.unresolved || other.unresolved,
        }
    }
}

fn expr_open_tail_residuals(expr: &HirExpr) -> OpenTailResiduals {
    // The LocalDecl/direct-owner proof keeps the allocation at the original seed statement, so
    // ordinary calls and lookups in the constructor tail retain their source evaluation point.
    // Decision awaits its statement owner, while Unresolved is retained diagnostic evidence.
    // Track them independently so each acceptance guard records its actual rejection contract.
    match expr {
        HirExpr::Decision(_) => OpenTailResiduals {
            decision: true,
            unresolved: false,
        },
        HirExpr::Unresolved(_) => OpenTailResiduals {
            decision: false,
            unresolved: true,
        },
        HirExpr::TableAccess(access) => {
            expr_open_tail_residuals(&access.base).union(expr_open_tail_residuals(&access.key))
        }
        HirExpr::Unary(unary) => expr_open_tail_residuals(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_open_tail_residuals(&binary.lhs).union(expr_open_tail_residuals(&binary.rhs))
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_open_tail_residuals(&logical.lhs).union(expr_open_tail_residuals(&logical.rhs))
        }
        HirExpr::Call(call) => {
            expr_open_tail_residuals(&call.callee).union(exprs_open_tail_residuals(&call.args))
        }
        HirExpr::TableConstructor(constructor) => constructor
            .fields
            .iter()
            .fold(OpenTailResiduals::default(), |residuals, field| {
                residuals.union(match field {
                    HirTableField::Array(value) => expr_open_tail_residuals(value),
                    HirTableField::Record(record) => expr_open_tail_residuals(&record.key)
                        .union(expr_open_tail_residuals(&record.value)),
                })
            })
            .union(
                constructor
                    .trailing_multivalue
                    .as_ref()
                    .map(|tail| expr_open_tail_residuals(tail.as_expr()))
                    .unwrap_or_default(),
            ),
        HirExpr::Closure(_)
        | HirExpr::Nil
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
        | HirExpr::CaptureInitializer(_)
        | HirExpr::VarArg => OpenTailResiduals::default(),
    }
}

fn exprs_open_tail_residuals<'a>(
    exprs: impl IntoIterator<Item = &'a HirExpr>,
) -> OpenTailResiduals {
    exprs
        .into_iter()
        .fold(OpenTailResiduals::default(), |residuals, expr| {
            residuals.union(expr_open_tail_residuals(expr))
        })
}

fn debug_prefix_stmt_is_inert(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => true,
        HirStmt::LocalDecl(decl) => {
            decl.values.tail.is_none() && decl.values.fixed.iter().all(debug_prefix_expr_is_inert)
        }
        HirStmt::Assign(assign) => {
            assign.values.tail.is_none()
                && assign.values.fixed.iter().all(debug_prefix_expr_is_inert)
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

fn debug_prefix_expr_is_inert(expr: &HirExpr) -> bool {
    match expr {
        // 闭包及其 producer 保持原位：捕获已有 binding 不调用子函数，ByValue 的读取
        // 也不后移。这里只证明无 debug 回调；捕获 seed 的持有/逃逸仍由 prefix scan 判定。
        HirExpr::Closure(_) => true,
        HirExpr::TableConstructor(constructor) => {
            constructor.fields.iter().all(|field| match field {
                HirTableField::Array(value) => debug_prefix_expr_is_inert(value),
                HirTableField::Record(record) => {
                    record_key_is_data_only(&record.key)
                        && debug_prefix_expr_is_inert(&record.value)
                }
            }) && constructor
                .trailing_multivalue
                .as_ref()
                .is_none_or(|tail| debug_prefix_expr_is_inert(tail.as_expr()))
        }
        _ => expr_is_data_only(expr),
    }
}

fn proto_has_cleanup(proto: &HirProto) -> bool {
    proto.body.stmts.iter().any(|stmt| {
        any_stmt_structure(stmt, &mut |stmt| {
            matches!(stmt, HirStmt::ToBeClosed(_) | HirStmt::Close(_))
        })
    })
}

fn stmt_contains_close(stmt: &HirStmt) -> bool {
    any_stmt_structure(stmt, &mut |stmt| matches!(stmt, HirStmt::Close(_)))
}

/// Splitting raw SETLIST into indexed writes interleaves each write with evaluation of the next
/// value.  Scalar values and data-only nested constructors are safe: they cannot observe the
/// target table between writes, and the fresh-seed proof rules out metatable dispatch.
fn expr_is_indexed_set_list_value_safe(expr: &HirExpr) -> bool {
    if matches!(expr, HirExpr::Unary(_)) {
        return seed_delay_expr_is_unobservable(expr);
    }
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
        HirExpr::Closure(closure) => closure.captures.iter().all(|capture| {
            matches!(
                capture.binding,
                crate::hir::HirBinding::Param(_)
                    | crate::hir::HirBinding::Local(_)
                    | crate::hir::HirBinding::Temp(_)
            )
        }),
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

fn record_key_is_data_only(key: &HirExpr) -> bool {
    expr_is_data_only(key)
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
        HirStmt::LocalRootRelease(_) => false,
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
                    HirExpr::Integer(index) => (1..=array_fields).contains(index),
                    HirExpr::Number(index) => {
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
    if !crate::hir::table_layout::matches_luau_allocation(rebuilt) {
        // 候选拒绝[SemanticBarrier:TableShape]：扩大 Luau hash 预分配改变 pairs 顺序。
        return false;
    }
    if seed.allocation == rebuilt.allocation
        && rebuilt.matches_allocation_capacity(
            rebuilt
                .fields
                .iter()
                .filter(|field| matches!(field, HirTableField::Array(_)))
                .count(),
        )
    {
        return !constructor_adds_definite_nil_record_key(seed, rebuilt);
    }
    if matches!(
        seed.allocation,
        crate::hir::common::HirTableAllocation::Indexed { .. }
            | crate::hir::common::HirTableAllocation::PucBatched(_)
    ) {
        // 候选拒绝[SemanticBarrier:TableShape]：record 语法也会预分配 hash；原空表
        // 吸收运行时写入后改变扩容和 #table，不能退回只检查数组 nil 的规则（regress_512）。
        return false;
    }
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
                if matches!(&record.key, HirExpr::Nil)
        )
    })
}

/// An array constructor may contain one value whose runtime nil-ness is unknown only when it
/// is the final array slot.  If a later slot is definitely populated, a preceding nil changes
/// the VM's array-part/length result (`t[1]=nil; t[2]=1` is not `{nil, 1}`).
fn values_have_safe_nil_shape(mut non_nil: impl Iterator<Item = bool>) -> bool {
    while let Some(definite) = non_nil.next() {
        if !definite {
            return non_nil.next().is_none();
        }
    }
    true
}

/// 这里按语句顺序追踪 direct binding 当前 definition 的 nil 性；producer 语句保持原位，
/// 因此不会继承 generic fold transaction 的表达式 clone 或 root lifetime 风险。
fn local_set_list_values_have_safe_nil_shape(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    set_list_index: usize,
    values: &[HirExpr],
) -> bool {
    let mut definitions = BTreeMap::<TableBinding, bool>::new();
    for stmt in &block.stmts[seed_index + 1..set_list_index] {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                let value_facts = decl
                    .values
                    .fixed
                    .iter()
                    .map(|value| expr_is_definitely_non_nil_from_definitions(value, &definitions))
                    .collect::<Vec<_>>();
                for (index, local) in decl.bindings.iter().enumerate() {
                    let definitely_non_nil = value_facts.get(index).copied().unwrap_or(false);
                    definitions.insert(TableBinding::Local(*local), definitely_non_nil);
                }
            }
            HirStmt::Assign(assign) => {
                let value_facts = assign
                    .values
                    .fixed
                    .iter()
                    .map(|value| expr_is_definitely_non_nil_from_definitions(value, &definitions))
                    .collect::<Vec<_>>();
                let exact_width = assign.values.tail.is_none()
                    && assign.targets.len() == assign.values.fixed.len();
                for (index, target) in assign.targets.iter().enumerate() {
                    let Some(binding) = binding_from_lvalue(target) else {
                        continue;
                    };
                    let definitely_non_nil =
                        exact_width && value_facts.get(index).copied().unwrap_or(false);
                    definitions.insert(binding, definitely_non_nil);
                }
            }
            _ => {
                // 结构化语句可能按路径改写已知 binding；区间内没有 must-def 合流证明时，
                // 不能沿用语句之前的 non-nil 事实。
                visit_stmts(
                    std::slice::from_ref(stmt),
                    &mut BindingWriteCollector(|binding| {
                        if let Some(binding) = binding_from_identity(binding) {
                            definitions.insert(binding, false);
                        }
                    }),
                );
            }
        }
    }

    values_have_safe_nil_shape(
        values
            .iter()
            .map(|value| expr_is_definitely_non_nil_from_definitions(value, &definitions)),
    )
}

fn expr_is_definitely_non_nil_from_definitions(
    expr: &HirExpr,
    definitions: &BTreeMap<TableBinding, bool>,
) -> bool {
    if value_facts(expr).is_non_nil() {
        return true;
    }
    let Some(binding) = binding_from_expr(expr) else {
        return false;
    };
    definitions.get(&binding).copied().unwrap_or(false)
}

fn array_fields_have_safe_nil_shape(fields: &[HirTableField]) -> bool {
    values_have_safe_nil_shape(fields.iter().filter_map(|field| match field {
        HirTableField::Array(value) => Some(value_facts(value).is_non_nil()),
        HirTableField::Record(_) => None,
    }))
}

fn array_fields_contain_uncertain_value(fields: &[HirTableField]) -> bool {
    fields.iter().any(|field| {
        matches!(
            field,
            HirTableField::Array(value) if !value_facts(value).is_non_nil()
        )
    })
}

fn table_field_contains_nil(field: &HirTableField) -> bool {
    match field {
        HirTableField::Array(value) => expr_contains_nil(value),
        HirTableField::Record(record) => {
            expr_contains_nil(&record.key) || expr_contains_nil(&record.value)
        }
    }
}

fn expr_contains_nil(expr: &HirExpr) -> bool {
    crate::hir::visit::any_expr(expr, &mut |expr| matches!(expr, HirExpr::Nil))
}
