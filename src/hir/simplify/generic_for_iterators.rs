//! 把 generic-for 的 VM 初始化序列收回完整 source value pack。
//!
//! Lua 5.4+ 除 iterator/state/control 外还会物化第 4 个 closing value；前置固定表达式
//! 与最终多返回调用又可能拆成多条赋值。这里优先按 GenericFor 已记录的完整源码 pack
//! 一次接管初始化序列；若 closing value 已经更早求值，则只额外收回紧邻循环头的匿名
//! 单次 `nil` run，不跨语句移动其它表达式。
//!
//! 输入：`t0 = next; t1,t2,t3 = factory()<exact:3>; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(next, factory()<open>)`
//! 输入：`t1,t2 = nil,nil; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(t0,nil,nil,t3)`
//! direct closure producer 保留为独立 local function；child proto 的体量无法由 HIR
//! 表达式复杂度概括，不应恢复成 loop head 内的多行匿名函数。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirGenericForInitializerProducerId, HirLValue, HirProto,
    HirStmt, HirValuePack, LocalId, ParamId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::{
    collect_temp_use_counts, stmts_reference_captured_bindings, stmts_value_captured_bindings,
};
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

pub(super) fn fold_generic_for_iterators_in_proto(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let reference_capture_homes = iterator_reference_capture_homes(&proto.body, facts);
    let tbc_protected_homes = iterator_tbc_protected_homes(&proto.body, facts);
    let physical_root_bindings = iterator_physical_root_bindings(proto);
    let debug_temps = proto
        .temp_debug_locals
        .iter()
        .map(Option::is_some)
        .collect();
    let preserved_temps = (0..proto.temp_count)
        .map(TempId)
        .filter(|temp| proto.inline_dispositions.temp(*temp).must_preserve())
        .collect();
    rewrite_proto(
        proto,
        &mut GenericForIteratorPass {
            use_counts,
            reference_capture_homes,
            tbc_protected_homes,
            physical_root_bindings,
            debug_temps,
            preserved_temps,
            facts,
        },
    )
}

struct GenericForIteratorPass<'a> {
    use_counts: BTreeMap<TempId, usize>,
    reference_capture_homes: BTreeSet<HomeSlotKey>,
    tbc_protected_homes: BTreeSet<HomeSlotKey>,
    physical_root_bindings: BTreeSet<DirectBinding>,
    debug_temps: Vec<bool>,
    preserved_temps: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
}

impl HirRewritePass for GenericForIteratorPass<'_> {
    const PRESERVES_GENERIC_FOR_INITIALIZER_TRANSACTION: bool = true;

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        let HirStmt::GenericFor(generic_for) = stmt else {
            return false;
        };
        trim_trailing_nil_iterators(&mut generic_for.iterator)
    }

    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut pending = VecDeque::from(old_stmts);
        let mut new_stmts = Vec::with_capacity(pending.len());
        let mut changed = false;

        while !pending.is_empty() {
            if fold_adjacent_nil_iterators(&mut pending, self, &mut new_stmts) {
                changed = true;
            } else if let Some(plan) = fold_plan(pending.make_contiguous(), self) {
                fold_front(&mut pending, plan, &mut new_stmts);
                changed = true;
            } else {
                new_stmts.push(
                    pending
                        .pop_front()
                        .expect("non-empty generic-for scan queue"),
                );
            }
        }

        block.stmts = new_stmts;
        changed
    }
}

fn trim_trailing_nil_iterators(iterator: &mut HirValuePack) -> bool {
    // 候选拒绝[SemanticBarrier:ValueArity]：`for _ in nil, f() do` 的 fixed nil 位于 open tail 前，删除会把 iterator/state 位置左移。
    if iterator.tail.is_some() {
        return false;
    }
    let original_len = iterator.fixed.len();
    while iterator.fixed.len() > 1 && matches!(iterator.fixed.last(), Some(HirExpr::Nil)) {
        iterator.fixed.pop();
    }
    iterator.fixed.len() != original_len
}

fn fold_adjacent_nil_iterators(
    pending: &mut VecDeque<HirStmt>,
    context: &GenericForIteratorPass<'_>,
    new_stmts: &mut Vec<HirStmt>,
) -> bool {
    let (iterator_start, value_count, producer_id) = {
        let stmts = pending.make_contiguous();
        let (Some(HirStmt::Assign(assign)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.first(), stmts.get(1))
        else {
            return false;
        };
        let value_count = assign.targets.len();
        // exact-width tail 也能给出目标数，但 fixed 为空；这里只接受逐项可核验的 nil。
        if value_count == 0
            || assign.values.tail.is_some()
            || assign.values.fixed.len() != value_count
            || !assign
                .values
                .fixed
                .iter()
                .all(|value| matches!(value, HirExpr::Nil))
        {
            return false;
        }
        let value_capture_homes = iterator_value_capture_homes(&stmts[1..], context.facts);
        let Some(producer_id) = assign.generic_for_initializer_producer else {
            return false;
        };
        let Some(span) = generic_for
            .initializer_transaction
            .as_ref()
            .filter(|transaction| transaction.id == producer_id.transaction())
            .and_then(|transaction| {
                transaction
                    .producers
                    .iter()
                    .find(|span| span.producer == producer_id)
            })
        else {
            return false;
        };
        if !producer_matches_iterator_span(assign, generic_for, span) {
            return false;
        }
        if !assign.targets.iter().all(|target| {
            let HirLValue::Temp(temp) = target else {
                return false;
            };
            iterator_target_can_be_deleted(*temp, &value_capture_homes, context)
        }) {
            return false;
        }
        (span.value_start, value_count, producer_id)
    };

    let Some(HirStmt::Assign(_)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for nil assignment");
    };
    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for owner");
    };
    generic_for.iterator.fixed[iterator_start..iterator_start + value_count].fill(HirExpr::Nil);
    consume_initializer_producers(&mut generic_for, [producer_id]);
    trim_trailing_nil_iterators(&mut generic_for.iterator);
    new_stmts.push(HirStmt::GenericFor(generic_for));
    true
}

#[derive(Clone, Copy)]
struct FoldPlan {
    assignment_count: usize,
    gap_count: usize,
}

fn fold_plan(stmts: &[HirStmt], context: &GenericForIteratorPass<'_>) -> Option<FoldPlan> {
    let transaction = match stmts.first() {
        Some(HirStmt::Assign(assign)) => assign.generic_for_initializer_producer?.transaction(),
        _ => return None,
    };
    let mut gap_fallback = None;
    for assignment_count in 1..stmts.len() {
        let Some(HirStmt::Assign(assign)) = stmts.get(assignment_count - 1) else {
            return gap_fallback;
        };
        if assign
            .generic_for_initializer_producer
            .is_none_or(|producer| producer.transaction() != transaction)
        {
            return gap_fallback;
        }
        let assignments = &stmts[..assignment_count];
        if let Some(HirStmt::GenericFor(generic_for)) = stmts.get(assignment_count) {
            let value_capture_homes =
                iterator_value_capture_homes(&stmts[assignment_count..], context.facts);
            return assignments_match_iterator(
                assignments,
                generic_for,
                &value_capture_homes,
                context,
            )
            .then_some(FoldPlan {
                assignment_count,
                gap_count: 0,
            })
            .or(gap_fallback);
        }
        if let (Some(gap @ HirStmt::Assign(_)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.get(assignment_count), stmts.get(assignment_count + 1))
        {
            let value_capture_homes =
                iterator_value_capture_homes(&stmts[assignment_count..], context.facts);
            if !assignments_match_iterator(assignments, generic_for, &value_capture_homes, context)
            {
                continue;
            }
            if iterator_pack_can_cross_assignment(assignments, gap, context) {
                gap_fallback.get_or_insert(FoldPlan {
                    assignment_count,
                    gap_count: 1,
                });
            }
            // The gap may itself be the next protocol producer. Prefer the larger adjacent
            // transaction; retain a proven reorder only as fallback if that match fails.
            continue;
        }
    }
    gap_fallback
}

// 跨 gap 比相邻折叠多一次求值重排。稳定标量的求值没有 user-code effect；只要 producer、
// gap 的直接读写 home 两两满足依赖顺序，就可以保留 gap 并把 iterator pack 延后到 loop head。
fn iterator_pack_can_cross_assignment(
    assignments: &[HirStmt],
    gap: &HirStmt,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    let HirStmt::Assign(gap) = gap else {
        return false;
    };
    if gap
        .values
        .tail
        .as_ref()
        .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：open/exact call gap 可执行 user code；iterator 求值跨过它会颠倒 producer 与 call 的事件顺序。
        return false;
    }

    let gap_targets = match direct_target_locations(&gap.targets, context.facts) {
        Ok(locations) => locations,
        Err(LocationFactError::Observable) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：upvalue/global/table 左值可执行 user code 或改变 loop head 可观察状态，iterator 求值不能跨过它。
            return false;
        }
        Err(LocationFactError::DeferredDecision | LocationFactError::DiagnosticResidual) => {
            unreachable!("lvalue cannot be an expression residual")
        }
    };
    let gap_sources = match stable_value_locations(&gap.values.fixed, context.facts) {
        Ok(locations) => locations,
        Err(LocationFactError::Observable) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：call、lookup、closure 或运算表达式跨 iterator producer 可执行 user code/读取可变状态；这里只移动字面量和可信直接 binding。
            return false;
        }
        Err(LocationFactError::DeferredDecision) => {
            // 候选拒绝[LayerBoundary]：Decision 由 decision/eliminate owner 原位物化；
            // owner 会 invalidates TempChain/BlockStructure，二者都是本 pass 的
            // scheduler dependency，因此物化后候选会被真实重审。
            return false;
        }
        Err(LocationFactError::DiagnosticResidual) => {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据，
            // 不把它埋入普通 iterator 表达式。
            return false;
        }
    };

    let mut iterator_targets = BindingLocations::default();
    let mut iterator_sources = BindingLocations::default();
    for stmt in assignments {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign
            .values
            .tail
            .as_ref()
            .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
        {
            // 候选拒绝[SemanticBarrier:EvalOrder]：`factory()<exact:N>; gap; for ...` 合并后会把 factory call 延迟到 gap 后；factory 可观察 gap 前后的状态。
            return false;
        }
        let Ok(targets) = direct_target_locations(&assign.targets, context.facts) else {
            return false;
        };
        iterator_targets.extend(targets);
        let sources = match stable_value_locations(&assign.values.fixed, context.facts) {
            Ok(locations) => locations,
            Err(LocationFactError::Observable) => {
                // 候选拒绝[SemanticBarrier:EvalOrder]：可观察 iterator RHS 延迟到 gap 后会重排 call/lookup/metamethod；只接纳字面量和可信直接 binding。
                return false;
            }
            Err(LocationFactError::DeferredDecision) => {
                // 候选拒绝[LayerBoundary]：Decision 交给 decision/eliminate owner 原位物化；
                // owner 会 invalidates 本 pass 依赖的 TempChain/BlockStructure，
                // 物化后会重审该 producer/gap 候选。
                return false;
            }
            Err(LocationFactError::DiagnosticResidual) => {
                // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
                return false;
            }
        };
        iterator_sources.extend(sources);
    }

    let dependency = locations_are_disjoint(&iterator_targets, &gap_targets)
        .and(locations_are_disjoint(&iterator_sources, &gap_targets))
        .and(locations_are_disjoint(&iterator_targets, &gap_sources));
    match dependency {
        LocationDisjointness::Proven => true,
        LocationDisjointness::Overlap => {
            // 候选拒绝[SemanticBarrier:ValueFlow]：gap 若读写 iterator
            // source/target 的同一 binding 或 possible home，延迟 producer 会改变
            // gap 快照或 loop 输入。Unknown provenance 已展开为完整 physical-home
            // universe，不再以缺事实状态永久拒绝。
            false
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum DirectBinding {
    Param(ParamId),
    Local(LocalId),
    Temp(TempId),
}

#[derive(Default)]
struct BindingLocations {
    bindings: BTreeSet<DirectBinding>,
    physical_homes: BTreeSet<HomeSlotKey>,
}

impl BindingLocations {
    fn insert(&mut self, binding: DirectBinding, facts: &ProtoPromotionFacts) {
        self.bindings.insert(binding);
        let homes = match binding {
            DirectBinding::Param(param) => facts.complete_param_home_slots(param),
            DirectBinding::Local(local) => facts.complete_local_home_slots(local),
            DirectBinding::Temp(temp) => facts.complete_temp_home_slots(temp),
        };
        self.physical_homes.extend(homes.iter().copied());
    }

    fn extend(&mut self, other: Self) {
        self.bindings.extend(other.bindings);
        self.physical_homes.extend(other.physical_homes);
    }
}

fn iterator_reference_capture_homes(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    stmts_reference_captured_bindings(&block.stmts).complete_home_slots(facts)
}

fn iterator_tbc_protected_homes(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut homes = BTreeSet::new();
    struct TbcHomeCollector<'a> {
        homes: &'a mut BTreeSet<HomeSlotKey>,
        facts: &'a ProtoPromotionFacts,
    }

    impl HirVisitor for TbcHomeCollector<'_> {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            let HirStmt::ToBeClosed(tbc) = stmt else {
                return;
            };
            let mut collector = BindingLocationCollector {
                locations: BindingLocations::default(),
                facts: self.facts,
            };
            visit_expr(&tbc.value, &mut collector);
            self.homes.extend(collector.locations.physical_homes);
        }
    }

    visit_stmts(
        &block.stmts,
        &mut TbcHomeCollector {
            homes: &mut homes,
            facts,
        },
    );
    homes
}

fn iterator_value_capture_homes(
    stmts_after_producer: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    stmts_value_captured_bindings(stmts_after_producer).complete_home_slots(facts)
}

fn iterator_physical_root_bindings(proto: &HirProto) -> BTreeSet<DirectBinding> {
    let mut materialized = MaterializedBindingCollector::default();
    visit_stmts(&proto.body.stmts, &mut materialized);
    proto
        .physical_root_locals
        .iter()
        .copied()
        .map(DirectBinding::Local)
        .chain(
            proto
                .physical_root_temps
                .iter()
                .copied()
                .map(DirectBinding::Temp),
        )
        .filter(|binding| materialized.bindings.contains(binding))
        .collect()
}

#[derive(Default)]
struct MaterializedBindingCollector {
    bindings: BTreeSet<DirectBinding>,
}

impl HirVisitor for MaterializedBindingCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                self.bindings
                    .extend(decl.bindings.iter().copied().map(DirectBinding::Local));
            }
            HirStmt::NumericFor(numeric_for) => {
                self.bindings
                    .insert(DirectBinding::Local(numeric_for.binding));
            }
            HirStmt::GenericFor(generic_for) => {
                self.bindings.extend(
                    generic_for
                        .bindings
                        .iter()
                        .copied()
                        .map(DirectBinding::Local),
                );
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Local(local) => {
                self.bindings.insert(DirectBinding::Local(*local));
            }
            HirLValue::Temp(temp) => {
                self.bindings.insert(DirectBinding::Temp(*temp));
            }
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => {}
        }
    }
}

#[derive(Clone, Copy)]
enum LocationFactError {
    Observable,
    DeferredDecision,
    DiagnosticResidual,
}

fn direct_target_locations(
    targets: &[HirLValue],
    facts: &ProtoPromotionFacts,
) -> Result<BindingLocations, LocationFactError> {
    let mut locations = BindingLocations::default();
    for target in targets {
        let binding = match target {
            HirLValue::Param(param) => DirectBinding::Param(*param),
            HirLValue::Local(local) => DirectBinding::Local(*local),
            HirLValue::Temp(temp) => DirectBinding::Temp(*temp),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                return Err(LocationFactError::Observable);
            }
        };
        locations.insert(binding, facts);
    }
    Ok(locations)
}

fn stable_value_locations(
    values: &[HirExpr],
    facts: &ProtoPromotionFacts,
) -> Result<BindingLocations, LocationFactError> {
    let mut locations = BindingLocations::default();
    for value in values {
        let binding = match value {
            HirExpr::ParamRef(param) => Some(DirectBinding::Param(*param)),
            HirExpr::LocalRef(local) => Some(DirectBinding::Local(*local)),
            HirExpr::TempRef(temp) => Some(DirectBinding::Temp(*temp)),
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::Vector(_)
            | HirExpr::UpvalueRef(_) => None,
            HirExpr::Decision(_) => return Err(LocationFactError::DeferredDecision),
            HirExpr::Unresolved(_) => return Err(LocationFactError::DiagnosticResidual),
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Call(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_) => return Err(LocationFactError::Observable),
        };
        if let Some(binding) = binding {
            locations.insert(binding, facts);
        }
    }
    Ok(locations)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LocationDisjointness {
    Proven,
    Overlap,
}

impl LocationDisjointness {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Overlap, _) | (_, Self::Overlap) => Self::Overlap,
            (Self::Proven, Self::Proven) => Self::Proven,
        }
    }
}

fn locations_are_disjoint(
    left: &BindingLocations,
    right: &BindingLocations,
) -> LocationDisjointness {
    if !left.bindings.is_disjoint(&right.bindings)
        || !left.physical_homes.is_disjoint(&right.physical_homes)
    {
        return LocationDisjointness::Overlap;
    }
    LocationDisjointness::Proven
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ProducerFlowFailure {
    TargetOverlap,
    SourceOverlap,
}

fn iterator_assignments_preserve_value_flow(
    assignments: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> Result<(), ProducerFlowFailure> {
    let mut prior_targets = BindingLocations::default();
    for stmt in assignments {
        let HirStmt::Assign(assign) = stmt else {
            unreachable!("generic-for producer flow only receives assignments");
        };
        let mut current_targets = BindingLocations::default();
        for target in &assign.targets {
            let Ok(target) = direct_target_locations(std::slice::from_ref(target), facts) else {
                unreachable!("matched generic-for producer targets are direct temps");
            };
            let target_dependency = locations_are_disjoint(&prior_targets, &target)
                .and(locations_are_disjoint(&current_targets, &target));
            match target_dependency {
                LocationDisjointness::Proven => {}
                LocationDisjointness::Overlap => {
                    return Err(ProducerFlowFailure::TargetOverlap);
                }
            }
            current_targets.extend(target);
        }

        let sources = value_pack_binding_locations(&assign.values, facts);
        match locations_are_disjoint(&prior_targets, &sources) {
            LocationDisjointness::Proven => {}
            LocationDisjointness::Overlap => return Err(ProducerFlowFailure::SourceOverlap),
        }
        prior_targets.extend(current_targets);
    }
    Ok(())
}

fn value_pack_binding_locations(
    values: &HirValuePack,
    facts: &ProtoPromotionFacts,
) -> BindingLocations {
    let mut collector = BindingLocationCollector {
        locations: BindingLocations::default(),
        facts,
    };
    for value in &values.fixed {
        visit_expr(value, &mut collector);
    }
    if let Some(tail) = &values.tail {
        visit_expr(tail.as_expr(), &mut collector);
    }
    collector.locations
}

struct BindingLocationCollector<'a> {
    locations: BindingLocations,
    facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for BindingLocationCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let binding = match expr {
            HirExpr::ParamRef(param) => Some(DirectBinding::Param(*param)),
            HirExpr::LocalRef(local) => Some(DirectBinding::Local(*local)),
            HirExpr::TempRef(temp) => Some(DirectBinding::Temp(*temp)),
            _ => None,
        };
        if let Some(binding) = binding {
            self.locations.insert(binding, self.facts);
        }
    }
}

fn assignments_match_iterator(
    assignments: &[HirStmt],
    generic_for: &HirGenericFor,
    value_capture_homes: &BTreeSet<HomeSlotKey>,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    let Some(transaction) = &generic_for.initializer_transaction else {
        return false;
    };
    let mut protocol_prefix_width = 0;
    for (index, (stmt, producer)) in assignments.iter().zip(&transaction.producers).enumerate() {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign.generic_for_initializer_producer != Some(producer.producer)
            || producer.producer.transaction() != transaction.id
            || producer.value_start != protocol_prefix_width
            || !producer_matches_iterator_span(assign, generic_for, producer)
        {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：target 之后的 fixed RHS 仍会求值但不占赋值槽；直接拼进 loop pack 会占据并移动后续 protocol 槽。
        if assign.values.fixed.len() > assign.targets.len() {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：非末尾 open tail 在源码列表中会被后续表达式截成单值；两个 tail 也不能保持各自的展开边界。
        if assign.values.tail.is_some()
            && (index + 1 != assignments.len() || generic_for.iterator.tail.is_some())
        {
            return false;
        }
        if assign
            .values
            .tail
            .as_ref()
            .and_then(|tail| tail.exact_width())
            .is_some_and(|width| assign.values.fixed.len() + width != assign.targets.len())
        {
            // 候选拒绝[SemanticBarrier:ValueArity]：原 assignment 会把 exact tail 截到
            // target arity；若证书已陈旧或 pack 宽度不符，改成 open tail 会重新暴露原本
            // 被截掉的返回值，或丢失原本补 nil 的结果。
            return false;
        }
        // 候选拒绝[PolicyBoundary]：closure producer 保留命名 binding，避免把完整 child body 压成 loop head 内的多行 IIFE。
        if assign
            .values
            .fixed
            .iter()
            .any(|value| matches!(value, HirExpr::Closure(_)))
        {
            return false;
        }
        for target in &assign.targets {
            let HirLValue::Temp(output) = target else {
                return false;
            };
            if !iterator_target_can_be_deleted(*output, value_capture_homes, context) {
                return false;
            }
        }
        protocol_prefix_width += assign.targets.len();
    }
    if assignments.len() > transaction.producers.len() {
        return false;
    }
    let has_remaining_protocol_values = protocol_prefix_width < transaction.iterator_width;
    if assignments
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::Assign(assign) if assign.values.tail.is_some()))
        && has_remaining_protocol_values
    {
        // 候选拒绝[SemanticBarrier:ValueArity]：open tail 必须位于 source value list
        // 末尾；若 protocol 仍有 fixed 后缀，把 exact tail 转成 open 后会吞掉这些槽位。
        return false;
    }
    match iterator_assignments_preserve_value_flow(assignments, context.facts) {
        Ok(()) => true,
        Err(ProducerFlowFailure::TargetOverlap) => {
            // 候选拒绝[SemanticBarrier:ValueFlow]：两个 producer target 若是同一 binding/exact home，原 loop 的两个 TempRef 都读最终覆盖值；合并 pack 会分别保留两个 RHS。
            false
        }
        Err(ProducerFlowFailure::SourceOverlap) => {
            // 候选拒绝[SemanticBarrier:ValueFlow]：后续 producer RHS 读取先前 target 的同一 binding/exact home 时，删除中间写会让它改读覆盖前的旧值。
            false
        }
    }
}

fn producer_matches_iterator_span(
    assign: &crate::hir::common::HirAssign,
    generic_for: &HirGenericFor,
    span: &crate::hir::common::HirGenericForInitializerSpan,
) -> bool {
    if span.value_count != assign.targets.len() {
        return false;
    }
    let Some(iterator_values) = generic_for
        .iterator
        .fixed
        .get(span.value_start..span.value_start + span.value_count)
    else {
        return false;
    };
    assign
        .targets
        .iter()
        .zip(iterator_values)
        .all(|(target, value)| {
            matches!((target, value), (HirLValue::Temp(target), HirExpr::TempRef(value)) if target == value)
        })
}

fn iterator_target_can_be_deleted(
    target: TempId,
    value_capture_homes: &BTreeSet<HomeSlotKey>,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    // 候选拒绝[SemanticBarrier:ValueFlow]：producer target 的额外读取仍需原 materialization；regress_343 的 loop 后 live-out 会变成未定义值。
    if context.use_counts.get(&target) != Some(&1) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:DebugScope]：debug.getlocal 可观察 source iterator/state/control 的词法身份；见 regress_343。
    if context
        .debug_temps
        .get(target.index())
        .copied()
        .unwrap_or(false)
    {
        return false;
    }
    if context.preserved_temps.contains(&target) {
        // 候选拒绝[LayerBoundary]：iterator fold 会删除 producer definition；HIR 已证明
        // 必须保留的 target 只能由理解该 disposition 的后续事务处理。
        return false;
    }
    let target_homes = context.facts.complete_temp_home_slots(target);
    if iterator_target_has_root_lifetime(target, &target_homes, context)
        || !target_homes.is_disjoint(&context.tbc_protected_homes)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：producer 的 raw home 若自身或经
        // different-binding alias 承担 PhysicalRoot，折入 loop header 会提前结束那份
        // 独立强引用。scope-end copy-root 本身不构成 blanket 拒绝：若当前 target 尚未被
        // 物化为 PhysicalRoot，折叠会把同一值原子转移给 GenericFor 的隐藏协议槽；一旦
        // 已有其它 root owner 把 binding 物化进集合，这里仍按实际 binding/home 拒绝。
        // TBC raw slot 仍必须保留原值到 `__close`；其间 GC/finalizer/cleanup 可观察差异。
        return false;
    }
    if !target_homes.is_disjoint(&context.reference_capture_homes)
        || !target_homes.is_disjoint(value_capture_homes)
    {
        // 候选拒绝[SemanticBarrier:Capture]：删除 producer 写会改变同
        // possible home 的 ByReference capture 或 producer 后 ByValue snapshot 所观察
        // 的值。直接 target capture 由 use-count
        // 拦截，这里覆盖 different-binding home alias；producer 前已完成的 ByValue
        // snapshot 不在后缀集合中，因此不会制造 proto-wide blanket 拒绝。
        return false;
    }
    true
}

fn iterator_target_has_root_lifetime(
    target: TempId,
    target_homes: &BTreeSet<HomeSlotKey>,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    context.physical_root_bindings.iter().any(|binding| {
        let mut locations = BindingLocations::default();
        locations.insert(*binding, context.facts);
        *binding == DirectBinding::Temp(target)
            || !target_homes.is_disjoint(&locations.physical_homes)
    })
}

fn fold_front(pending: &mut VecDeque<HirStmt>, plan: FoldPlan, new_stmts: &mut Vec<HirStmt>) {
    let mut iterator = HirValuePack::default();
    let mut consumed_protocol_values = 0;
    let mut consumed_producers = Vec::with_capacity(plan.assignment_count);
    for _ in 0..plan.assignment_count {
        let HirStmt::Assign(assign) = pending
            .pop_front()
            .expect("validated generic-for init assignment")
        else {
            unreachable!("fold plan only counts assignments");
        };
        consumed_producers.push(
            assign
                .generic_for_initializer_producer
                .expect("validated generic-for producer token"),
        );
        let target_count = assign.targets.len();
        consumed_protocol_values += target_count;
        let fixed_count = assign.values.fixed.len();
        iterator.fixed.extend(assign.values.fixed);
        if let Some(tail) = assign.values.tail {
            iterator.tail = Some(tail.into_open());
        } else {
            iterator.fixed.resize(
                iterator.fixed.len() + target_count - fixed_count,
                HirExpr::Nil,
            );
        }
    }

    for _ in 0..plan.gap_count {
        new_stmts.push(
            pending
                .pop_front()
                .expect("validated generic-for assignment gap"),
        );
    }

    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated generic-for owner");
    };
    if iterator.tail.is_none() {
        iterator
            .fixed
            .extend(generic_for.iterator.fixed.drain(consumed_protocol_values..));
        iterator.tail = generic_for.iterator.tail.take();
    } else {
        assert!(
            generic_for.iterator.fixed.len() == consumed_protocol_values
                && generic_for.iterator.tail.is_none(),
            "validated open-tail fold must consume the complete generic-for pack"
        );
    }
    trim_trailing_nil_iterators(&mut iterator);
    generic_for.iterator = iterator;
    consume_initializer_producers(&mut generic_for, consumed_producers);
    new_stmts.push(HirStmt::GenericFor(generic_for));
}

fn consume_initializer_producers(
    generic_for: &mut HirGenericFor,
    consumed: impl IntoIterator<Item = HirGenericForInitializerProducerId>,
) {
    let consumed = consumed.into_iter().collect::<BTreeSet<_>>();
    let Some(transaction) = &mut generic_for.initializer_transaction else {
        return;
    };
    transaction
        .producers
        .retain(|span| !consumed.contains(&span.producer));
    if transaction.producers.is_empty() {
        generic_for.initializer_transaction = None;
    }
}
