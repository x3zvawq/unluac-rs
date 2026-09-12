//! 这个子模块负责 table-constructor pass 里的 binding 识别与使用索引。
//!
//! 它依赖 HIR 已经分好的 lvalue/expr 形状，回答“这个读写是不是同一个构造器绑定”，
//! 并用稳定 stmt id 索引 binding 的 use/mention 位置；不会扫描候选 region 或重建字段序列。
//! 例如：`t[k] = v` 会在这里识别 `t` 的绑定身份，并把 `k` 作为普通语义表达式统计；
//! 键最终能否写成 `name = value` 不属于 HIR binding facts。
//! capture 从类型化父级身份投影到构造器的 Temp/Local 域，两种捕获模式均保留物化依赖。
//! 物化次数消费共享逻辑写事件；捕获集合独立累积，不把 root release 当作物理槽覆盖。
//! 同一遍访问区分普通值观察与直接写 base / 单值 return；仅后两类 occurrence 不会提前
//! 暴露新表。`t.x=f(t)` 的 RHS 仍是观察，capture 和同 home 的源码身份由原索引继续保护。

use std::collections::BTreeSet;
use std::ops::Bound::{Excluded, Unbounded};

use crate::hir::common::{HirBinding, HirCapture, HirExpr, HirLValue, HirStmt};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::super::mention::BindingWriteCollector;
use super::{BindingId, TableBinding};
use crate::hir::visit::{HirVisitor, visit_block, visit_stmts};

pub(super) fn binding_from_lvalue(lvalue: &HirLValue) -> Option<TableBinding> {
    HirBinding::from_lvalue(lvalue).and_then(binding_from_identity)
}

pub(super) fn binding_from_expr(expr: &HirExpr) -> Option<TableBinding> {
    HirBinding::from_expr(expr).and_then(binding_from_identity)
}

pub(super) fn binding_from_identity(binding: HirBinding) -> Option<TableBinding> {
    match binding {
        HirBinding::Temp(temp) => Some(TableBinding::Temp(temp)),
        HirBinding::Local(local) => Some(TableBinding::Local(local)),
        HirBinding::Param(_) | HirBinding::Upvalue(_) => None,
    }
}

pub(super) fn matches_binding_ref(expr: &HirExpr, binding: TableBinding) -> bool {
    binding_from_expr(expr) == Some(binding)
}

pub(super) struct BindingFacts {
    pub(super) materialized: BindingSlots<u32>,
    pub(super) reference_captured: BindingSlots<bool>,
    pub(super) reference_captured_home_slots: BTreeSet<HomeSlotKey>,
    pub(super) observed_before_exit: BindingSlots<bool>,
}

fn binding_home_slot(
    binding: TableBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match binding {
        TableBinding::Temp(temp) => promotion_facts.home_slot(temp),
        TableBinding::Local(local) => promotion_facts.local_home_slot(local),
    }
}

pub(super) fn collect_binding_facts(
    block: &crate::hir::common::HirBlock,
    promotion_facts: &ProtoPromotionFacts,
    temp_count: usize,
    local_count: usize,
) -> BindingFacts {
    let mut materialized = BindingSlots::new(temp_count, local_count);
    let collector = BindingCaptureCollector {
        promotion_facts,
        reference_captured: BindingSlots::new(temp_count, local_count),
        reference_captured_home_slots: BTreeSet::new(),
        observed_before_exit: BindingSlots::new(temp_count, local_count),
        private_occurrences: BTreeSet::new(),
    };
    let mut pair = (
        BindingWriteCollector(|binding| {
            if let Some(binding) = binding_from_identity(binding) {
                increment_materialized_count(&mut materialized, binding);
            }
        }),
        collector,
    );
    visit_block(block, &mut pair);
    let collector = pair.1;
    BindingFacts {
        materialized,
        reference_captured: collector.reference_captured,
        reference_captured_home_slots: collector.reference_captured_home_slots,
        observed_before_exit: collector.observed_before_exit,
    }
}

#[derive(Debug, Clone)]
pub(super) struct BindingSlots<T> {
    temps: Vec<T>,
    locals: Vec<T>,
    temp_limit: usize,
    local_limit: usize,
}

impl<T> BindingSlots<T> {
    fn new(temp_limit: usize, local_limit: usize) -> Self {
        Self {
            temps: Vec::new(),
            locals: Vec::new(),
            temp_limit,
            local_limit,
        }
    }

    pub(super) fn get(&self, binding: TableBinding) -> Option<&T> {
        match binding {
            TableBinding::Temp(temp) => self.temps.get(temp.index()),
            TableBinding::Local(local) => self.locals.get(local.index()),
        }
    }

    fn get_mut_or_default(&mut self, binding: TableBinding) -> &mut T
    where
        T: Default,
    {
        let (slots, index, limit) = match binding {
            TableBinding::Temp(temp) => (&mut self.temps, temp.index(), self.temp_limit),
            TableBinding::Local(local) => (&mut self.locals, local.index(), self.local_limit),
        };
        assert!(
            index < limit,
            "table-constructor binding must belong to its proto"
        );
        if slots.len() <= index {
            slots.resize_with(index + 1, T::default);
        }
        &mut slots[index]
    }
}

impl BindingSlots<bool> {
    pub(super) fn from_debug_hints(
        temp_hints: &[Option<String>],
        local_hints: &[Option<String>],
    ) -> Self {
        Self {
            temps: temp_hints.iter().map(Option::is_some).collect(),
            locals: local_hints.iter().map(Option::is_some).collect(),
            temp_limit: temp_hints.len(),
            local_limit: local_hints.len(),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct BindingIndex {
    ids: BindingSlots<Option<BindingId>>,
    bindings: Vec<TableBinding>,
}

impl BindingIndex {
    pub(super) fn new(temp_count: usize, local_count: usize) -> Self {
        Self {
            ids: BindingSlots::new(temp_count, local_count),
            bindings: Vec::new(),
        }
    }

    pub(super) fn intern(&mut self, binding: TableBinding) -> BindingId {
        if let Some(id) = self.id_of(binding) {
            return id;
        }
        let id = self.bindings.len();
        *self.ids.get_mut_or_default(binding) = Some(id);
        self.bindings.push(binding);
        id
    }

    pub(super) fn id_of(&self, binding: TableBinding) -> Option<BindingId> {
        self.ids.get(binding).copied().flatten()
    }

    pub(super) fn len(&self) -> usize {
        self.bindings.len()
    }

    pub(super) fn materialized_counts(&self, counts: &BindingSlots<u32>) -> Vec<u32> {
        self.bindings
            .iter()
            .map(|binding| counts.get(*binding).copied().unwrap_or_default())
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct StmtBindingSummary {
    uses: Vec<BindingId>,
    mentions: Vec<BindingId>,
}

impl StmtBindingSummary {
    pub(super) fn uses(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.uses.iter().copied()
    }

    fn mentions(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.mentions.iter().copied()
    }
}

pub(super) fn collect_stmt_binding_summary(
    stmt: &HirStmt,
    binding_index: &mut BindingIndex,
) -> StmtBindingSummary {
    intern_stmt_bindings(stmt, binding_index);
    collect_stmt_slice_binding_summary(std::slice::from_ref(stmt), binding_index)
}

pub(super) fn intern_stmt_bindings(stmt: &HirStmt, binding_index: &mut BindingIndex) {
    match stmt {
        HirStmt::LocalRootRelease(local) => {
            binding_index.intern(TableBinding::Local(*local));
        }
        HirStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                binding_index.intern(TableBinding::Local(*binding));
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                if let Some(binding) = binding_from_lvalue(target) {
                    binding_index.intern(binding);
                }
            }
        }
        HirStmt::NumericFor(numeric_for) => {
            binding_index.intern(TableBinding::Local(numeric_for.binding));
        }
        HirStmt::GenericFor(generic_for) => {
            for binding in &generic_for.bindings {
                binding_index.intern(TableBinding::Local(*binding));
            }
        }
        HirStmt::TableSetList(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_) => {}
    }
}

pub(super) fn collect_stmt_slice_binding_summary(
    stmts: &[HirStmt],
    binding_index: &mut BindingIndex,
) -> StmtBindingSummary {
    let mut collector = BindingUseCollector {
        binding_index,
        uses: Vec::new(),
        mentions: Vec::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.uses.sort_unstable();
    collector.uses.dedup();
    collector.mentions.sort_unstable();
    collector.mentions.dedup();
    StmtBindingSummary {
        uses: collector.uses,
        mentions: collector.mentions,
    }
}

#[derive(Debug, Clone)]
pub(super) struct BindingOccurrenceIndex {
    uses: Vec<BTreeSet<usize>>,
    mentions: Vec<BTreeSet<usize>>,
    sticky_uses: Vec<bool>,
}

impl BindingOccurrenceIndex {
    pub(super) fn new(
        binding_index: &BindingIndex,
        stmts: &[StmtBindingSummary],
        reference_captured_bindings: &BindingSlots<bool>,
        reference_captured_home_slots: &BTreeSet<HomeSlotKey>,
        debug_identity_bindings: &BindingSlots<bool>,
        promotion_facts: &ProtoPromotionFacts,
    ) -> Self {
        let mut index = Self {
            uses: vec![BTreeSet::new(); binding_index.len()],
            mentions: vec![BTreeSet::new(); binding_index.len()],
            sticky_uses: binding_index
                .bindings
                .iter()
                .map(|binding| {
                    reference_captured_bindings
                        .get(*binding)
                        .copied()
                        .unwrap_or_default()
                        || debug_identity_bindings
                            .get(*binding)
                            .copied()
                            .unwrap_or_default()
                        || binding_home_slot(*binding, promotion_facts)
                            .is_some_and(|slot| reference_captured_home_slots.contains(&slot))
                })
                .collect(),
        };
        for (stmt_id, summary) in stmts.iter().enumerate() {
            for binding_id in summary.uses() {
                index.uses[binding_id].insert(stmt_id);
            }
            for binding_id in summary.mentions() {
                index.mentions[binding_id].insert(stmt_id);
            }
        }
        index
    }

    pub(super) fn remaining_uses_after(&self, stmt_id: usize) -> BindingUseSummary<'_> {
        BindingUseSummary {
            index: self,
            after_stmt: stmt_id,
        }
    }

    pub(super) fn last_use(&self, binding_id: BindingId) -> Option<usize> {
        self.uses
            .get(binding_id)
            .and_then(|occurrences| occurrences.last().copied())
    }

    pub(super) fn has_source_identity(&self, binding_id: BindingId) -> bool {
        self.sticky_uses[binding_id]
    }

    pub(super) fn remove_stmt(&mut self, stmt_id: usize, summary: &StmtBindingSummary) {
        for binding_id in summary.uses() {
            self.uses[binding_id].remove(&stmt_id);
        }
        for binding_id in summary.mentions() {
            self.mentions[binding_id].remove(&stmt_id);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct BindingUseSummary<'a> {
    index: &'a BindingOccurrenceIndex,
    after_stmt: usize,
}

impl BindingUseSummary<'_> {
    pub(super) fn contains(self, binding_id: BindingId) -> bool {
        self.index
            .sticky_uses
            .get(binding_id)
            .copied()
            .unwrap_or_default()
            || self.index.uses.get(binding_id).is_some_and(|occurrences| {
                occurrences
                    .range((Excluded(self.after_stmt), Unbounded))
                    .next()
                    .is_some()
            })
    }
}

struct BindingCaptureCollector<'a> {
    promotion_facts: &'a ProtoPromotionFacts,
    // The table pass must preserve both by-reference cells and by-value snapshots.  A
    // constructor rewrite can otherwise move a declaration before a closure observes it.
    reference_captured: BindingSlots<bool>,
    reference_captured_home_slots: BTreeSet<HomeSlotKey>,
    observed_before_exit: BindingSlots<bool>,
    // 只豁免这一 expression occurrence；同语句 RHS 再读相同 binding 仍然是观察。
    private_occurrences: BTreeSet<usize>,
}

impl HirVisitor<'_> for BindingCaptureCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::TableAccess(access) = target {
                        self.private_occurrences
                            .insert(std::ptr::from_ref(&access.base).addr());
                    }
                }
            }
            HirStmt::TableSetList(batch) => {
                self.private_occurrences
                    .insert(std::ptr::from_ref(&batch.base).addr());
            }
            HirStmt::Return(ret) if ret.values.tail.is_none() && ret.values.fixed.len() == 1 => {
                self.private_occurrences
                    .insert(std::ptr::from_ref(&ret.values.fixed[0]).addr());
            }
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if !self
            .private_occurrences
            .remove(&std::ptr::from_ref(expr).addr())
            && let Some(binding) = binding_from_expr(expr)
        {
            *self.observed_before_exit.get_mut_or_default(binding) = true;
        }
    }

    fn visit_capture(&mut self, capture: &HirCapture) {
        // 两种 capture 都依赖父级物化身份；ByValue 也不能随 producer 删除而变成孤儿。
        if let Some(binding) = binding_from_identity(capture.binding) {
            *self.reference_captured.get_mut_or_default(binding) = true;
            *self.observed_before_exit.get_mut_or_default(binding) = true;
            if let Some(slot) = binding_home_slot(binding, self.promotion_facts) {
                self.reference_captured_home_slots.insert(slot);
            }
        }
    }
}

pub(super) fn expr_uses_binding(expr: &HirExpr, binding: TableBinding) -> bool {
    crate::hir::visit::any_expr(expr, &mut |expr| matches_binding_ref(expr, binding))
}

struct BindingUseCollector<'a> {
    binding_index: &'a mut BindingIndex,
    uses: Vec<BindingId>,
    mentions: Vec<BindingId>,
}

impl HirVisitor<'_> for BindingUseCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::NumericFor(numeric_for) => self.mentions.push(
                self.binding_index
                    .intern(TableBinding::Local(numeric_for.binding)),
            ),
            HirStmt::GenericFor(generic_for) => self.mentions.extend(
                generic_for
                    .bindings
                    .iter()
                    .map(|binding| self.binding_index.intern(TableBinding::Local(*binding))),
            ),
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = binding_from_expr(expr) {
            let binding_id = self.binding_index.intern(binding);
            self.uses.push(binding_id);
            self.mentions.push(binding_id);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = binding_from_lvalue(lvalue) {
            self.mentions.push(self.binding_index.intern(binding));
        }
    }
}

fn increment_materialized_count(counts: &mut BindingSlots<u32>, binding: TableBinding) {
    let count = counts.get_mut_or_default(binding);
    *count = count
        .checked_add(1)
        .expect("table-constructor materialization count must fit u32");
}
