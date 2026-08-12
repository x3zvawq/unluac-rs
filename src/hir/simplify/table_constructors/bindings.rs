//! 这个子模块负责 table-constructor pass 里的 binding 识别与字段键翻译。
//!
//! 它依赖 HIR 已经分好的 lvalue/expr 形状，回答“这个读写是不是同一个构造器绑定”，
//! 并用稳定 stmt id 索引 binding 的 use/mention 位置；不会扫描候选 region 或重建字段序列。
//! 例如：`t.x = v` 会在这里把键翻成 `Name(\"x\")` 并识别 `t` 的绑定身份。

use std::collections::BTreeSet;
use std::ops::Bound::{Excluded, Unbounded};

use crate::ast::{DecompileDialect, is_lua_identifier_name};
use crate::hir::common::{
    HirCallExpr, HirCaptureMode, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableField,
    HirTableKey,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::{BindingId, TableBinding};
use crate::hir::simplify::visit::{HirVisitor, visit_block, visit_stmts};

pub(super) fn binding_from_lvalue(lvalue: &HirLValue) -> Option<TableBinding> {
    match lvalue {
        HirLValue::Temp(temp) => Some(TableBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(TableBinding::Local(*local)),
        HirLValue::Param(_)
        | HirLValue::Upvalue(_)
        | HirLValue::Global(_)
        | HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn binding_from_expr(expr: &HirExpr) -> Option<TableBinding> {
    match expr {
        HirExpr::TempRef(temp) => Some(TableBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(TableBinding::Local(*local)),
        _ => None,
    }
}

pub(super) fn matches_binding_ref(expr: &HirExpr, binding: TableBinding) -> bool {
    binding_from_expr(expr) == Some(binding)
}

pub(super) fn table_key_from_expr(expr: &HirExpr, dialect: DecompileDialect) -> HirTableKey {
    if let HirExpr::String(name) = expr
        && let Some(name) = name.as_utf8()
        && is_lua_identifier_name(name, dialect)
    {
        return HirTableKey::Name(name.to_owned());
    }
    HirTableKey::Expr(expr.clone())
}

pub(super) struct BindingFacts {
    pub(super) materialized: BindingSlots<u32>,
    pub(super) reference_captured: BindingSlots<bool>,
    pub(super) reference_captured_home_slots: BTreeSet<HomeSlotKey>,
}

pub(super) fn collect_binding_facts(
    block: &crate::hir::common::HirBlock,
    promotion_facts: &ProtoPromotionFacts,
    temp_count: usize,
    local_count: usize,
) -> BindingFacts {
    let mut collector = BindingFactCollector {
        promotion_facts,
        materialized: BindingSlots::new(temp_count, local_count),
        reference_captured: BindingSlots::new(temp_count, local_count),
        reference_captured_home_slots: BTreeSet::new(),
    };
    visit_block(block, &mut collector);
    BindingFacts {
        materialized: collector.materialized,
        reference_captured: collector.reference_captured,
        reference_captured_home_slots: collector.reference_captured_home_slots,
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
    fn uses(&self) -> impl Iterator<Item = BindingId> + '_ {
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
                        || matches!(
                            binding,
                            TableBinding::Temp(temp)
                                if promotion_facts.home_slot(*temp).is_some_and(
                                    |slot| reference_captured_home_slots.contains(&slot)
                                )
                        )
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

    pub(super) fn mentions_after(&self, binding_id: BindingId, stmt_id: usize) -> bool {
        self.mentions.get(binding_id).is_some_and(|occurrences| {
            occurrences
                .range((Excluded(stmt_id), Unbounded))
                .next()
                .is_some()
        })
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

struct BindingFactCollector<'a> {
    promotion_facts: &'a ProtoPromotionFacts,
    materialized: BindingSlots<u32>,
    reference_captured: BindingSlots<bool>,
    reference_captured_home_slots: BTreeSet<HomeSlotKey>,
}

impl HirVisitor for BindingFactCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    increment_materialized_count(
                        &mut self.materialized,
                        TableBinding::Local(*binding),
                    );
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let Some(binding) = binding_from_lvalue(target) {
                        increment_materialized_count(&mut self.materialized, binding);
                    }
                }
            }
            HirStmt::NumericFor(numeric_for) => increment_materialized_count(
                &mut self.materialized,
                TableBinding::Local(numeric_for.binding),
            ),
            HirStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    increment_materialized_count(
                        &mut self.materialized,
                        TableBinding::Local(*binding),
                    );
                }
            }
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::Closure(closure) = expr else {
            return;
        };
        for binding in closure
            .captures
            .iter()
            .filter(|capture| capture.mode == HirCaptureMode::ByReference)
            .filter_map(|capture| binding_from_expr(&capture.value))
        {
            *self.reference_captured.get_mut_or_default(binding) = true;
            if let TableBinding::Temp(temp) = binding
                && let Some(slot) = self.promotion_facts.home_slot(temp)
            {
                self.reference_captured_home_slots.insert(slot);
            }
        }
    }
}

pub(super) fn expr_uses_binding(expr: &HirExpr, binding: TableBinding) -> bool {
    if matches_binding_ref(expr, binding) {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        HirExpr::Unary(unary) => expr_uses_binding(&unary.expr, binding),
        HirExpr::Binary(binary) => {
            expr_uses_binding(&binary.lhs, binding) || expr_uses_binding(&binary.rhs, binding)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_uses_binding(&logical.lhs, binding) || expr_uses_binding(&logical.rhs, binding)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_uses_binding(&node.test, binding)
                || decision_target_uses_binding(&node.truthy, binding)
                || decision_target_uses_binding(&node.falsy, binding)
        }),
        HirExpr::Call(call) => call_expr_uses_binding(call, binding),
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_uses_binding(expr, binding),
                HirTableField::Record(field) => {
                    table_key_uses_binding(&field.key, binding)
                        || expr_uses_binding(&field.value, binding)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_uses_binding(&capture.value, binding)),
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
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

pub(super) fn lvalue_uses_binding(lvalue: &HirLValue, binding: TableBinding) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => TableBinding::Temp(*temp) == binding,
        HirLValue::Local(local) => TableBinding::Local(*local) == binding,
        HirLValue::Param(_) => false,
        HirLValue::Upvalue(_) => false,
        HirLValue::Global(_) => false,
        HirLValue::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
    }
}

struct BindingUseCollector<'a> {
    binding_index: &'a mut BindingIndex,
    uses: Vec<BindingId>,
    mentions: Vec<BindingId>,
}

impl HirVisitor for BindingUseCollector<'_> {
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

fn call_expr_uses_binding(call: &HirCallExpr, binding: TableBinding) -> bool {
    expr_uses_binding(&call.callee, binding)
        || call.args.iter().any(|arg| expr_uses_binding(arg, binding))
}

fn decision_target_uses_binding(target: &HirDecisionTarget, binding: TableBinding) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_uses_binding(expr, binding),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_uses_binding(key: &HirTableKey, binding: TableBinding) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_uses_binding(expr, binding),
    }
}
