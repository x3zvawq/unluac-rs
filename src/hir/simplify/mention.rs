//! HIR simplify 里的 binding/temp 提及查询。
//!
//! 多个 pass 都需要回答“某段 HIR 是否还引用某个 local/temp”以及“某条语句是否写入
//! temp”。这些问题属于只读树遍历，不应散落在各个 pass 里各写一套 visitor。
//! 本模块只提供语法树提及事实，不判断 carried-local、branch-value 等业务形状。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirCaptureMode, HirExpr, HirLValue, HirProto, HirStmt, LocalId, ParamId, TempId,
};

use super::visit::{HirVisitor, visit_block, visit_expr, visit_proto, visit_stmts};

pub(super) fn stmts_mention_local(stmts: &[HirStmt], local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_stmts(stmts, local)
}

pub(super) fn block_mentions_local(block: &HirBlock, local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_block(block, local)
}

pub(super) fn expr_mentions_local(expr: &HirExpr, local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_expr(expr, local)
}

pub(super) fn stmt_captures_local(stmt: &HirStmt, local: LocalId) -> bool {
    LocalCaptureCollector::captures_in_stmt(stmt, local)
}

pub(super) fn stmts_captured_locals(stmts: &[HirStmt]) -> BTreeSet<LocalId> {
    let mut collector = CapturedLocalSetCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.locals
}

#[derive(Default)]
pub(super) struct ReferenceCapturedBindings {
    pub(super) locals: BTreeSet<LocalId>,
    pub(super) params: BTreeSet<ParamId>,
    pub(super) temps: BTreeSet<TempId>,
}

pub(super) fn stmts_reference_captured_bindings(stmts: &[HirStmt]) -> ReferenceCapturedBindings {
    let mut collector = ReferenceCaptureCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

/// Collect bindings copied into a closure by value.  Unlike a reference capture, a value
/// capture is a snapshot: a later write to the same physical slot must not be merged back into
/// the captured binding merely because the snapshot has no ordinary expression use.
pub(super) fn stmts_value_captured_bindings(stmts: &[HirStmt]) -> ReferenceCapturedBindings {
    let mut collector = ValueCaptureCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

pub(super) fn stmts_to_be_closed_temps(stmts: &[HirStmt]) -> BTreeSet<TempId> {
    let mut collector = ToBeClosedTempCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.temps
}

/// 收集不能改写成普通 local 状态的词法身份。
///
/// numeric/generic-for binding 和 `<close>` 值都有 VM 级生命周期合同；即使 HIR 中只看见
/// 一条等值赋值，也不能把它们当作普通 carried local。调用方只把这个集合当作保守阻断门。
pub(super) fn stmts_protected_locals(stmts: &[HirStmt]) -> BTreeSet<LocalId> {
    let mut collector = ProtectedLocalCollector::default();
    visit_stmts(stmts, &mut collector);
    collector.locals
}

#[derive(Default)]
struct ProtectedLocalCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor for ProtectedLocalCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::NumericFor(for_stmt) => {
                self.locals.insert(for_stmt.binding);
            }
            HirStmt::GenericFor(for_stmt) => {
                self.locals.extend(for_stmt.bindings.iter().copied());
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                let mut refs = LocalRefSetCollector {
                    locals: &mut self.locals,
                };
                visit_expr(&to_be_closed.value, &mut refs);
            }
            _ => {}
        }
    }
}

#[derive(Default)]
struct ToBeClosedTempCollector {
    temps: BTreeSet<TempId>,
}

impl HirVisitor for ToBeClosedTempCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::ToBeClosed(to_be_closed) = stmt else {
            return;
        };
        if let HirExpr::TempRef(temp) = &to_be_closed.value {
            self.temps.insert(*temp);
        }
    }
}

#[derive(Default)]
struct ReferenceCaptureCollector {
    bindings: ReferenceCapturedBindings,
}

impl HirVisitor for ReferenceCaptureCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::Closure(closure) = expr else {
            return;
        };
        for capture in &closure.captures {
            if capture.mode != HirCaptureMode::ByReference {
                continue;
            }
            let mut collector = BindingRefCollector {
                bindings: &mut self.bindings,
            };
            visit_expr(&capture.value, &mut collector);
        }
    }
}

#[derive(Default)]
struct ValueCaptureCollector {
    bindings: ReferenceCapturedBindings,
}

impl HirVisitor for ValueCaptureCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::Closure(closure) = expr else {
            return;
        };
        for capture in &closure.captures {
            if capture.mode != HirCaptureMode::ByValue {
                continue;
            }
            let mut collector = BindingRefCollector {
                bindings: &mut self.bindings,
            };
            visit_expr(&capture.value, &mut collector);
        }
    }
}

struct BindingRefCollector<'a> {
    bindings: &'a mut ReferenceCapturedBindings,
}

impl HirVisitor for BindingRefCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) => {
                self.bindings.locals.insert(*local);
            }
            HirExpr::ParamRef(param) => {
                self.bindings.params.insert(*param);
            }
            HirExpr::TempRef(temp) => {
                self.bindings.temps.insert(*temp);
            }
            _ => {}
        }
    }
}

pub(super) fn expr_mentions_temp(expr: &HirExpr, temp: TempId) -> bool {
    TempMentionCollector::mentions_in_expr(expr, temp)
}

pub(super) fn stmt_writes_temp(stmt: &HirStmt, temp: TempId) -> bool {
    TempWriteCollector::writes_in_stmt(stmt, temp)
}

pub(super) fn collect_temp_use_counts(proto: &HirProto) -> BTreeMap<TempId, usize> {
    let mut collector = TempUseCollector::default();
    visit_proto(proto, &mut collector);
    collector.counts
}

pub(super) fn collect_temp_write_counts(proto: &HirProto) -> BTreeMap<TempId, usize> {
    let mut collector = TempWriteCountCollector::default();
    visit_proto(proto, &mut collector);
    collector.counts
}

#[derive(Default)]
struct TempWriteCountCollector {
    counts: BTreeMap<TempId, usize>,
}

impl HirVisitor for TempWriteCountCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            *self.counts.entry(*temp).or_default() += 1;
        }
    }
}

#[derive(Default)]
struct TempUseCollector {
    counts: BTreeMap<TempId, usize>,
}

impl HirVisitor for TempUseCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            *self.counts.entry(*temp).or_default() += 1;
        }
    }
}

struct LocalMentionCollector {
    local: LocalId,
    mentioned: bool,
}

impl LocalMentionCollector {
    fn mentions_in_stmts(stmts: &[HirStmt], local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_stmts(stmts, &mut collector);
        collector.mentioned
    }

    fn mentions_in_block(block: &HirBlock, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_block(block, &mut collector);
        collector.mentioned
    }

    fn mentions_in_expr(expr: &HirExpr, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_expr(expr, &mut collector);
        collector.mentioned
    }
}

impl HirVisitor for LocalMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::LocalRef(local) if *local == self.local);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

struct LocalCaptureCollector {
    local: LocalId,
    captured: bool,
}

impl LocalCaptureCollector {
    fn captures_in_stmt(stmt: &HirStmt, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            captured: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.captured
    }
}

impl HirVisitor for LocalCaptureCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::Closure(closure) = expr {
            self.captured |= closure
                .captures
                .iter()
                .any(|capture| expr_mentions_local(&capture.value, self.local));
        }
    }
}

#[derive(Default)]
struct CapturedLocalSetCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor for CapturedLocalSetCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::Closure(closure) = expr else {
            return;
        };
        for capture in &closure.captures {
            let mut collector = LocalRefSetCollector {
                locals: &mut self.locals,
            };
            visit_expr(&capture.value, &mut collector);
        }
    }
}

struct LocalRefSetCollector<'a> {
    locals: &'a mut BTreeSet<LocalId>,
}

impl HirVisitor for LocalRefSetCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.locals.insert(*local);
        }
    }
}

struct TempMentionCollector {
    temp: TempId,
    mentioned: bool,
}

impl TempMentionCollector {
    fn mentions_in_expr(expr: &HirExpr, temp: TempId) -> bool {
        let mut collector = Self {
            temp,
            mentioned: false,
        };
        visit_expr(expr, &mut collector);
        collector.mentioned
    }
}

impl HirVisitor for TempMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::TempRef(temp) if *temp == self.temp);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}

struct TempWriteCollector {
    temp: TempId,
    written: bool,
}

impl TempWriteCollector {
    fn writes_in_stmt(stmt: &HirStmt, temp: TempId) -> bool {
        let mut collector = Self {
            temp,
            written: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.written
    }
}

impl HirVisitor for TempWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}
