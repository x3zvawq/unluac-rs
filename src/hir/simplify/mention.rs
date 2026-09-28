//! HIR simplify 共用的 binding/temp 提及与资源身份收集。
//!
//! 消费共享 visitor 和 Promotion 的 home 查询，发布当前快照的只读事实。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBinding, HirBlock, HirCapture, HirCaptureMode, HirExpr, HirLValue, HirProto, HirStmt,
    LocalId, ParamId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use crate::hir::visit::{HirVisitor, visit_block, visit_expr, visit_proto, visit_stmts};

pub(super) fn stmts_mention_local(stmts: &[HirStmt], local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_stmts(stmts, local)
}

/// 批量查询同一后缀时一次收集读取和直接左值；声明字段本身不属于 mention。
pub(super) fn stmts_mentioned_locals(stmts: &[HirStmt]) -> BTreeSet<LocalId> {
    let mut locals = BTreeSet::new();
    visit_stmts(
        stmts,
        &mut LocalMentionSetCollector {
            locals: &mut locals,
        },
    );
    locals
}

pub(super) fn block_mentions_local(block: &HirBlock, local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_block(block, local)
}

pub(super) fn expr_mentions_local(expr: &HirExpr, local: LocalId) -> bool {
    crate::hir::visit::any_expr(
        expr,
        &mut |expr| matches!(expr, HirExpr::LocalRef(id) if *id == local),
    )
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

impl ReferenceCapturedBindings {
    /// 身份合并后使用完整 possible homes；Unknown 扩大到 Promotion 的物理 universe。
    /// ByValue/ByReference 的选择由收集入口决定，投影不把来源槽当成定义写入。
    pub(super) fn complete_home_slots(&self, facts: &ProtoPromotionFacts) -> BTreeSet<HomeSlotKey> {
        let bindings = self
            .locals
            .iter()
            .copied()
            .map(HirBinding::Local)
            .chain(self.params.iter().copied().map(HirBinding::Param))
            .chain(self.temps.iter().copied().map(HirBinding::Temp));
        let mut homes = BTreeSet::new();
        for binding in bindings {
            homes.extend(facts.complete_binding_home_slots(binding).iter().copied());
        }
        homes
    }

    pub(super) fn contains(&self, binding: HirBinding) -> bool {
        match binding {
            HirBinding::Local(local) => self.locals.contains(&local),
            HirBinding::Param(param) => self.params.contains(&param),
            HirBinding::Temp(temp) => self.temps.contains(&temp),
            HirBinding::Upvalue(_) => false,
        }
    }

    fn insert(&mut self, binding: HirBinding) {
        match binding {
            HirBinding::Local(local) => {
                self.locals.insert(local);
            }
            HirBinding::Param(param) => {
                self.params.insert(param);
            }
            HirBinding::Temp(temp) => {
                self.temps.insert(temp);
            }
            HirBinding::Upvalue(_) => {}
        }
    }
}

/// 发布当前树中的直接读取身份，含 closure 的父 binding，不进入 child proto。
/// sink 决定收集 identity、home 或两者，不另建四类引用集合再还原同一个 binding。
pub(super) struct BindingReadCollector<F>(pub(super) F);

impl<F: FnMut(HirBinding)> HirVisitor<'_> for BindingReadCollector<F> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = HirBinding::from_expr(expr) {
            (self.0)(binding);
        }
    }
}

pub(super) fn binding_home_read_collector<'a>(
    facts: &'a ProtoPromotionFacts,
    homes: &'a mut BTreeSet<HomeSlotKey>,
) -> impl for<'hir> HirVisitor<'hir> + 'a {
    BindingReadCollector(move |binding| {
        homes.extend(facts.complete_binding_home_slots(binding).iter().copied());
    })
}

pub(super) fn expr_read_homes(
    expr: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut homes = BTreeSet::new();
    visit_expr(expr, &mut binding_home_read_collector(facts, &mut homes));
    homes
}

pub(super) fn stmts_reference_captured_bindings(stmts: &[HirStmt]) -> ReferenceCapturedBindings {
    let mut collector = CaptureCollector::new(HirCaptureMode::ByReference);
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

/// Collect bindings copied into a closure by value.  Unlike a reference capture, a value
/// capture is a snapshot: a later write to the same physical slot must not be merged back into
/// the captured binding merely because the snapshot has no ordinary expression use.
pub(super) fn stmts_value_captured_bindings(stmts: &[HirStmt]) -> ReferenceCapturedBindings {
    let mut collector = CaptureCollector::new(HirCaptureMode::ByValue);
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

/// 按 TBC origin 收集资源注册点的物理 home，不从改写后的 value 重建槽位 epoch。
/// 当前 value 的逻辑读取与 protected-local 保护由各自查询保留。
pub(super) fn stmts_tbc_protected_home_slots(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut collector = ToBeClosedHomeCollector {
        facts,
        homes: BTreeSet::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.homes
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
pub(super) struct ProtectedLocalCollector {
    pub(super) locals: BTreeSet<LocalId>,
}

impl HirVisitor<'_> for ProtectedLocalCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::NumericFor(for_stmt) => {
                self.locals.insert(for_stmt.binding);
            }
            HirStmt::GenericFor(for_stmt) => {
                self.locals.extend(for_stmt.bindings.iter().copied());
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                let mut refs = LocalMentionSetCollector {
                    locals: &mut self.locals,
                };
                visit_expr(&to_be_closed.value, &mut refs);
            }
            _ => {}
        }
    }
}

pub(super) struct ToBeClosedHomeCollector<'a> {
    pub(super) facts: &'a ProtoPromotionFacts,
    pub(super) homes: BTreeSet<HomeSlotKey>,
}

impl HirVisitor<'_> for ToBeClosedHomeCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::ToBeClosed(to_be_closed) = stmt else {
            return;
        };
        self.homes.insert(self.facts.tbc_home(to_be_closed.origin));
    }
}

#[derive(Default)]
pub(super) struct ToBeClosedTempCollector {
    pub(super) temps: BTreeSet<TempId>,
}

impl HirVisitor<'_> for ToBeClosedTempCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::ToBeClosed(to_be_closed) = stmt else {
            return;
        };
        if let HirExpr::TempRef(temp) = &to_be_closed.value {
            self.temps.insert(*temp);
        }
    }
}

pub(super) struct CaptureCollector {
    mode: HirCaptureMode,
    pub(super) bindings: ReferenceCapturedBindings,
}

impl CaptureCollector {
    pub(super) fn new(mode: HirCaptureMode) -> Self {
        Self {
            mode,
            bindings: Default::default(),
        }
    }
}

impl HirVisitor<'_> for CaptureCollector {
    fn visit_capture(&mut self, capture: &HirCapture) {
        if capture.mode != self.mode {
            return;
        }
        self.bindings.insert(capture.binding);
    }
}

pub(super) fn expr_mentions_temp(expr: &HirExpr, temp: TempId) -> bool {
    crate::hir::visit::any_expr(
        expr,
        &mut |expr| matches!(expr, HirExpr::TempRef(id) if *id == temp),
    )
}

pub(super) fn stmt_writes_temp(stmt: &HirStmt, temp: TempId) -> bool {
    TempWriteCollector::writes_in_stmt(stmt, temp)
}

pub(super) fn stmt_writes_local(stmt: &HirStmt, local: LocalId) -> bool {
    let mut written = false;
    visit_local_writes(stmt, |target| written |= target == local);
    written
}

pub(super) fn stmts_write_local(stmts: &[HirStmt], local: LocalId) -> bool {
    stmts.iter().any(|stmt| stmt_writes_local(stmt, local))
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

impl HirVisitor<'_> for TempWriteCountCollector {
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

impl HirVisitor<'_> for TempUseCollector {
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
}

impl HirVisitor<'_> for LocalMentionCollector {
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

impl HirVisitor<'_> for LocalCaptureCollector {
    fn visit_capture(&mut self, capture: &HirCapture) {
        self.captured |= capture.binding == HirBinding::Local(self.local);
    }
}

#[derive(Default)]
struct CapturedLocalSetCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor<'_> for CapturedLocalSetCollector {
    fn visit_capture(&mut self, capture: &HirCapture) {
        if let HirBinding::Local(local) = capture.binding {
            self.locals.insert(local);
        }
    }
}

struct LocalMentionSetCollector<'a> {
    locals: &'a mut BTreeSet<LocalId>,
}

impl HirVisitor<'_> for LocalMentionSetCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.locals.insert(*local);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Local(local) = lvalue {
            self.locals.insert(*local);
        }
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

impl HirVisitor<'_> for TempWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}

/// 枚举当前语句的逻辑 local 写入，包括声明、循环绑定和 root release；不进入子 proto。
/// 调用者可按身份查询或维护索引，VM home 覆盖仍由各自的物理写入 owner 解释。
pub(super) fn visit_local_writes(stmt: &HirStmt, mut visit: impl FnMut(LocalId)) {
    visit_stmts(
        std::slice::from_ref(stmt),
        &mut BindingWriteCollector(|binding| {
            if let HirBinding::Local(local) = binding {
                visit(local);
            }
        }),
    );
}

/// 枚举声明、循环绑定与左值的逻辑写入；重复 target 和 root release 各保留一次事件。
/// 例如 `a, a = x, y` 产生两次写；这些身份事件不证明原 VM home 被覆盖。
pub(super) struct BindingWriteCollector<F>(pub(super) F);

impl<F: FnMut(HirBinding)> HirVisitor<'_> for BindingWriteCollector<F> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                for &local in &decl.bindings {
                    (self.0)(HirBinding::Local(local));
                }
            }
            HirStmt::NumericFor(for_stmt) => (self.0)(HirBinding::Local(for_stmt.binding)),
            HirStmt::GenericFor(for_stmt) => {
                for &local in &for_stmt.bindings {
                    (self.0)(HirBinding::Local(local));
                }
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = HirBinding::from_lvalue(lvalue) {
            (self.0)(binding);
        }
    }
}
