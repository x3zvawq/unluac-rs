//! 提供 HIR temp 的只读 read/touch 查询及出现位置索引。
//!
//! 消费当前表达式或语句快照；递归根分析和 locals 的共享事件由 RootEventIndex 持有。

use std::collections::BTreeSet;

use crate::hir::common::{HirExpr, HirLValue, HirProto, HirStmt, TempId};

use crate::hir::visit::{HirVisitor, visit_expr, visit_proto, visit_stmts};

pub(super) fn expr_touches_any_temp(expr: &HirExpr, temps: &BTreeSet<TempId>) -> bool {
    crate::hir::visit::any_expr(
        expr,
        &mut |expr| matches!(expr, HirExpr::TempRef(temp) if temps.contains(temp)),
    )
}

pub(super) fn collect_temp_refs_in_expr(expr: &HirExpr) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    visit_expr(
        expr,
        &mut TempRefCollector(|temp| {
            temps.insert(temp);
        }),
    );
    temps
}

pub(super) fn collect_temp_touch_positions(stmts: &[HirStmt]) -> TempTouchIndex {
    let mut positions = TempTouchIndex::default();
    for (index, stmt) in stmts.iter().enumerate() {
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut TempRefCollector(|temp| positions.record(temp, index)),
        );
    }
    positions
}

pub(super) fn collect_temp_reads_in_proto(proto: &HirProto) -> BTreeSet<TempId> {
    let mut collector = TempReadCollector::default();
    visit_proto(proto, &mut collector);
    collector.temps
}

/// temp 逻辑读写的直属语句位置；物理 home 与生命周期由各自 owner 解释。
pub(super) type TempTouchIndex = crate::graph::PositionIndex<TempId>;

struct TempRefCollector<F>(F);

#[derive(Default)]
pub(super) struct TempReadCollector {
    pub(super) temps: BTreeSet<TempId>,
}

impl HirVisitor<'_> for TempReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.temps.insert(*temp);
        }
    }
}

impl<F: FnMut(TempId)> HirVisitor<'_> for TempRefCollector<F> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            (self.0)(*temp);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            (self.0)(*temp);
        }
    }
}
