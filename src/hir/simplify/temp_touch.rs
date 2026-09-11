//! 这个文件承载 temp 引用检测相关的纯查询工具。
//!
//! 独立表达式、语句片段与 proto 的一次性查询在这里按明确的 read/touch 角色收集。
//! `carried_locals` 的当前改写快照仍由 `TempTouchIndex` 发布直属语句位置；locals 与
//! root 分析的递归快照则消费共享 RootEventIndex，不在这里重建每层后代集合。
//!
//! 这些查询都是只读的，不会修改 HIR 结构。位置事实直接发布到共享 PositionIndex，
//! 不先复制每条语句的集合再转置或计数。按 temp 建立的 occurrence index 让候选扩张
//! 只访问真实 touch 语句，不必为每个定义重复扫描完整后缀。touch 包含 Temp lvalue 写入，
//! 不能替代只读取表达式的 read 查询；两者都遵守共享 visitor 的 capture 绑定投影。

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
