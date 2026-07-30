//! 这个文件承载 HIR `Decision` 的共享表达式化入口。
//!
//! `Decision` 是 HIR 内部为了保住共享短路子图而引入的中间形态，但它到底什么时候
//! 能安全折回普通表达式，不能让 analyze 和 simplify 各自维护一套规则。这里把
//! 那条共享入口固定下来，避免两边因为局部实现分叉而把同一棵决策图恢复成两种风格。

use crate::hir::common::{HirDecisionExpr, HirExpr};

pub(in crate::hir) fn finalize_condition_decision_expr(decision: HirDecisionExpr) -> HirExpr {
    if super::simplify::decision::decision_has_shared_nodes(&decision) {
        HirExpr::Decision(Box::new(decision))
    } else {
        super::simplify::decision::collapse_condition_decision_expr(&decision)
            .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
    }
}

pub(in crate::hir) fn finalize_value_decision_expr(decision: HirDecisionExpr) -> HirExpr {
    super::simplify::decision::collapse_value_decision_expr(&decision)
        .unwrap_or_else(|| HirExpr::Decision(Box::new(decision)))
}
