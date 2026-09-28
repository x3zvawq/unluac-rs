//! 为 HIR Decision 综合可证明等价的值表达式。
//!
//! 消费规范化 DAG、事件安全性与抽象值验证，保留原求值轨迹并选择有限候选。

mod cost;
mod domain;
mod safety;
mod value;

pub(crate) use cost::expr_cost;
pub(crate) use value::synthesize_value_decision_expr;

use crate::hir::common::{HirBinaryExpr, HirExpr, HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind};
use crate::hir::expr_safety::HirExprSafety;

const EXTRA_TRUTHY_SYMBOLS: usize = 2;

fn normalize_candidate_expr(expr: HirExpr, safety: HirExprSafety) -> HirExpr {
    match expr {
        HirExpr::Unary(unary) => match unary.op {
            HirUnaryOpKind::Not => match normalize_candidate_expr(unary.expr, safety) {
                HirExpr::Boolean(value) => HirExpr::Boolean(!value),
                inner => HirExpr::Unary(Box::new(HirUnaryExpr {
                    source_site: unary.source_site,
                    op: HirUnaryOpKind::Not,
                    expr: inner,
                })),
            },
            _ => HirExpr::Unary(Box::new(HirUnaryExpr {
                source_site: unary.source_site,
                op: unary.op,
                expr: normalize_candidate_expr(unary.expr, safety),
            })),
        },
        HirExpr::LogicalAnd(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs, safety);
            let rhs = normalize_candidate_expr(logical.rhs, safety);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs, safety) {
                if lhs_truthy { rhs } else { lhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                HirExpr::Boolean(false)
            } else {
                let expr = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    preserves_boolean_prewrite: false,
                    lhs,
                    rhs,
                }));
                super::super::logical_simplify::simplify_logical_shape_with_safety(&expr, safety)
                    .unwrap_or(expr)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs, safety);
            let rhs = normalize_candidate_expr(logical.rhs, safety);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs, safety) {
                if lhs_truthy { lhs } else { rhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                HirExpr::Boolean(true)
            } else {
                let expr = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    preserves_boolean_prewrite: false,
                    lhs,
                    rhs,
                }));
                super::super::logical_simplify::simplify_logical_shape_with_safety(&expr, safety)
                    .unwrap_or(expr)
            }
        }
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(HirBinaryExpr {
            source_site: binary.source_site,
            op: binary.op,
            lhs: normalize_candidate_expr(binary.lhs, safety),
            rhs: normalize_candidate_expr(binary.rhs, safety),
        })),
        other => other,
    }
}
