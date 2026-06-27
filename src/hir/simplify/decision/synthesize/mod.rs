//! 这个文件负责为“纯、稳定”的 `Decision` 提供值表达式综合。
//!
//! 前面的 `collapse_value_decision_expr` 只覆盖一批很直接的局部形状；一旦共享 DAG
//! 需要稍微跨一层做组合，它就会保守失败，然后被末端物化成嵌套 `if`。这对正确性
//! 没问题，但会把本来能够自然保留成短路表达式的 case 也压平。这里补的是一条确定性的
//! 结构性路径：
//! 1. 只接受无副作用、表达式求值顺序稳定的 decision；
//! 2. 沿 DAG 自顶向下提取每个节点的单一最佳表达式候选；
//! 3. 只在少量固定模板里做选择，而不是枚举表达式空间；
//! 4. 用抽象值解释器验证候选是否与原 decision 等价。

mod cost;
mod domain;
mod readable;
mod safety;
mod value;

pub(crate) use cost::expr_cost;
pub(crate) use readable::{naturalize_pure_logical_expr, synthesize_readable_pure_logical_expr};
pub(crate) use safety::decision_is_synth_safe;
pub(crate) use value::synthesize_value_decision_expr;

use crate::hir::common::{HirBinaryExpr, HirExpr, HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind};

const MAX_SYNTH_REFS: usize = 4;
const EXTRA_TRUTHY_SYMBOLS: usize = 2;

fn normalize_candidate_expr(expr: HirExpr) -> HirExpr {
    match expr {
        HirExpr::Unary(unary) => match unary.op {
            HirUnaryOpKind::Not => match normalize_candidate_expr(unary.expr) {
                HirExpr::Boolean(value) => HirExpr::Boolean(!value),
                inner => HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Not,
                    expr: inner,
                })),
            },
            _ => HirExpr::Unary(Box::new(HirUnaryExpr {
                op: unary.op,
                expr: normalize_candidate_expr(unary.expr),
            })),
        },
        HirExpr::LogicalAnd(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs);
            let rhs = normalize_candidate_expr(logical.rhs);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs) {
                if lhs_truthy { rhs } else { lhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                HirExpr::Boolean(false)
            } else {
                let expr = HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs }));
                super::simplify_lua_logical_shape(&expr).unwrap_or(expr)
            }
        }
        HirExpr::LogicalOr(logical) => {
            let lhs = normalize_candidate_expr(logical.lhs);
            let rhs = normalize_candidate_expr(logical.rhs);
            if let Some(lhs_truthy) = super::expr_truthiness(&lhs) {
                if lhs_truthy { lhs } else { rhs }
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(false))
            {
                lhs
            } else if super::expr_is_boolean_valued(&lhs) && matches!(rhs, HirExpr::Boolean(true)) {
                HirExpr::Boolean(true)
            } else {
                let expr = HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }));
                super::simplify_lua_logical_shape(&expr).unwrap_or(expr)
            }
        }
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(HirBinaryExpr {
            op: binary.op,
            lhs: normalize_candidate_expr(binary.lhs),
            rhs: normalize_candidate_expr(binary.rhs),
        })),
        other => other,
    }
}
