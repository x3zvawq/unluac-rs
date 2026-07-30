//! 这个文件集中处理 HIR 对短路 DAG 的消费。
//!
//! `StructureFacts` 现在提供的是“按 truthy/falsy 连边的短路 DAG”，而不是先验压平
//! 的线性链。这里的职责就是把这些 DAG 重新折回 HIR 的 `LogicalAnd / LogicalOr`，
//! 同时保留值位置和条件位置在 Lua 里的不同语义。

mod decision;
mod lowering;

use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
};
use crate::structure::BlockRef;
use crate::structure::{ConditionPlan, ConditionTarget, ValueDecisionPlan, ValueDecisionTarget};
use crate::transformer::LowInstr;

pub(super) use self::decision::{build_condition_decision_expr, build_value_decision_expr};
use self::lowering::{lower_short_circuit_subject, lower_short_circuit_subject_single_eval};
use super::exprs::{
    expr_for_fixed_def, expr_for_fixed_def_single_eval, expr_for_ssa_value, lower_branch_subject,
    lower_branch_subject_single_eval,
};
use super::lower::ProtoLowering;
