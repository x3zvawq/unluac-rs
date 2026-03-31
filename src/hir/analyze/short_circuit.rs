//! 这个文件集中处理 HIR 对短路 DAG 的消费。
//!
//! `StructureFacts` 现在提供的是“按 truthy/falsy 连边的短路 DAG”，而不是先验压平
//! 的线性链。这里的职责就是把这些 DAG 重新折回 HIR 的 `LogicalAnd / LogicalOr`，
//! 同时保留值位置和条件位置在 Lua 里的不同语义。

mod decision;
mod guards;
mod lowering;
mod recovery;

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, DefId, PhiId, SsaValue};
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, TempId,
};
use crate::hir::decision::{
    decision_is_synth_safe, finalize_condition_decision_expr, finalize_value_decision_expr,
};
use crate::structure::{
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef,
    ShortCircuitTarget,
};
use crate::transformer::{BranchOperands, CondOperand, InstrRef, LowInstr, Reg};

use self::decision::{
    DecisionEdge, branch_exit_blocks_from_value_merge_candidate, build_branch_decision_expr,
    build_branch_decision_expr_for_value_merge_candidate,
    build_branch_decision_expr_for_value_merge_candidate_single_eval,
    build_branch_decision_expr_single_eval, build_decision_expr, build_impure_value_merge_expr,
    build_value_decision_expr, build_value_decision_expr_single_eval,
};
use self::guards::{
    decision_references_forbidden_candidate_temps, expr_references_forbidden_candidate_temps,
};
pub(super) use self::lowering::{
    lower_materialized_value_leaf_expr, lower_short_circuit_subject,
    lower_short_circuit_subject_single_eval,
};
use self::lowering::{lower_short_circuit_subject_inline, lower_value_leaf_expr};
pub(super) use self::recovery::{
    BranchShortCircuitPlan, build_branch_short_circuit_plan, build_conditional_reassign_plan,
    consumed_value_merge_subject_instrs,
    recover_short_value_merge_expr_recovery_with_allowed_blocks,
    recover_short_value_merge_expr_with_allowed_blocks, value_merge_candidate_by_header,
    value_merge_candidates_in_block, value_merge_skipped_blocks,
};
#[cfg(test)]
use self::recovery::{ChangedRegionEntry, ValueLeafKind, find_changed_region_entry};
use super::ProtoLowering;
use super::exprs::{
    expr_for_dup_safe_fixed_def, expr_for_fixed_def, expr_for_reg_at_block_entry, expr_for_reg_use,
    lower_branch_subject, lower_branch_subject_inline, lower_branch_subject_single_eval,
};

#[cfg(test)]
mod tests;
