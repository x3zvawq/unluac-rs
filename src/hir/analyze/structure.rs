//! 这个文件是 HIR 结构恢复的 facade。
//!
//! 它只负责声明 `structure/` 子模块、拼装共享上下文，并暴露结构化 lowering 的入口。
//! 真正的业务逻辑都放在目录里，避免入口文件再次膨胀成难维护的巨型实现。

mod body;
mod branch_values;
mod loops;
mod overrides;
mod rewrites;

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, PhiId};
use crate::hir::common::{
    HirBlock, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
    HirGenericFor, HirLValue, HirLabel, HirLabelId, HirLogicalExpr, HirNumericFor, HirRepeat,
    HirStmt, HirWhile, TempId,
};
use crate::structure::{
    BranchCandidate, BranchKind, BranchRegionFact, BranchValueMergeArm, BranchValueMergeCandidate,
    BranchValueMergeValue, GotoReason, LoopCandidate, LoopKindHint, LoopValueArm, LoopValueMerge,
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNodeRef, ShortCircuitTarget,
};
use crate::transformer::{InstrRef, LowInstr, Reg};

use super::exprs::{
    expr_for_dup_safe_fixed_def, expr_for_fixed_def, expr_for_reg_at_block_exit, expr_for_reg_use,
};
use super::short_circuit::{
    BranchShortCircuitPlan, build_branch_short_circuit_plan, build_conditional_reassign_plan,
    consumed_value_merge_subject_instrs, header_subject_is_value_carrier,
    lower_materialized_value_leaf_expr, lower_short_circuit_subject,
    recover_short_value_merge_expr_recovery_with_allowed_blocks,
    recover_short_value_merge_expr_with_allowed_blocks, value_merge_candidate_by_header,
    value_merge_skipped_blocks,
};
use super::{ProtoLowering, assign_stmt, branch_stmt, lower_branch_cond};
use super::{
    build_label_map_for_summary, goto_block, is_control_terminator, lower_control_instr,
    lower_phi_materialization_with_allowed_blocks_except, lower_regular_instr,
};
use body::*;
use overrides::StructureOverrideState;
use rewrites::{
    apply_loop_rewrites, expr_as_lvalue, install_def_target_overrides, lvalue_as_expr,
    rewrite_expr_temps, rewrite_stmt_exprs, shared_expr_for_defs, shared_lvalue_for_defs,
    temp_expr_overrides,
};

/// 尝试基于现有结构候选恢复一个更接近源码的 HIR block。
pub(super) fn try_build_structured_body(lowering: &ProtoLowering<'_>) -> Option<HirBlock> {
    body::build_structured_body(lowering)
}
