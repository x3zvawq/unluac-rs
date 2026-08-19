//! 这个文件直接消费 Structure 最终 region/edge plan。
//!
//! 这里不按 header 搜候选、不做试降回滚，也不把 emitted 集合作为结构决策依据。
//! region、edge 与 value identity 已在 Structure 冻结；本模块只执行计划并校验引用一致性。

use std::collections::BTreeMap;

use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLValue, HirLabel, HirLabelId, HirNumericFor, HirProtoRef,
    HirRepeat, HirStmt, HirWhile, TempId,
};
use crate::hir::decision::{finalize_condition_decision_expr, finalize_value_decision_expr};
use crate::structure::{
    BlockEmissionPlan, BlockRef, BlockTerminatorKind, BlockTerminatorPlan, CleanupDisposition,
    EdgeKind, EdgePlan, EdgeRef, EdgeTransfer, LabelPlacement, LoopConditionProtocol,
    LoopIterationDisposition, LoopRepeatForm, LoopRepeatProtocol, LoopValuePhase, LoopValueSource,
    LoopVmProtocol, PhiId, PhiIncomingDisposition, PlanRequirement, RegionId, RegionPlan, SsaValue,
    UnstructuredLayoutItem,
};
use crate::transformer::{InstrRef, LowInstr, Reg};

use super::super::exprs::{expr_for_reg_use, lower_branch_cond};
use super::super::helpers::{assign_stmt, branch_stmt, goto_block};
use super::super::instrs::{local_decl_stmts, lower_regular_instr, lower_terminal_instr};
use super::super::lower::ProtoLowering;
use super::super::short_circuit::{build_condition_decision_expr, build_value_decision_expr};
use super::generic_for::lower_generic_for_iterator;

mod blocks;
mod branches;
mod edges;
/// 从最终 region arena 构造 HIR body。
mod index;
mod labels;
mod loops;
mod syntax;
mod traversal;
mod verification;

pub(super) fn build_planned_body(
    proto: HirProtoRef,
    lowering: &ProtoLowering<'_>,
) -> Result<HirBlock, HirLowerError> {
    let mut lowerer = PlanBodyLowerer::new(proto, lowering)?;
    let body = lowerer.lower_plan_node(lowering.structure.plan().root())?;
    #[cfg(debug_assertions)]
    if lowerer.emitted_label_count != lowering.structure.plan().labels().len() {
        return Err(HirLowerError::InvalidPlanRegion {
            proto: proto.index(),
            region: lowering.structure.plan().root().index(),
            detail: "final plan contains a label outside the emitted region tree",
        });
    }
    Ok(body)
}

struct PlanBodyLowerer<'a, 'b> {
    proto: HirProtoRef,
    lowering: &'b ProtoLowering<'a>,
    index: PlanLoweringIndex,
    #[cfg(debug_assertions)]
    emitted_labels: Vec<bool>,
    #[cfg(debug_assertions)]
    emitted_label_count: usize,
    #[cfg(debug_assertions)]
    emitted_blocks: Vec<bool>,
    #[cfg(debug_assertions)]
    emitted_synthetic_inputs: Vec<bool>,
    condition_block_seen_at: Vec<usize>,
    condition_epoch: usize,
}

struct PlanLoweringIndex {
    plain_block_count: Vec<Option<usize>>,
    single_plain_block: Vec<Option<BlockRef>>,
    region_inputs: Vec<Vec<(PhiId, SsaValue)>>,
    unresolved_requirement: Vec<Option<(BlockRef, Reg)>>,
    normal_tail_guard_by_edge: Vec<Option<(RegionId, TempId)>>,
    consumed_loop_copy_targets: Vec<Vec<PhiId>>,
    repeat_staged_result_by_phi: Vec<Option<(RegionId, TempId)>>,
    canonical_move_source: Vec<Option<SsaValue>>,
    absorbed_region_result_moves: Vec<bool>,
    shared_ssa_temps: Vec<bool>,
}

struct PlannedLoopCondition {
    prefix: Vec<HirStmt>,
    cond: HirExpr,
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum CopyBinding {
    Temp(TempId),
    Local(crate::hir::common::LocalId),
}

fn copy_target_binding(target: &HirLValue) -> Option<CopyBinding> {
    match target {
        HirLValue::Temp(temp) => Some(CopyBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(CopyBinding::Local(*local)),
        _ => None,
    }
}

fn copy_value_binding(value: &HirExpr) -> Option<CopyBinding> {
    match value {
        HirExpr::TempRef(temp) => Some(CopyBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(CopyBinding::Local(*local)),
        _ => None,
    }
}

fn copy_assignment_stmt(targets: Vec<HirLValue>, values: Vec<HirExpr>) -> Option<HirStmt> {
    if targets.len() != values.len() {
        return Some(assign_stmt(targets, values));
    }
    let mut target_counts = BTreeMap::<CopyBinding, usize>::new();
    for binding in targets.iter().filter_map(copy_target_binding) {
        *target_counts.entry(binding).or_default() += 1;
    }
    let mut retained_targets = Vec::with_capacity(targets.len());
    let mut retained_values = Vec::with_capacity(values.len());
    for (target, value) in targets.into_iter().zip(values) {
        let binding = copy_target_binding(&target);
        let is_unique_self_copy = binding == copy_value_binding(&value)
            && binding.is_some_and(|binding| target_counts.get(&binding) == Some(&1));
        if !is_unique_self_copy {
            retained_targets.push(target);
            retained_values.push(value);
        }
    }
    (!retained_targets.is_empty()).then(|| assign_stmt(retained_targets, retained_values))
}

struct PlannedForRegions {
    preheader: Option<RegionId>,
    control: RegionId,
    normal_tail: Option<(HirBlock, TempId)>,
}

struct PlannedLoopParts {
    preheader: Option<RegionId>,
    control: RegionId,
    body: HirBlock,
    normal_tail_region: Option<RegionId>,
    normal_tail_body: Option<HirBlock>,
}

#[derive(Clone, Copy)]
struct PlannedLoopIdentity {
    header: BlockRef,
    source_bindings: Option<crate::structure::LoopSourceBindings>,
    preheader_body: Option<EdgeRef>,
    preheader_exit: Option<EdgeRef>,
    has_normal_tail: bool,
}

enum LowerTask {
    Region(RegionId),
    Block {
        owner: RegionId,
        block: BlockRef,
    },
    FinishSequence {
        region: RegionId,
        outer_prefix: Vec<HirStmt>,
        prefix: Vec<HirStmt>,
        result_start: usize,
        child_count: usize,
        single_pass: bool,
    },
    FinishBranch {
        region: RegionId,
        prefix: Vec<HirStmt>,
        plan: crate::structure::BranchPlanId,
        condition: RegionId,
        has_else: bool,
        result_start: usize,
    },
    FinishLoop {
        region: RegionId,
        prefix: Vec<HirStmt>,
        plan: crate::structure::LoopPlanId,
        preheader: Option<RegionId>,
        control: RegionId,
        normal_tail: Option<RegionId>,
        result_start: usize,
    },
    FinishUnstructured {
        region: RegionId,
        outer_prefix: Vec<HirStmt>,
        prefix: Vec<HirStmt>,
        result_start: usize,
        item_count: usize,
        single_pass: bool,
    },
}
