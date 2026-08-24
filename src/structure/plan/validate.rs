use std::collections::BTreeSet;

use super::{
    BlockEmissionPlan, BlockTerminatorKind, BranchArm, CleanupDisposition, ConditionArcPolarity,
    ConditionPlan, ConditionPlanId, ConditionTarget, ControlFlowFeature, EdgeActionPlacement,
    EdgeTransfer, ForwardRouteKind, LabelPlacement, LoopPlanId, PhiIncomingDisposition,
    PlanRequirement, RegionId, RegionNavigation, RegionPlan, ScopePlanId, StructureError,
    UnstructuredLayoutItem, ValueDecisionArcPlan, ValueDecisionPlan, ValueDecisionPlanId,
    ValueDecisionTarget,
};
use crate::structure::helpers::shared_pure_terminal_kind;
use crate::structure::{
    BlockKind, BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts, SsaValue, StructurePlan,
};
use crate::transformer::{BranchSubject, InstrRef, LowInstr, LoweredProto};

mod branches;
mod cleanup;
mod conditions;
mod edges;
mod emissions;
mod labels;
mod loops;
mod phis;
mod propagated_breaks;
mod regions;
mod requirements;
mod single_pass;
mod terminators;
mod value_decisions;

use branches::*;
use cleanup::*;
use conditions::*;
use edges::*;
use emissions::*;
use labels::*;
use loops::*;
use phis::*;
use propagated_breaks::*;
use regions::*;
use requirements::*;
use single_pass::*;
use terminators::*;
use value_decisions::*;

pub(super) fn validate(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.regions.is_empty() || plan.root.index() >= plan.regions.len() {
        return Err(StructureError::invalid("plan root is missing"));
    }
    if !matches!(
        plan.regions[plan.root.index()],
        RegionPlan::Sequence { parent: None, .. }
    ) {
        return Err(StructureError::invalid(
            "plan root must be a parentless sequence",
        ));
    }
    if plan.region_by_block.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block-to-region index length mismatch",
        ));
    }

    validate_containment(plan)?;
    plan.navigation.validate(cfg, plan)?;
    let intervals = &plan.navigation;
    let edge_regions = &plan.navigation;
    let block_stats = RegionBlockStats::new(plan, intervals)?;
    validate_block_terminators(proto, cfg, plan)?;
    validate_block_coverage(cfg, plan)?;
    validate_region_entries(cfg, plan, intervals)?;
    validate_single_pass_plans(cfg, plan, intervals)?;
    let condition_edges = validate_condition_plans(proto, cfg, plan)?;
    validate_branch_plans(cfg, plan, intervals, &block_stats, &condition_edges)?;
    let loop_edges = validate_loop_plans(proto, cfg, plan, intervals, &block_stats)?;
    validate_labels(cfg, plan)?;
    validate_edges(
        cfg,
        plan,
        intervals,
        edge_regions,
        &condition_edges,
        &loop_edges,
    )?;
    validate_requirements(cfg, plan, intervals)?;
    validate_value_decision_plans(cfg, plan)?;
    Ok(())
}

pub(super) fn validate_final(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    validate(proto, cfg, plan)?;
    crate::structure::scope::validate_label_tbc_barriers(proto, cfg, plan)?;
    validate_condition_predicates(proto, plan)?;
    validate_condition_prefix_placements(proto, cfg, plan)?;
    validate_cleanup(proto, cfg, plan)?;
    validate_phis(cfg, dataflow, plan)?;
    validate_block_emissions(cfg, plan)?;
    super::loop_protocol::validate(proto, cfg, graph_facts, dataflow, plan)?;
    validate_condition_values(proto, cfg, dataflow, plan)?;
    validate_value_decision_values(proto, cfg, dataflow, plan)?;
    Ok(())
}
