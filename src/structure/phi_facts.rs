//! 为 Structure 统一投影 Dataflow phi 的 incoming 与值身份。
//!
//! 供 branch、loop 和短路候选共享，最终处置由 plan 持有。

use std::collections::{BTreeSet, VecDeque};

use crate::structure::{
    BlockRef, Cfg, DataflowFacts, EdgeRef, GraphFacts, PhiCandidate, PhiId, PhiIncomingSlot,
    SsaValue,
};
use crate::transformer::Reg;

use super::common::{
    BranchValueMergeArm, BranchValueMergeValue, LoopKindHint, LoopValueArm, LoopValueMerge,
    PhiEdgeCopy, ShortCircuitValueIncoming, StructurePlan,
};
use super::plan::{
    EdgeTransfer, PhiIncomingDisposition, PhiIncomingPlan, PhiPlan, PlanRequirement, RegionId,
    RegionPlan, StructureError,
};

mod branch_arms;
mod finalize;
mod forwarded_actions;
mod install;
mod loop_incomings;
mod ownership;

use branch_arms::*;
pub(super) use finalize::{
    CanonicalEdgeCopyTargets, build_forwarded_action_heads, effective_edge_copies,
    finalize_phi_ownership,
};
use forwarded_actions::*;
pub(super) use install::incoming_requires_edge_copy;
use install::*;
use loop_incomings::*;
use ownership::*;

pub(super) struct ShortCircuitPhiFacts {
    pub(super) entry_value: SsaValue,
    pub(super) value_incomings: Vec<ShortCircuitValueIncoming>,
}

pub(super) struct BranchValueMergeContext<'a> {
    header: BlockRef,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
}

impl<'a> BranchValueMergeContext<'a> {
    pub(super) fn new(
        _cfg: &'a Cfg,
        header: BlockRef,
        graph_facts: &'a GraphFacts,
        dataflow: &'a DataflowFacts,
    ) -> Self {
        Self {
            header,
            graph_facts,
            dataflow,
        }
    }
}

fn branch_value_merge_from_phi(
    context: &BranchValueMergeContext<'_>,
    phi: &PhiCandidate,
    then_preds: &BTreeSet<BlockRef>,
    else_preds: &BTreeSet<BlockRef>,
    ignored_preds: Option<&BTreeSet<BlockRef>>,
) -> Option<BranchValueMergeValue> {
    let entry_value = context.dataflow.block_exit_value(context.header, phi.reg);
    let mut then_arm = BranchValueMergeArm {
        preds: BTreeSet::new(),
        values: BTreeSet::new(),
        entry_values: BTreeSet::new(),
        update_values: BTreeSet::new(),
    };
    let mut else_arm = BranchValueMergeArm {
        preds: BTreeSet::new(),
        values: BTreeSet::new(),
        entry_values: BTreeSet::new(),
        update_values: BTreeSet::new(),
    };

    for incoming in &phi.incoming {
        let pred = incoming.pred?;
        if then_preds.contains(&pred) {
            extend_branch_value_arm(
                context.header,
                context.graph_facts,
                context.dataflow,
                entry_value,
                &mut then_arm,
                incoming,
            );
        } else if else_preds.contains(&pred) {
            extend_branch_value_arm(
                context.header,
                context.graph_facts,
                context.dataflow,
                entry_value,
                &mut else_arm,
                incoming,
            );
        } else if ignored_preds.is_some_and(|preds| preds.contains(&pred)) {
            continue;
        } else {
            return None;
        }
    }

    if then_arm.preds.is_empty()
        || else_arm.preds.is_empty()
        || (then_arm.values == else_arm.values
            && then_arm.update_values.is_empty()
            && else_arm.update_values.is_empty())
    {
        return None;
    }

    Some(BranchValueMergeValue {
        phi_id: phi.id,
        reg: phi.reg,
        then_arm,
        else_arm,
    })
}

pub(super) fn branch_value_merges_in_block(
    context: &BranchValueMergeContext<'_>,
    block: BlockRef,
    then_preds: &BTreeSet<BlockRef>,
    else_preds: &BTreeSet<BlockRef>,
    ignored_preds: Option<&BTreeSet<BlockRef>>,
) -> Vec<BranchValueMergeValue> {
    context
        .dataflow
        .phi_candidates_in_block(block)
        .iter()
        .filter_map(|phi| {
            branch_value_merge_from_phi(context, phi, then_preds, else_preds, ignored_preds)
        })
        .collect()
}

fn loop_value_merge_from_phi(
    phi: &PhiCandidate,
    loop_blocks: &BTreeSet<BlockRef>,
) -> LoopValueMerge {
    let mut inside_arm = LoopValueArm::default();
    let mut outside_arm = LoopValueArm::default();

    for (slot, incoming) in phi.incoming.iter().enumerate() {
        let arm = if incoming
            .pred
            .is_some_and(|pred| loop_blocks.contains(&pred))
        {
            &mut inside_arm
        } else {
            &mut outside_arm
        };
        arm.incoming_slots.push(PhiIncomingSlot(slot));
    }

    LoopValueMerge {
        phi_id: phi.id,
        reg: phi.reg,
        inside_arm,
        outside_arm,
    }
}

pub(super) fn loop_value_merges_in_block(
    dataflow: &DataflowFacts,
    block: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopValueMerge> {
    dataflow
        .phi_candidates_in_block(block)
        .iter()
        .map(|phi| loop_value_merge_from_phi(phi, loop_blocks))
        .collect()
}

pub(super) fn short_circuit_phi_facts(
    dataflow: &DataflowFacts,
    header: BlockRef,
    reg: Reg,
    value_leaves: &BTreeSet<BlockRef>,
) -> ShortCircuitPhiFacts {
    ShortCircuitPhiFacts {
        entry_value: dataflow.block_exit_value(header, reg),
        // 值叶可能先汇入中间 phi，再作为单个 incoming 进入最终 merge。这里记录
        // DAG 的真实叶 block，而不是最终 phi 的物理 predecessor，避免 HIR 再展开 phi。
        value_incomings: value_leaves
            .iter()
            .map(|pred| {
                let value = dataflow.block_exit_value(*pred, reg);
                let latest_local_def = match value {
                    SsaValue::Def(def) if dataflow.def_block(def) == *pred => Some(def),
                    _ => None,
                };
                ShortCircuitValueIncoming {
                    pred: *pred,
                    latest_local_def,
                    value,
                }
            })
            .collect(),
    }
}
