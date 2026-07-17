//! 这个文件集中承载“StructureFacts 如何消费 Dataflow phi”的共享翻译规则。
//!
//! `loops / branch_values / short_circuit` 都会把 `phi.incoming` 重新整理成更贴近
//! 源码恢复的结构事实。如果每个 pass 都各自维护一套 `incoming -> arm/value identity`
//! 转换，规则一变就会三处平行返工。这里把这层翻译集中成单一 owner，让结构层
//! 共享同一套 phi 语义。
//!
//! 它依赖 Dataflow 已经提供稳定的 `phi_candidates / SsaValue / def 元数据`，
//! 这里只负责把这些底层 merge 事实改写成 StructureFacts 可直接消费的形状；
//! 它不会越权决定最终 HIR 表达式或语法结构。
//!
//! 例子：
//! - branch merge 会把 `phi.incoming` 直接整理成 `then_arm / else_arm` 两臂 SSA 值集
//! - loop header/exit merge 会整理成 `inside_arm / outside_arm` 或按 predecessor
//!   分组的 incoming facts；branch 已完整覆盖两臂时拥有更外层的 exit phi，loop 只保留
//!   自己需要接管的出口值；generic owner 只排除确定已有结构 owner 的 phi
//! - short-circuit value merge 会提前带出 `entry_value / value_incomings`，避免 HIR
//!   再回头拆 phi

use std::collections::{BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, DataflowFacts, GraphFacts, PhiCandidate, PhiId, SsaValue};
use crate::transformer::Reg;

use super::common::{
    BranchValueMergeArm, BranchValueMergeCandidate, BranchValueMergeValue,
    GenericPhiMaterialization, GenericPhiSource, GotoReason, GotoRequirement, LoopCandidate,
    LoopValueArm, LoopValueIncoming, LoopValueMerge, PhiEdgeCopy, ShortCircuitCandidate,
    ShortCircuitValueIncoming, StructurePlan,
};
use super::plan::{EdgeOwner, PhiIncomingDisposition};

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

pub(super) fn loop_value_merge_from_phi(
    _dataflow: &DataflowFacts,
    phi: &PhiCandidate,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<LoopValueMerge> {
    let mut inside_arm = LoopValueArm::default();
    let mut outside_arm = LoopValueArm::default();

    for incoming in &phi.incoming {
        let arm = if incoming
            .pred
            .is_some_and(|pred| loop_blocks.contains(&pred))
        {
            &mut inside_arm
        } else {
            &mut outside_arm
        };
        arm.incomings.push(LoopValueIncoming {
            pred: incoming.pred,
            value: incoming.value,
        });
    }

    Some(LoopValueMerge {
        phi_id: phi.id,
        reg: phi.reg,
        inside_arm,
        outside_arm,
    })
}

pub(super) fn loop_value_merges_in_block(
    dataflow: &DataflowFacts,
    block: BlockRef,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Vec<LoopValueMerge> {
    dataflow
        .phi_candidates_in_block(block)
        .iter()
        .filter_map(|phi| loop_value_merge_from_phi(dataflow, phi, loop_blocks))
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

pub(super) fn analyze_generic_phi_materializations(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_value_merge_candidates: &[BranchValueMergeCandidate],
    plan: &StructurePlan,
    loop_candidates: &[LoopCandidate],
    short_circuit_candidates: &[ShortCircuitCandidate],
) -> Vec<GenericPhiMaterialization> {
    let mut covered = short_circuit_candidates
        .iter()
        .filter(|candidate| candidate.reducible)
        .filter_map(|candidate| candidate.result_phi_id)
        .collect::<BTreeSet<_>>();
    covered.extend(consumed_branch_value_merge_ids(
        branch_value_merge_candidates,
        plan,
    ));
    covered.extend(consumed_loop_header_phi_ids(loop_candidates));
    extend_transitive_structured_phi_owners(dataflow, &mut covered);

    for phi in &dataflow.phi_candidates {
        assert!(
            !plan.phi_has_edge_copy(phi.id)
                || plan.phi_is_edge_owned(phi.id)
                || covered.contains(&phi.id)
                || plan.phi_is_dead(phi.id),
            "mixed edge/merge {} must have a structured merge owner",
            phi.id
        );
    }

    let mut generic = dataflow
        .phi_candidates
        .iter()
        .filter(|phi| !covered.contains(&phi.id))
        .filter(|phi| !plan.phi_is_dead(phi.id))
        .filter(|phi| !plan.phi_has_edge_copy(phi.id))
        .map(|phi| GenericPhiMaterialization {
            block: phi.block,
            phi_id: phi.id,
            reg: phi.reg,
            source: generic_phi_source(cfg, graph_facts, dataflow, phi),
        })
        .collect::<Vec<_>>();
    generic.sort_by_key(|phi| (phi.block, phi.phi_id));
    generic
}

/// 结构 owner 会从目标 phi 递归读取 incoming 的 leaf defs，因此只作为这些目标的
/// SSA 中继、且没有指令直接读取的上游 phi 不需要再单独物化。
fn extend_transitive_structured_phi_owners(
    dataflow: &DataflowFacts,
    covered: &mut BTreeSet<PhiId>,
) {
    let mut pending = covered.iter().copied().collect::<VecDeque<_>>();
    while let Some(phi_id) = pending.pop_front() {
        let Some(phi) = dataflow.phi_candidate(phi_id) else {
            continue;
        };
        for incoming in &phi.incoming {
            let SsaValue::Phi(upstream) = incoming.value else {
                continue;
            };
            if covered.contains(&upstream)
                || dataflow.phi_use_count(upstream) != 0
                || !dataflow
                    .phi_consumer_ids(upstream)
                    .iter()
                    .all(|consumer| covered.contains(consumer))
            {
                continue;
            }
            covered.insert(upstream);
            pending.push_back(upstream);
        }
    }
}

pub(super) fn analyze_phi_incoming_dispositions(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    goto_requirements: &[GotoRequirement],
) -> (Vec<Vec<PhiIncomingDisposition>>, Vec<Vec<PhiEdgeCopy>>) {
    let dead_phis = dataflow.compute_truly_dead_phis();
    let mut dispositions = Vec::with_capacity(dataflow.phi_candidates.len());
    let mut edge_copies = vec![Vec::new(); cfg.edges.len()];
    for phi in &dataflow.phi_candidates {
        if dead_phis.contains(&phi.id) {
            dispositions.push(vec![PhiIncomingDisposition::Dead; phi.incoming.len()]);
            continue;
        }

        let mut phi_dispositions = Vec::with_capacity(phi.incoming.len());
        for incoming in &phi.incoming {
            let disposition = incoming
                .edge
                .map_or(PhiIncomingDisposition::Merge, |edge_ref| {
                    let edge = cfg.edges[edge_ref.index()];
                    if matches!(plan.edge_owners[edge_ref.index()], EdgeOwner::Unreachable) {
                        PhiIncomingDisposition::Unreachable
                    } else if matches!(
                        plan.edge_owners[edge_ref.index()],
                        EdgeOwner::Goto(id)
                            if goto_requirements[id.index()].reason
                                != GotoReason::UnstructuredContinueLike
                    ) || plan.unstructured_layout_by_block[edge.from.index()].is_some()
                    {
                        edge_copies[edge_ref.index()].push(PhiEdgeCopy {
                            phi_id: phi.id,
                            value: incoming.value,
                        });
                        PhiIncomingDisposition::EdgeCopy
                    } else {
                        PhiIncomingDisposition::Merge
                    }
                });
            phi_dispositions.push(disposition);
        }
        dispositions.push(phi_dispositions);
    }
    (dispositions, edge_copies)
}

/// 外层 branch 已完整解释两臂来源时，不让内层 loop 再物化同一个出口 phi。
pub(super) fn remove_branch_owned_loop_exit_values(
    loop_candidates: &mut [LoopCandidate],
    branch_candidates: &[BranchValueMergeCandidate],
    plan: &StructurePlan,
    dataflow: &DataflowFacts,
) {
    let branch_owned = consumed_branch_value_merge_values(branch_candidates, plan)
        .filter(|value| {
            let phi = &dataflow.phi_candidates[value.phi_id.index()];
            phi.incoming.iter().all(|incoming| {
                incoming.pred.is_some_and(|pred| {
                    value.then_arm.preds.contains(&pred) || value.else_arm.preds.contains(&pred)
                })
            })
        })
        .map(|value| value.phi_id)
        .collect::<BTreeSet<_>>();
    for candidate in loop_candidates {
        for exit in &mut candidate.exit_value_merges {
            exit.values
                .retain(|value| !branch_owned.contains(&value.phi_id));
        }
        candidate
            .exit_value_merges
            .retain(|exit| !exit.values.is_empty());
    }
}

/// 相邻 loop 共用边界 block 时，后继 header phi 只归后继 loop state。
pub(super) fn remove_loop_header_owned_loop_exit_values(candidates: &mut [LoopCandidate]) {
    let header_owned = candidates
        .iter()
        .flat_map(|candidate| {
            candidate
                .header_value_merges
                .iter()
                .map(move |value| (candidate.header, value.phi_id))
        })
        .collect::<BTreeSet<_>>();

    for candidate in candidates {
        for exit in &mut candidate.exit_value_merges {
            exit.values
                .retain(|value| !header_owned.contains(&(exit.exit, value.phi_id)));
        }
        candidate
            .exit_value_merges
            .retain(|exit| !exit.values.is_empty());
    }
}

fn consumed_branch_value_merge_ids<'a>(
    candidates: &'a [BranchValueMergeCandidate],
    plan: &'a StructurePlan,
) -> impl Iterator<Item = PhiId> + 'a {
    consumed_branch_value_merge_values(candidates, plan).map(|value| value.phi_id)
}

fn consumed_branch_value_merge_values<'a>(
    candidates: &'a [BranchValueMergeCandidate],
    plan: &'a StructurePlan,
) -> impl Iterator<Item = &'a BranchValueMergeValue> + 'a {
    plan.branch_value_merge_by_region
        .values()
        .filter_map(|id| candidates.get(id.index()))
        .flat_map(|candidate| &candidate.values)
}

fn generic_phi_source(
    _cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    phi: &PhiCandidate,
) -> GenericPhiSource {
    let Some(idom) = graph_facts
        .dominator_tree
        .parent
        .get(phi.block.index())
        .copied()
        .flatten()
    else {
        return GenericPhiSource::Unresolved;
    };
    let idom_value = dataflow.block_exit_value(idom, phi.reg);
    if phi
        .incoming
        .iter()
        .all(|incoming| incoming.value == idom_value)
    {
        GenericPhiSource::IdomExit(idom)
    } else {
        GenericPhiSource::Unresolved
    }
}

fn extend_branch_value_arm(
    header: BlockRef,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    entry_value: SsaValue,
    arm: &mut BranchValueMergeArm,
    incoming: &crate::structure::PhiIncoming,
) {
    let Some(pred) = incoming.pred else {
        return;
    };
    arm.preds.insert(pred);
    arm.values.insert(incoming.value);
    let carries_entry = dataflow.value_contains(incoming.value, entry_value);
    // 非循环 header 的当前入口值不可能包含一个由 header 严格支配的定义；若能从
    // header 之后重新流回入口，就已经构成 backedge。顺序 branch 的 preserved arm
    // 因而无需反复展开随前序分支增长的整条 Phi 链。
    let needs_dominated_update_check = carries_entry
        && (incoming.value != entry_value || graph_facts.loop_headers.contains(&header));
    let is_dominated_update = needs_dominated_update_check
        && dataflow.leaf_defs(incoming.value).iter().any(|def| {
            let block = dataflow.def_block(*def);
            block != header && graph_facts.dominator_tree.dominates(header, block)
        });
    if carries_entry {
        arm.entry_values.insert(incoming.value);
    }
    if !carries_entry || is_dominated_update {
        arm.update_values.insert(incoming.value);
    }
}

fn consumed_loop_header_phi_ids(
    loop_candidates: &[LoopCandidate],
) -> impl Iterator<Item = PhiId> + '_ {
    loop_candidates.iter().flat_map(|candidate| {
        candidate
            .header_value_merges
            .iter()
            .map(|value| value.phi_id)
    })
}
