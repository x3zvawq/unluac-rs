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

use std::collections::BTreeSet;

use crate::structure::{BlockRef, Cfg, DataflowFacts, GraphFacts, PhiCandidate, PhiId, SsaValue};
use crate::transformer::Reg;

use super::common::{
    BranchValueMergeArm, BranchValueMergeCandidate, BranchValueMergeValue,
    GenericPhiMaterialization, GenericPhiSource, LoopCandidate, LoopValueArm, LoopValueIncoming,
    LoopValueMerge, ShortCircuitCandidate, ShortCircuitValueIncoming, StructurePlan,
};

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

    (!then_arm.preds.is_empty() && !else_arm.preds.is_empty()).then_some(BranchValueMergeValue {
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
    _cfg: &Cfg,
    dataflow: &DataflowFacts,
    header: BlockRef,
    reg: Reg,
    phi: &PhiCandidate,
) -> ShortCircuitPhiFacts {
    ShortCircuitPhiFacts {
        entry_value: dataflow.block_exit_value(header, reg),
        value_incomings: phi
            .incoming
            .iter()
            .filter_map(|incoming| {
                let pred = incoming.pred?;
                let latest_local_def = match incoming.value {
                    SsaValue::Def(def) if dataflow.def_block(def) == pred => Some(def),
                    _ => None,
                };
                Some(ShortCircuitValueIncoming {
                    pred,
                    latest_local_def,
                    value: incoming.value,
                })
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

    let mut generic = dataflow
        .phi_candidates
        .iter()
        .filter(|phi| !covered.contains(&phi.id))
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

/// 外层 branch 已完整解释两臂来源时，不让内层 loop 再物化同一个出口 phi。
pub(super) fn remove_branch_owned_loop_exit_values(
    loop_candidates: &mut [LoopCandidate],
    branch_candidates: &[BranchValueMergeCandidate],
    plan: &StructurePlan,
) {
    let branch_owned =
        consumed_branch_value_merge_ids(branch_candidates, plan).collect::<BTreeSet<_>>();
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
    plan.branch_value_merge_by_header
        .values()
        .filter_map(|id| candidates.get(id.index()))
        .flat_map(|candidate| candidate.values.iter().map(|value| value.phi_id))
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
