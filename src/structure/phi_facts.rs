//! 这个文件集中承载“StructureFacts 如何消费 Dataflow phi”的共享翻译规则。
//!
//! `loops / branch_values / short_circuit` 都会把 `phi.incoming` 重新整理成更贴近
//! 源码恢复的结构事实。如果每个 pass 都各自维护一套 `incoming -> arm/value defs`
//! 转换，规则一变就会三处平行返工。这里把这层翻译集中成单一 owner，让结构层
//! 共享同一套 phi 语义。
//!
//! 它依赖 Dataflow 已经提供稳定的 `phi_candidates / reaching_defs / def 元数据`，
//! 这里只负责把这些底层 merge 事实改写成 StructureFacts 可直接消费的形状；
//! 它不会越权决定最终 HIR 表达式或语法结构。
//!
//! 例子：
//! - branch merge 会把 `phi.incoming` 直接整理成 `then_arm / else_arm` 两臂 def 集
//! - loop header/exit merge 会整理成 `inside_arm / outside_arm` 或按 predecessor
//!   分组的 incoming facts
//! - short-circuit value merge 会提前带出 `entry_defs / value_incomings`，避免 HIR
//!   再回头拆 phi

use std::collections::BTreeSet;

use crate::cfg::{BlockRef, Cfg, DataflowFacts, DefId, PhiCandidate};
use crate::transformer::Reg;

use super::common::{
    BranchValueMergeArm, BranchValueMergeCandidate, BranchValueMergeValue,
    GenericPhiMaterialization, LoopCandidate, LoopValueArm, LoopValueIncoming, LoopValueMerge,
    ShortCircuitCandidate, ShortCircuitValueIncoming,
};

pub(super) struct ShortCircuitPhiFacts {
    pub(super) entry_defs: BTreeSet<DefId>,
    pub(super) value_incomings: Vec<ShortCircuitValueIncoming>,
}

pub(super) fn branch_value_merge_from_phi(
    header: BlockRef,
    dataflow: &DataflowFacts,
    phi: &PhiCandidate,
    then_preds: &BTreeSet<BlockRef>,
    else_preds: &BTreeSet<BlockRef>,
) -> Option<BranchValueMergeValue> {
    let mut then_arm = BranchValueMergeArm {
        preds: BTreeSet::new(),
        defs: BTreeSet::new(),
        non_header_defs: BTreeSet::new(),
    };
    let mut else_arm = BranchValueMergeArm {
        preds: BTreeSet::new(),
        defs: BTreeSet::new(),
        non_header_defs: BTreeSet::new(),
    };

    for incoming in &phi.incoming {
        if then_preds.contains(&incoming.pred) {
            extend_branch_value_arm(header, dataflow, &mut then_arm, incoming);
        } else if else_preds.contains(&incoming.pred) {
            extend_branch_value_arm(header, dataflow, &mut else_arm, incoming);
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
    header: BlockRef,
    dataflow: &DataflowFacts,
    block: BlockRef,
    then_preds: &BTreeSet<BlockRef>,
    else_preds: &BTreeSet<BlockRef>,
) -> Vec<BranchValueMergeValue> {
    dataflow
        .phi_candidates_in_block(block)
        .iter()
        .filter_map(|phi| {
            branch_value_merge_from_phi(header, dataflow, phi, then_preds, else_preds)
        })
        .collect()
}

pub(super) fn loop_value_merge_from_phi(
    phi: &PhiCandidate,
    loop_blocks: &BTreeSet<BlockRef>,
) -> Option<LoopValueMerge> {
    let mut inside_arm = LoopValueArm::default();
    let mut outside_arm = LoopValueArm::default();

    for incoming in &phi.incoming {
        let arm = if loop_blocks.contains(&incoming.pred) {
            &mut inside_arm
        } else {
            &mut outside_arm
        };
        arm.incomings.push(LoopValueIncoming {
            pred: incoming.pred,
            defs: incoming.defs.clone(),
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
        .filter_map(|phi| loop_value_merge_from_phi(phi, loop_blocks))
        .collect()
}

pub(super) fn short_circuit_phi_facts(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    header: BlockRef,
    reg: Reg,
    phi: &PhiCandidate,
) -> ShortCircuitPhiFacts {
    ShortCircuitPhiFacts {
        entry_defs: value_merge_entry_defs(cfg, dataflow, header, reg),
        value_incomings: phi
            .incoming
            .iter()
            .map(|incoming| ShortCircuitValueIncoming {
                pred: incoming.pred,
                defs: incoming.defs.clone(),
                latest_local_def: latest_local_incoming_def(
                    dataflow,
                    incoming.pred,
                    &incoming.defs,
                ),
            })
            .collect(),
    }
}

pub(super) fn analyze_generic_phi_materializations(
    dataflow: &DataflowFacts,
    branch_value_merge_candidates: &[BranchValueMergeCandidate],
    loop_candidates: &[LoopCandidate],
    short_circuit_candidates: &[ShortCircuitCandidate],
) -> Vec<GenericPhiMaterialization> {
    let mut covered = short_circuit_candidates
        .iter()
        .filter_map(|candidate| candidate.result_phi_id)
        .collect::<BTreeSet<_>>();
    covered.extend(
        branch_value_merge_candidates
            .iter()
            .flat_map(|candidate| candidate.values.iter().map(|value| value.phi_id)),
    );
    covered.extend(loop_value_merge_ids(loop_candidates));

    let mut generic = dataflow
        .phi_candidates
        .iter()
        .filter(|phi| !covered.contains(&phi.id))
        .map(|phi| GenericPhiMaterialization {
            block: phi.block,
            phi_id: phi.id,
            reg: phi.reg,
        })
        .collect::<Vec<_>>();
    generic.sort_by_key(|phi| (phi.block, phi.phi_id));
    generic
}

fn extend_branch_value_arm(
    header: BlockRef,
    dataflow: &DataflowFacts,
    arm: &mut BranchValueMergeArm,
    incoming: &crate::cfg::PhiIncoming,
) {
    arm.preds.insert(incoming.pred);
    for &def in &incoming.defs {
        arm.defs.insert(def);
        if dataflow.def_block(def) != header {
            arm.non_header_defs.insert(def);
        }
    }
}

fn latest_local_incoming_def(
    dataflow: &DataflowFacts,
    block: BlockRef,
    defs: &BTreeSet<DefId>,
) -> Option<DefId> {
    dataflow.latest_local_def_in_block(block, defs.iter().copied())
}

fn value_merge_entry_defs(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    header: BlockRef,
    reg: Reg,
) -> BTreeSet<DefId> {
    let Some(instr_ref) = cfg.blocks[header.index()].instrs.last() else {
        return BTreeSet::new();
    };

    dataflow
        .reaching_defs_at(instr_ref)
        .fixed
        .get(reg)
        .map(|defs| defs.iter().copied().collect())
        .unwrap_or_default()
}

fn loop_value_merge_ids(
    loop_candidates: &[LoopCandidate],
) -> impl Iterator<Item = crate::cfg::PhiId> + '_ {
    loop_candidates.iter().flat_map(|candidate| {
        candidate
            .header_value_merges
            .iter()
            .map(|value| value.phi_id)
            .chain(
                candidate
                    .exit_value_merges
                    .iter()
                    .flat_map(|exit| exit.values.iter().map(|value| value.phi_id)),
            )
    })
}
