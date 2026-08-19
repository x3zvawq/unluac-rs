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
//!   分组的 incoming facts；最终 plan 再把每个 incoming 唯一归到 region input/result、
//!   loop-carried、edge copy、dead 或显式 unresolved
//! - short-circuit value merge 会提前带出 `entry_value / value_incomings`，避免 HIR
//!   再回头拆 phi

use std::collections::{BTreeSet, VecDeque};

use crate::structure::{
    BlockRef, Cfg, DataflowFacts, DefId, EdgeRef, GraphFacts, PhiCandidate, PhiId, SsaValue,
};
use crate::transformer::{LowInstr, LoweredProto, Reg};

use super::common::{
    BranchValueMergeArm, BranchValueMergeValue, LoopKindHint, LoopValueArm, LoopValueIncoming,
    LoopValueMerge, PhiEdgeCopy, ShortCircuitValueIncoming, StructurePlan,
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

/// 只解析最终 action 实际引用的透明 Move 链；dead/unreachable def 不进入计划合同。
pub(crate) struct CanonicalMoveIndex<'a> {
    proto: &'a LoweredProto,
    dataflow: &'a DataflowFacts,
    resolved: Vec<Option<SsaValue>>,
    state: Vec<u8>,
    path: Vec<DefId>,
}

impl<'a> CanonicalMoveIndex<'a> {
    pub(crate) fn new(proto: &'a LoweredProto, dataflow: &'a DataflowFacts) -> Self {
        Self {
            proto,
            dataflow,
            resolved: vec![None; dataflow.defs.len()],
            state: vec![0; dataflow.defs.len()],
            path: Vec::new(),
        }
    }

    pub(crate) fn resolve(&mut self, mut value: SsaValue) -> Result<SsaValue, StructureError> {
        self.path.clear();
        let root = loop {
            let SsaValue::Def(def) = value else {
                break value;
            };
            let definition = self.dataflow.defs.get(def.index()).ok_or_else(|| {
                StructureError::invalid(format!("edge action references missing {def}"))
            })?;
            if definition.id != def {
                return Err(StructureError::invalid(
                    "edge action references a non-dense SSA def",
                ));
            }
            if let Some(root) = self.resolved[def.index()] {
                break root;
            }
            if self.state[def.index()] == 1 {
                return Err(StructureError::invalid(
                    "transparent Move identities form an SSA cycle",
                ));
            }
            self.state[def.index()] = 1;
            self.path.push(def);
            value = match self.proto.instrs.get(definition.instr.index()) {
                Some(LowInstr::Move(move_)) if move_.dst == definition.reg => self
                    .dataflow
                    .use_values
                    .get(definition.instr.index())
                    .and_then(|uses| uses.fixed.get(move_.src))
                    .ok_or_else(|| {
                        StructureError::invalid(format!(
                            "edge action {def} Move has no canonical SSA source"
                        ))
                    })?,
                Some(_) => SsaValue::Def(def),
                None => {
                    return Err(StructureError::invalid(format!(
                        "edge action {def} references an instruction outside the proto"
                    )));
                }
            };
            if value == SsaValue::Def(def) {
                break value;
            }
        };
        for def in self.path.drain(..).rev() {
            self.resolved[def.index()] = Some(root);
            self.state[def.index()] = 2;
        }
        Ok(root)
    }
}

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
