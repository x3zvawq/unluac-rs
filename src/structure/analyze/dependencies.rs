//! 为条件与值决策标记控制域内部的固定值和开放包依赖。
//! 区域外 producer 与入口 phi 是输入边界，不展开其历史；标记仅属于当前 CFG/SSA 快照。

use super::{Cfg, DataflowFacts};
use crate::structure::BlockRef;
use crate::structure::cfg::EvaluationDependency;

pub(super) struct DependencyMarks<'a> {
    pub(super) instructions: &'a mut [usize],
    pub(super) defs: &'a mut [usize],
    pub(super) phis: &'a mut [usize],
    pub(super) epoch: usize,
}

/// 调用方提供控制域及本次标记代次；already_proven 只能引用同域内已成功完成的闭包。
pub(super) fn mark_region_dependencies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    contains_block: impl Fn(BlockRef) -> bool,
    marks: DependencyMarks<'_>,
    pending_values: &mut Vec<EvaluationDependency>,
    roots: impl IntoIterator<Item = EvaluationDependency>,
    already_proven: impl Fn(super::super::SsaValue) -> bool,
) -> bool {
    pending_values.clear();
    pending_values.extend(roots);
    while let Some(dependency) = pending_values.pop() {
        if matches!(dependency, EvaluationDependency::Value(value) if already_proven(value)) {
            continue;
        }
        match dependency {
            EvaluationDependency::Value(super::super::SsaValue::Entry(_)) => {}
            EvaluationDependency::Value(super::super::SsaValue::Def(def)) => {
                let Some(stamp) = marks.defs.get_mut(def.index()) else {
                    return false;
                };
                if *stamp == marks.epoch {
                    continue;
                }
                *stamp = marks.epoch;
                let Some(definition) = dataflow.defs.get(def.index()) else {
                    return false;
                };
                pending_values.push(EvaluationDependency::Instruction(definition.instr));
            }
            EvaluationDependency::Instruction(instr) => {
                let Some(block) = cfg.instr_to_block.get(instr.index()) else {
                    return false;
                };
                if !contains_block(*block) {
                    continue;
                }
                let Some(needed) = marks.instructions.get_mut(instr.index()) else {
                    return false;
                };
                if *needed == marks.epoch {
                    continue;
                }
                *needed = marks.epoch;
                pending_values.extend(dataflow.evaluation_inputs(instr));
            }
            EvaluationDependency::Value(super::super::SsaValue::Phi(phi)) => {
                let Some(stamp) = marks.phis.get_mut(phi.index()) else {
                    return false;
                };
                if *stamp == marks.epoch {
                    continue;
                }
                *stamp = marks.epoch;
                let Some(phi) = dataflow.phi_candidate(phi) else {
                    return false;
                };
                // 候选入口上的 phi 是显式 RegionInput。继续展开它的历史
                // incoming 不仅越过当前控制域，也会让连续 value-decision
                // 沿整条 SSA 链重复回溯。
                if !contains_block(phi.block)
                    || phi.incoming.iter().any(|incoming| {
                        incoming
                            .edge
                            .and_then(|edge| cfg.edges.get(edge.index()))
                            .is_none_or(|edge| !contains_block(edge.from))
                    })
                {
                    continue;
                }
                pending_values.extend(
                    phi.incoming
                        .iter()
                        .map(|incoming| EvaluationDependency::Value(incoming.value)),
                );
            }
        }
    }
    true
}
