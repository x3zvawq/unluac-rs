//! 汇总 loop phi、使用范围和 VM for 控制值分析，依赖 canonical SSA 与区域导航。
//! 直接借用 Dataflow 的分量/使用边与拓扑顺序；本层只传播区域使用范围，
//! 不负责冻结语法协议。例如 consumer 在 control 外被观察时，其上游 carried phi 也被标记。

use super::*;

impl LoopValueAnalysis {
    pub(super) fn build(
        proto: &LoweredProto,
        cfg: &Cfg,
        graph_facts: &GraphFacts,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
    ) -> Result<Self, StructureError> {
        let phi_count = dataflow.phi_candidates.len();
        let components = dataflow.phi_graph.components();
        let mut component_extents = vec![PhiUseExtent::default(); components.len()];
        for (phi, uses) in dataflow.phi_uses.iter().enumerate() {
            let extent = &mut component_extents[dataflow.phi_graph.component_index(PhiId(phi))];
            for site in uses {
                let owner = cfg
                    .instr_to_block
                    .get(site.instr.index())
                    .copied()
                    .and_then(|block| plan.region_for_block(block));
                let position = owner
                    .and_then(|owner| plan.navigation.preorder_index.get(owner.index()).copied());
                if let Some(position) = position.filter(|position| *position != usize::MAX) {
                    extent.include_region(position);
                } else {
                    extent.has_unowned_use = true;
                }
            }
        }
        // Dataflow 按源到汇签发分量；从汇反向传播，直接消费 canonical use 边，
        // 不另建 condensation 邻接表或再排序同一 DAG。重复边只重复幂等的范围合并。
        for (component, members) in components.iter().enumerate().rev() {
            for phi in members {
                for consumer in &dataflow.phi_phi_uses[phi.index()] {
                    let consumer_component = dataflow.phi_graph.component_index(*consumer);
                    if component != consumer_component {
                        let consumer_extent = component_extents[consumer_component];
                        component_extents[component].merge(consumer_extent);
                    }
                }
            }
        }
        let use_extents = (0..phi_count)
            .map(|phi| component_extents[dataflow.phi_graph.component_index(PhiId(phi))])
            .collect();

        let mut vm_for_control = vec![false; phi_count];
        for members in components {
            let [phi] = members.as_slice() else {
                continue;
            };
            let Some(candidate) = dataflow.phi_candidates.get(phi.index()) else {
                continue;
            };
            if candidate.id != *phi
                || candidate.incoming.is_empty()
                || candidate
                    .incoming
                    .iter()
                    .any(|incoming| incoming.value == SsaValue::Phi(candidate.id))
            {
                continue;
            }
            vm_for_control[phi.index()] = candidate.incoming.iter().all(|incoming| match incoming
                .value
            {
                SsaValue::Entry(_) => false,
                SsaValue::Def(def) => def_is_vm_for_control(proto, dataflow, def),
                SsaValue::Phi(source) => {
                    vm_for_control.get(source.index()).copied().unwrap_or(false)
                }
            });
        }

        let mut absorbed_owner_by_edge = vec![None; cfg.edges.len()];
        for (loop_id, payload) in plan.loops() {
            if !matches!(
                payload.kind,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            ) {
                continue;
            }
            let region = plan
                .loop_region(loop_id)
                .ok_or_else(|| StructureError::invalid("VM-for has no owning region"))?;
            for edge in absorbed_value_edges(cfg, graph_facts, dataflow, plan, region, payload)? {
                let slot = absorbed_owner_by_edge
                    .get_mut(edge.index())
                    .ok_or_else(|| {
                        StructureError::invalid("loop value action references a missing CFG edge")
                    })?;
                if slot.replace(loop_id).is_some() {
                    return Err(StructureError::invalid(format!(
                        "CFG edge {edge} is absorbed by multiple loop protocols"
                    )));
                }
            }
        }

        Ok(Self {
            vm_for_control,
            use_extents,
            absorbed_owner_by_edge,
        })
    }

    pub(super) fn value_is_vm_for_control(
        &self,
        proto: &LoweredProto,
        dataflow: &DataflowFacts,
        value: SsaValue,
    ) -> bool {
        match value {
            SsaValue::Def(def) => def_is_vm_for_control(proto, dataflow, def),
            SsaValue::Phi(phi) => self
                .vm_for_control
                .get(phi.index())
                .copied()
                .unwrap_or(false),
            SsaValue::Entry(_) => false,
        }
    }

    pub(super) fn phi_observed_outside(
        &self,
        plan: &StructurePlan,
        control: RegionId,
        phi: PhiId,
    ) -> bool {
        let Some(extent) = self.use_extents.get(phi.index()).copied() else {
            return true;
        };
        if extent.has_unowned_use {
            return true;
        }
        if !extent.has_region {
            return false;
        }
        let Some((start, end)) = plan
            .navigation
            .preorder_index
            .get(control.index())
            .copied()
            .zip(plan.navigation.subtree_end.get(control.index()).copied())
        else {
            return true;
        };
        extent.first_region < start || extent.last_region >= end
    }
}

pub(super) fn def_is_vm_for_control(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    def: crate::structure::DefId,
) -> bool {
    // GenericForCall 定义用户可见的迭代变量，即使与 control 共槽也不是隐藏值；
    // 它们可作为内层循环的普通输入。独立的 control 写回由 GenericForLoop 定义。
    dataflow.defs.get(def.index()).is_some_and(|definition| {
        matches!(
            proto.instrs.get(definition.instr.index()),
            Some(
                LowInstr::NumericForInit(_)
                    | LowInstr::NumericForLoop(_)
                    | LowInstr::GenericForPrep(_)
                    | LowInstr::GenericForLoop(_)
            )
        )
    })
}
