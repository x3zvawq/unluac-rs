//! 汇总 loop phi、使用范围和 VM for 控制值分析；依赖 SSA/区域导航，不负责冻结语法协议；例如判断 carried phi 是否在 control 外被观察。

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
        if dataflow.phi_phi_uses.len() != phi_count || dataflow.phi_uses.len() != phi_count {
            return Err(StructureError::invalid(
                "loop value analysis received a sparse phi-use index",
            ));
        }

        let mut reverse_uses = vec![Vec::<usize>::new(); phi_count];
        for (source, consumers) in dataflow.phi_phi_uses.iter().enumerate() {
            for consumer in consumers {
                let Some(sources) = reverse_uses.get_mut(consumer.index()) else {
                    return Err(StructureError::invalid(
                        "loop value analysis found a missing phi consumer",
                    ));
                };
                sources.push(source);
            }
        }

        let mut visited = vec![false; phi_count];
        let mut finish_order = Vec::with_capacity(phi_count);
        for start in 0..phi_count {
            if visited[start] {
                continue;
            }
            let mut pending = vec![(start, false)];
            while let Some((phi, leaving)) = pending.pop() {
                if leaving {
                    finish_order.push(phi);
                    continue;
                }
                if std::mem::replace(&mut visited[phi], true) {
                    continue;
                }
                pending.push((phi, true));
                for consumer in dataflow.phi_phi_uses[phi].iter().rev() {
                    if consumer.index() >= phi_count {
                        return Err(StructureError::invalid(
                            "loop value analysis found a missing phi consumer",
                        ));
                    }
                    if !visited[consumer.index()] {
                        pending.push((consumer.index(), false));
                    }
                }
            }
        }

        let mut component_by_phi = vec![usize::MAX; phi_count];
        let mut components = Vec::<Vec<usize>>::new();
        for start in finish_order.into_iter().rev() {
            if component_by_phi[start] != usize::MAX {
                continue;
            }
            let component = components.len();
            let mut members = Vec::new();
            let mut pending = vec![start];
            component_by_phi[start] = component;
            while let Some(phi) = pending.pop() {
                members.push(phi);
                for source in &reverse_uses[phi] {
                    if component_by_phi[*source] == usize::MAX {
                        component_by_phi[*source] = component;
                        pending.push(*source);
                    }
                }
            }
            components.push(members);
        }

        let mut component_edges = vec![Vec::<usize>::new(); components.len()];
        let mut indegree = vec![0usize; components.len()];
        for (source, consumers) in dataflow.phi_phi_uses.iter().enumerate() {
            let source_component = component_by_phi[source];
            for consumer in consumers {
                let consumer_component = component_by_phi[consumer.index()];
                if source_component == consumer_component {
                    continue;
                }
                component_edges[source_component].push(consumer_component);
                indegree[consumer_component] =
                    indegree[consumer_component].checked_add(1).ok_or_else(|| {
                        StructureError::invalid("loop value analysis indegree overflowed")
                    })?;
            }
        }
        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(component, degree)| (*degree == 0).then_some(component))
            .collect::<VecDeque<_>>();
        let mut topo = Vec::with_capacity(components.len());
        while let Some(component) = ready.pop_front() {
            topo.push(component);
            for consumer in &component_edges[component] {
                indegree[*consumer] -= 1;
                if indegree[*consumer] == 0 {
                    ready.push_back(*consumer);
                }
            }
        }
        if topo.len() != components.len() {
            return Err(StructureError::invalid(
                "loop value analysis failed to condense the phi graph",
            ));
        }

        let mut component_extents = vec![PhiUseExtent::default(); components.len()];
        for (phi, uses) in dataflow.phi_uses.iter().enumerate() {
            let extent = &mut component_extents[component_by_phi[phi]];
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
        for component in topo.iter().rev().copied() {
            for consumer in &component_edges[component] {
                let consumer_extent = component_extents[*consumer];
                component_extents[component].merge(consumer_extent);
            }
        }
        let use_extents = component_by_phi
            .iter()
            .map(|component| component_extents[*component])
            .collect();

        let mut vm_for_control = vec![false; phi_count];
        for component in topo {
            let [phi] = components[component].as_slice() else {
                continue;
            };
            let Some(candidate) = dataflow.phi_candidates.get(*phi) else {
                continue;
            };
            if candidate.id.index() != *phi
                || candidate.incoming.is_empty()
                || candidate
                    .incoming
                    .iter()
                    .any(|incoming| incoming.value == SsaValue::Phi(candidate.id))
            {
                continue;
            }
            vm_for_control[*phi] = candidate
                .incoming
                .iter()
                .all(|incoming| match incoming.value {
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
    dataflow.defs.get(def.index()).is_some_and(|definition| {
        matches!(
            proto.instrs.get(definition.instr.index()),
            Some(
                LowInstr::NumericForInit(_)
                    | LowInstr::NumericForLoop(_)
                    | LowInstr::GenericForPrep(_)
                    | LowInstr::GenericForCall(_)
                    | LowInstr::GenericForLoop(_)
            )
        )
    })
}
