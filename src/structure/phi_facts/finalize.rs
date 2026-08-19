//! 编排最终 phi ownership、收集稠密边动作并提供 canonical copy 查询；依赖冻结 StructurePlan，不负责转发链求值；例如把唯一 incoming 写入对应 EdgePlan。

use super::*;

/// 完成最终 plan 的 value ownership，并把 canonical copies 直接写入对应 edge。
///
/// 这一步只消费已选中的 region payload。任何无法证明唯一 owner 的 live incoming 都
/// 显式标记为 `DiagnosticUnresolved`，不能再交给 HIR 猜一个 predecessor。
pub(in crate::structure) fn finalize_phi_ownership(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    validate_phi_arena(dataflow)?;
    let island_regions = regions_owned_by_island_graph(plan)?;
    let owner_index = RegionOwnerIndex::new(plan)?;
    let mut dispositions = dataflow
        .phi_candidates
        .iter()
        .map(|phi| vec![None; phi.incoming.len()])
        .collect::<Vec<Vec<Option<PhiIncomingDisposition>>>>();

    for phi in &dataflow.phi_candidates {
        if dataflow.phi_is_truly_dead(phi.id) {
            dispositions[phi.id.index()].fill(Some(PhiIncomingDisposition::Dead));
            continue;
        }
        let has_structured_value_owner = plan.condition_value_owner(phi.id).is_some()
            || plan.value_decision_owner(phi.id).is_some();
        for (incoming_index, incoming) in phi.incoming.iter().enumerate() {
            let Some(edge_ref) = incoming.edge else {
                continue;
            };
            let edge_plan = plan.edge_plan(edge_ref).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} incoming #{incoming_index} references missing edge {edge_ref}",
                    phi.id
                ))
            })?;
            let edge = cfg.edges.get(edge_ref.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} incoming #{incoming_index} references edge {edge_ref} outside CFG",
                    phi.id
                ))
            })?;
            let target_island_owned = plan
                .region_for_block(edge.to)
                .and_then(|region| island_regions.get(region.index()))
                .copied()
                .unwrap_or(false);
            let disposition = if matches!(edge_plan.transfer, EdgeTransfer::Unreachable) {
                PhiIncomingDisposition::Dead
            } else if matches!(edge_plan.transfer, EdgeTransfer::Goto(..))
                || island_regions
                    .get(edge_plan.owner.index())
                    .copied()
                    .unwrap_or(false)
                // island 可以从 structured value 的 merge block 开始；这时 phi 仍由
                // 前一 region 产出，不能仅因目标 block 属于 island 就降级为 edge copy。
                || (target_island_owned && !has_structured_value_owner)
            {
                PhiIncomingDisposition::EdgeCopy
            } else {
                continue;
            };
            dispositions[phi.id.index()][incoming_index] = Some(disposition);
        }
    }

    claim_selected_region_values(dataflow, plan, &owner_index, &mut dispositions)?;
    claim_idom_inputs(graph_facts, dataflow, plan, &owner_index, &mut dispositions)?;
    propagate_transitive_region_owners(dataflow, &owner_index, &mut dispositions)?;

    let mut unresolved = BTreeSet::new();
    let dispositions = dataflow
        .phi_candidates
        .iter()
        .zip(dispositions)
        .map(|(phi, owners)| {
            phi.incoming
                .iter()
                .zip(owners)
                .map(|(incoming, owner)| {
                    match (owner, incoming.edge) {
                        // Structured owners may conflict when one live-through phi feeds two
                        // enclosing loop states. A physical CFG edge is still an exact execution
                        // point, so its canonical copy is the unique lossless disposition.
                        (None | Some(PhiIncomingDisposition::DiagnosticUnresolved), Some(_)) => {
                            PhiIncomingDisposition::EdgeCopy
                        }
                        (Some(owner), _) => owner,
                        (None, None) => {
                            unresolved.insert(phi.id);
                            PhiIncomingDisposition::DiagnosticUnresolved
                        }
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    unresolved.extend(
        dispositions
            .iter()
            .enumerate()
            .filter(|(_, owners)| owners.contains(&PhiIncomingDisposition::DiagnosticUnresolved))
            .map(|(index, _)| PhiId(index)),
    );

    let edge_copies = collect_dense_edge_actions(cfg, dataflow, plan, &dispositions)?;

    for (edge_index, copies) in edge_copies.into_iter().enumerate() {
        let edge_plan = plan
            .edge_plans
            .get_mut(edge_index)
            .ok_or_else(|| StructureError::invalid(format!("missing edge plan #{edge_index}")))?;
        edge_plan.phi_copies = copies;
    }
    plan.forward_action_head = build_forwarded_action_heads(plan)?;
    install_phi_plans(cfg, dataflow, plan, dispositions)?;
    install_unresolved_requirements(plan, dataflow, unresolved)?;
    validate_phi_ownership(cfg, dataflow, plan)
}

pub(super) fn collect_dense_edge_actions(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    dispositions: &[Vec<PhiIncomingDisposition>],
) -> Result<Vec<Vec<PhiEdgeCopy>>, StructureError> {
    let mut actions = vec![Vec::new(); cfg.edges.len()];
    let canonical_targets = CanonicalEdgeCopyTargets::build(plan, dataflow.phi_candidates.len())?;
    // `usize::MAX` 代表尚未见过；edge arena 本身不可能拥有这个下标。
    let mut target_edge = vec![usize::MAX; dataflow.phi_candidates.len()];
    for phi in &dataflow.phi_candidates {
        let owners = dispositions.get(phi.id.index()).ok_or_else(|| {
            StructureError::invalid(format!("{} has no incoming ownership plan", phi.id))
        })?;
        for (incoming, owner) in phi.incoming.iter().zip(owners) {
            if !incoming_requires_edge_copy(plan, phi.id, *owner) {
                continue;
            }
            let Some(edge) = incoming.edge else {
                continue;
            };
            let target = canonical_targets.for_incoming(plan, phi, incoming, *owner);
            let edge_actions = actions.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} incoming references missing edge {edge}",
                    phi.id
                ))
            })?;
            let seen_edge = target_edge.get_mut(target.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "edge {edge} canonical copy target {target} is outside the phi arena"
                ))
            })?;
            if *seen_edge == edge.index() {
                return Err(StructureError::invalid(format!(
                    "edge {edge} writes {target} more than once",
                )));
            }
            *seen_edge = edge.index();
            edge_actions.push(PhiEdgeCopy {
                phi_id: target,
                value: incoming.value,
            });
        }
    }
    Ok(actions)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CanonicalBreakTarget {
    owner: RegionId,
    target: PhiId,
}

/// numeric/generic-for 的 exit phi 到 canonical header phi 的稠密反向索引。
///
/// 构建只遍历一次最终 loop payload；之后每个 incoming 的 canonical target 查询均为
/// O(1)，不会再对同一 loop 的 header/exit values 做交叉扫描。
pub(in crate::structure) struct CanonicalEdgeCopyTargets {
    by_phi: Vec<Option<CanonicalBreakTarget>>,
}

impl CanonicalEdgeCopyTargets {
    pub(in crate::structure) fn build(
        plan: &StructurePlan,
        phi_count: usize,
    ) -> Result<Self, StructureError> {
        let mut by_phi = vec![None; phi_count];
        for (region, node) in plan.regions() {
            let RegionPlan::Loop { plan: loop_id, .. } = node else {
                continue;
            };
            let loop_ = plan.loop_(*loop_id).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop region {} references missing plan {}",
                    region.index(),
                    loop_id.index()
                ))
            })?;
            if !matches!(
                loop_.kind,
                LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
            ) {
                continue;
            }

            let max_reg = loop_
                .header_values
                .iter()
                .map(|value| value.reg.index())
                .chain(
                    loop_
                        .exit_values
                        .iter()
                        .flat_map(|exit| exit.values.iter().map(|value| value.reg.index())),
                )
                .max();
            let mut header_by_reg = Vec::new();
            if let Some(max_reg) = max_reg {
                let len = max_reg.checked_add(1).ok_or_else(|| {
                    StructureError::invalid("loop value register index overflows its dense arena")
                })?;
                header_by_reg.try_reserve_exact(len).map_err(|_| {
                    StructureError::invalid("loop value register arena is too large")
                })?;
                header_by_reg.resize(len, None);
            }
            for value in &loop_.header_values {
                if value.phi_id.index() >= phi_count {
                    return Err(StructureError::invalid(format!(
                        "loop region {} header references missing {}",
                        region.index(),
                        value.phi_id
                    )));
                }
                let slot = &mut header_by_reg[value.reg.index()];
                if slot
                    .replace(value.phi_id)
                    .is_some_and(|old| old != value.phi_id)
                {
                    return Err(StructureError::invalid(format!(
                        "loop region {} has multiple header phis for {}",
                        region.index(),
                        value.reg
                    )));
                }
            }
            for value in loop_.exit_values.iter().flat_map(|exit| exit.values.iter()) {
                let Some(target) = header_by_reg.get(value.reg.index()).copied().flatten() else {
                    continue;
                };
                let Some(slot) = by_phi.get_mut(value.phi_id.index()) else {
                    return Err(StructureError::invalid(format!(
                        "loop region {} exit references missing {}",
                        region.index(),
                        value.phi_id
                    )));
                };
                let mapping = CanonicalBreakTarget {
                    owner: region,
                    target,
                };
                if slot.replace(mapping).is_some_and(|old| old != mapping) {
                    return Err(StructureError::invalid(format!(
                        "{} has conflicting canonical loop targets",
                        value.phi_id
                    )));
                }
            }
        }
        Ok(Self { by_phi })
    }

    pub(in crate::structure) fn for_incoming(
        &self,
        plan: &StructurePlan,
        phi: &PhiCandidate,
        incoming: &crate::structure::PhiIncoming,
        disposition: PhiIncomingDisposition,
    ) -> PhiId {
        let (Some(edge), PhiIncomingDisposition::RegionResult(region)) =
            (incoming.edge, disposition)
        else {
            return phi.id;
        };
        if !matches!(
            plan.edge_plan(edge).map(|edge| edge.transfer),
            Some(EdgeTransfer::Break(owner)) if owner == region
        ) {
            return phi.id;
        }
        self.by_phi
            .get(phi.id.index())
            .copied()
            .flatten()
            .filter(|mapping| mapping.owner == region)
            .map_or(phi.id, |mapping| mapping.target)
    }
}

pub(in crate::structure) fn build_forwarded_action_heads(
    plan: &StructurePlan,
) -> Result<Vec<Option<EdgeRef>>, StructureError> {
    let mut edge_by_preorder = vec![None; plan.edge_plans.len()];
    for (index, preorder) in plan.forward_preorder.iter().copied().enumerate() {
        if preorder == usize::MAX {
            continue;
        }
        let slot = edge_by_preorder.get_mut(preorder).ok_or_else(|| {
            StructureError::invalid("forward route preorder exceeds its dense arena")
        })?;
        if slot.replace(EdgeRef(index)).is_some() {
            return Err(StructureError::invalid(
                "forward route preorder contains duplicate ranks",
            ));
        }
    }
    let mut next_action = vec![None; plan.edge_plans.len()];
    for edge in edge_by_preorder.into_iter().flatten() {
        next_action[edge.index()] = if plan
            .edge_plans
            .get(edge.index())
            .is_some_and(|edge| !edge.phi_copies.is_empty())
        {
            Some(edge)
        } else {
            plan.forward_next[edge.index()].and_then(|next| next_action[next.index()])
        };
    }
    Ok(next_action)
}

pub(in crate::structure) fn effective_edge_copies(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    edge: EdgeRef,
) -> Result<Vec<PhiEdgeCopy>, StructureError> {
    let edge_plan = plan
        .edge_plan(edge)
        .ok_or_else(|| StructureError::invalid(format!("missing edge plan for {edge}")))?;
    let Some(route) = edge_plan.forward_route else {
        return Ok(edge_plan.phi_copies.clone());
    };

    let mut composer = ForwardedActionComposer::new(dataflow);
    composer.begin_route(Some(route))?;
    for action in plan.forward_route_action_edges(route) {
        let copies = &plan.edge_plans[action.index()].phi_copies;
        composer.apply_forwarded_batch(cfg, dataflow, plan, copies, true)?;
    }
    let summary = composer.finish()?;
    composer.begin_route(None)?;
    composer.install_entry(&edge_plan.phi_copies)?;
    composer.apply_forwarded_batch(cfg, dataflow, plan, &summary, false)?;
    composer.finish()
}
