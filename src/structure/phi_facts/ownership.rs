//! 传播并合并 region value owner、安装 unresolved requirement 并验证 phi arena；依赖区域树和 use 图，不负责生成 HIR；例如选择最具体的结构化 owner。

use super::*;

pub(super) fn require_phi(
    dataflow: &DataflowFacts,
    phi_id: PhiId,
) -> Result<&PhiCandidate, StructureError> {
    dataflow.phi_candidate(phi_id).ok_or_else(|| {
        StructureError::invalid(format!("selected value owner references missing {phi_id}"))
    })
}

pub(super) fn claim_idom_inputs(
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
) -> Result<(), StructureError> {
    for phi in &dataflow.phi_candidates {
        if dispositions[phi.id.index()].iter().all(Option::is_some) {
            continue;
        }
        let Some(idom) = graph_facts
            .dominator_tree
            .parent
            .get(phi.block.index())
            .copied()
            .flatten()
        else {
            continue;
        };
        let idom_value = dataflow.block_exit_value(idom, phi.reg);
        if !phi
            .incoming
            .iter()
            .all(|incoming| incoming.value == idom_value)
        {
            continue;
        }
        let region = plan.region_for_block(phi.block).ok_or_else(|| {
            StructureError::invalid(format!("{} target block has no region", phi.id))
        })?;
        for slot in &mut dispositions[phi.id.index()] {
            claim_owner(
                owner_index,
                slot,
                PhiIncomingDisposition::RegionInput(region),
            );
        }
    }
    Ok(())
}

pub(super) fn propagate_transitive_region_owners(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
) -> Result<(), StructureError> {
    pub(super) fn consume_ready_uses(
        owner_index: &RegionOwnerIndex,
        owner_uses: &[Vec<Option<PhiIncomingDisposition>>],
        phi_index: usize,
        next_use: &mut [usize],
        inherited_owners: &mut [Option<PhiIncomingDisposition>],
    ) {
        // owner merge 带有结构优先级，不能按依赖就绪时间重排；cursor 只消费 canonical
        // incoming 顺序中已经连续就绪的前缀，因此每条 use 最多合并一次。
        let uses = &owner_uses[phi_index];
        let cursor = &mut next_use[phi_index];
        while let Some(Some(owner)) = uses.get(*cursor) {
            let inherited = &mut inherited_owners[phi_index];
            *inherited = Some(match *inherited {
                None => *owner,
                Some(current) => merge_structured_owners(owner_index, current, *owner),
            });
            *cursor += 1;
        }
    }

    let phi_count = dataflow.phi_candidates.len();
    // ordinal 把 consumer incoming 映射回 upstream 的稳定 use 顺序。后续发布只填槽位，
    // unresolved 首次归零时 accumulator 必然已经消费完整序列。
    let mut owner_uses = vec![Vec::<Option<PhiIncomingDisposition>>::new(); phi_count];
    let mut use_ordinals = dispositions
        .iter()
        .map(|owners| vec![None; owners.len()])
        .collect::<Vec<_>>();
    let mut unresolved_uses = vec![0usize; phi_count];
    let mut next_use = vec![0usize; phi_count];
    let mut inherited_owners = vec![None; phi_count];
    for phi in &dataflow.phi_candidates {
        let owners = dispositions.get(phi.id.index()).ok_or_else(|| {
            StructureError::invalid(format!("{} has no incoming ownership row", phi.id))
        })?;
        if owners.len() != phi.incoming.len() {
            return Err(StructureError::invalid(format!(
                "{} has {} owner slots for {} incomings",
                phi.id,
                owners.len(),
                phi.incoming.len()
            )));
        }
        for (incoming_index, incoming) in phi.incoming.iter().enumerate() {
            let SsaValue::Phi(upstream) = incoming.value else {
                continue;
            };
            let Some(uses) = owner_uses.get_mut(upstream.index()) else {
                return Err(StructureError::invalid(format!(
                    "{} incoming references missing {upstream}",
                    phi.id
                )));
            };
            let owner = owners[incoming_index].filter(|owner| owner.region().is_some());
            if owner.is_none() {
                let unresolved = &mut unresolved_uses[upstream.index()];
                *unresolved = unresolved.checked_add(1).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "{upstream} unresolved phi-use count overflows usize"
                    ))
                })?;
            }
            let ordinal = uses.len();
            uses.push(owner);
            use_ordinals[phi.id.index()][incoming_index] = Some(ordinal);
        }
    }

    for phi_index in 0..phi_count {
        consume_ready_uses(
            owner_index,
            &owner_uses,
            phi_index,
            &mut next_use,
            &mut inherited_owners,
        );
    }

    let mut pending = owner_uses
        .iter()
        .zip(&unresolved_uses)
        .enumerate()
        .filter_map(|(index, (uses, unresolved))| {
            (!uses.is_empty() && *unresolved == 0).then_some(PhiId(index))
        })
        .collect::<VecDeque<_>>();
    while let Some(phi_id) = pending.pop_front() {
        if dataflow.phi_use_count(phi_id) != 0
            || dispositions[phi_id.index()].iter().any(Option::is_some)
        {
            continue;
        }
        let owner = inherited_owners[phi_id.index()].ok_or_else(|| {
            StructureError::invalid(format!(
                "{phi_id} has resolved phi uses without an inherited owner"
            ))
        })?;

        let phi = require_phi(dataflow, phi_id)?;
        let mut changed = false;
        for slot in &mut dispositions[phi_id.index()] {
            changed |= claim_owner(owner_index, slot, owner);
        }
        if !changed {
            continue;
        }
        for (incoming_index, incoming) in phi.incoming.iter().enumerate() {
            let SsaValue::Phi(upstream) = incoming.value else {
                continue;
            };
            let Some(owner) = dispositions[phi_id.index()][incoming_index]
                .filter(|owner| owner.region().is_some())
            else {
                continue;
            };
            let ordinal = use_ordinals[phi_id.index()][incoming_index].ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} incoming has no registered {upstream} phi-use",
                    phi.id
                ))
            })?;
            let owner_slot = owner_uses
                .get_mut(upstream.index())
                .and_then(|uses| uses.get_mut(ordinal))
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "{} incoming references missing {upstream} phi-use #{ordinal}",
                        phi.id
                    ))
                })?;
            if owner_slot.replace(owner).is_some() {
                return Err(StructureError::invalid(format!(
                    "{upstream} phi-use #{ordinal} owner was published more than once"
                )));
            }
            let unresolved = unresolved_uses.get_mut(upstream.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{} incoming references missing {upstream}",
                    phi.id
                ))
            })?;
            *unresolved = unresolved.checked_sub(1).ok_or_else(|| {
                StructureError::invalid(format!(
                    "{upstream} phi-use owner was published more than once"
                ))
            })?;
            consume_ready_uses(
                owner_index,
                &owner_uses,
                upstream.index(),
                &mut next_use,
                &mut inherited_owners,
            );
            if *unresolved == 0 {
                if next_use[upstream.index()] != owner_uses[upstream.index()].len() {
                    return Err(StructureError::invalid(format!(
                        "{upstream} resolved count disagrees with its owner-use accumulator"
                    )));
                }
                pending.push_back(upstream);
            }
        }
    }
    Ok(())
}

/// Region containment 的稠密区间索引。
///
/// phi owner 合并会被每个 incoming 反复调用；预先把 containment tree 编成 Euler
/// interval 后，祖先判断保持 O(1)，不会再按 region 深度逐层追溯 parent。
pub(super) struct RegionOwnerIndex {
    enter: Vec<usize>,
    exit: Vec<usize>,
    inside_branch: Vec<bool>,
    value_decision: Vec<bool>,
}

impl RegionOwnerIndex {
    pub(super) fn new(plan: &StructurePlan) -> Result<Self, StructureError> {
        let region_count = plan.regions().len();
        let root = plan.root();
        if region_count == 0 || root.index() >= region_count {
            return Err(StructureError::invalid(
                "region owner index requires a valid plan root",
            ));
        }

        let mut children = vec![Vec::new(); region_count];
        for (region, payload) in plan.regions() {
            match payload.parent() {
                None if region == root => {}
                None => {
                    return Err(StructureError::invalid(format!(
                        "non-root region {} has no containment parent",
                        region.index()
                    )));
                }
                Some(_) if region == root => {
                    return Err(StructureError::invalid(
                        "plan root unexpectedly has a containment parent",
                    ));
                }
                Some(parent) => {
                    let Some(parent_children) = children.get_mut(parent.index()) else {
                        return Err(StructureError::invalid(format!(
                            "region {} references missing parent {}",
                            region.index(),
                            parent.index()
                        )));
                    };
                    parent_children.push(region);
                }
            }
        }

        let mut enter = vec![usize::MAX; region_count];
        let mut exit = vec![usize::MAX; region_count];
        let mut inside_branch = vec![false; region_count];
        let mut value_decision = vec![false; region_count];
        let mut clock = 0usize;
        let mut pending = vec![(root, false, false)];
        while let Some((region, leaving, inherited_branch)) = pending.pop() {
            if leaving {
                exit[region.index()] = clock;
                continue;
            }
            if enter[region.index()] != usize::MAX {
                return Err(StructureError::invalid(
                    "region containment contains a cycle or duplicate child",
                ));
            }
            enter[region.index()] = clock;
            clock += 1;
            let branch =
                inherited_branch || matches!(plan.region(region), Some(RegionPlan::Branch { .. }));
            inside_branch[region.index()] = branch;
            value_decision[region.index()] =
                matches!(plan.region(region), Some(RegionPlan::ValueDecision { .. }));
            pending.push((region, true, branch));
            for child in children[region.index()].iter().rev() {
                pending.push((*child, false, branch));
            }
        }
        if let Some(region) = enter.iter().position(|entry| *entry == usize::MAX) {
            return Err(StructureError::invalid(format!(
                "region {region} is disconnected from the plan root"
            )));
        }

        Ok(Self {
            enter,
            exit,
            inside_branch,
            value_decision,
        })
    }

    pub(super) fn contains(&self, ancestor: RegionId, region: RegionId) -> bool {
        self.enter
            .get(ancestor.index())
            .zip(self.exit.get(ancestor.index()))
            .zip(self.enter.get(region.index()))
            .is_some_and(|((enter, exit), region)| *enter <= *region && *region < *exit)
    }

    pub(super) fn inside_branch(&self, region: RegionId) -> bool {
        self.inside_branch
            .get(region.index())
            .copied()
            .unwrap_or(false)
    }

    pub(super) fn is_value_decision(&self, region: RegionId) -> bool {
        self.value_decision
            .get(region.index())
            .copied()
            .unwrap_or(false)
    }

    pub(super) fn more_specific(&self, left: RegionId, right: RegionId) -> Option<RegionId> {
        if self.contains(left, right) {
            Some(right)
        } else if self.contains(right, left) {
            Some(left)
        } else {
            None
        }
    }
}

pub(super) fn claim_owner(
    owner_index: &RegionOwnerIndex,
    slot: &mut Option<PhiIncomingDisposition>,
    owner: PhiIncomingDisposition,
) -> bool {
    let merged = match *slot {
        None => owner,
        Some(current) => merge_structured_owners(owner_index, current, owner),
    };
    let changed = *slot != Some(merged);
    *slot = Some(merged);
    changed
}

pub(super) fn merge_structured_owners(
    owner_index: &RegionOwnerIndex,
    left: PhiIncomingDisposition,
    right: PhiIncomingDisposition,
) -> PhiIncomingDisposition {
    use PhiIncomingDisposition::{
        Dead, DiagnosticUnresolved, EdgeCopy, LoopCarried, RegionInput, RegionResult,
    };

    if left == right {
        return left;
    }
    if matches!(left, Dead | EdgeCopy) {
        return left;
    }
    if matches!(right, Dead | EdgeCopy) {
        return right;
    }
    if matches!(left, DiagnosticUnresolved) || matches!(right, DiagnosticUnresolved) {
        return DiagnosticUnresolved;
    }
    match (left, right) {
        (LoopCarried(left_region), LoopCarried(right_region)) => {
            if left_region == right_region {
                left
            } else {
                // condition/result join 同时喂给内外两层回边时，join 本身属于更内层
                // region 的结果；外层只消费这份结果，不能把它误报成两个 carried owner。
                owner_index
                    .more_specific(left_region, right_region)
                    .map_or(DiagnosticUnresolved, RegionResult)
            }
        }
        (LoopCarried(_), _) => left,
        (_, LoopCarried(_)) => right,
        (RegionInput(input), RegionResult(result)) | (RegionResult(result), RegionInput(input)) => {
            if owner_index.inside_branch(result) || owner_index.is_value_decision(result) {
                RegionResult(result)
            } else {
                RegionInput(input)
            }
        }
        (RegionInput(left_region), RegionInput(right_region)) => owner_index
            .more_specific(left_region, right_region)
            .map_or(DiagnosticUnresolved, RegionInput),
        (RegionResult(left_region), RegionResult(right_region)) => owner_index
            .more_specific(left_region, right_region)
            .map_or(DiagnosticUnresolved, RegionResult),
        _ => DiagnosticUnresolved,
    }
}

pub(super) fn install_unresolved_requirements(
    plan: &mut StructurePlan,
    dataflow: &DataflowFacts,
    unresolved: BTreeSet<PhiId>,
) -> Result<(), StructureError> {
    for phi_id in unresolved {
        let phi = require_phi(dataflow, phi_id)?;
        let unresolved = plan
            .requirements
            .unresolved_by_block
            .get_mut(phi.block.index())
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "unresolved requirement for {phi_id} references missing block {}",
                    phi.block
                ))
            })?;
        *unresolved = true;
        plan.requirements
            .entries
            .push(PlanRequirement::UnresolvedValue {
                phi_id,
                block: phi.block,
                reg: phi.reg,
            });
    }
    Ok(())
}

pub(super) fn validate_phi_ownership(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.phis.len() != dataflow.phi_candidates.len()
        || plan.phis_by_block.len() != cfg.blocks.len()
        || plan.phis_by_region.len() != plan.regions().len()
        || plan.edge_plans.len() != cfg.edges.len()
    {
        return Err(StructureError::invalid(
            "value ownership arena does not match CFG/dataflow",
        ));
    }
    let mut expected_copies = vec![Vec::new(); cfg.edges.len()];
    let mut expected_by_block = vec![Vec::new(); cfg.blocks.len()];
    let mut expected_by_region = vec![Vec::new(); plan.regions().len()];
    let mut region_seen_at = vec![usize::MAX; plan.regions().len()];
    let mut unresolved_requirements = vec![false; dataflow.phi_candidates.len()];
    let canonical_targets = CanonicalEdgeCopyTargets::build(plan, dataflow.phi_candidates.len())?;
    for requirement in &plan.requirements.entries {
        let PlanRequirement::UnresolvedValue { phi_id, .. } = requirement else {
            continue;
        };
        let Some(slot) = unresolved_requirements.get_mut(phi_id.index()) else {
            return Err(StructureError::invalid(format!(
                "unresolved requirement references missing {phi_id}"
            )));
        };
        *slot = true;
    }
    for phi in &dataflow.phi_candidates {
        let phi_plan = plan
            .phi_plan(phi.id)
            .ok_or_else(|| StructureError::invalid(format!("missing value plan for {}", phi.id)))?;
        if phi_plan.phi != phi.id
            || phi_plan.block != phi.block
            || phi_plan.reg != phi.reg
            || phi_plan.incomings.len() != phi.incoming.len()
        {
            return Err(StructureError::invalid(format!(
                "{} value plan does not match canonical SSA",
                phi.id
            )));
        }
        let Some(block_phis) = expected_by_block.get_mut(phi.block.index()) else {
            return Err(StructureError::invalid(format!(
                "{} target block is outside the CFG arena",
                phi.id
            )));
        };
        block_phis.push(phi.id);
        for (incoming_index, (incoming, incoming_plan)) in
            phi.incoming.iter().zip(&phi_plan.incomings).enumerate()
        {
            if incoming_plan.edge != incoming.edge || incoming_plan.value != incoming.value {
                return Err(StructureError::invalid(format!(
                    "{} incoming #{incoming_index} source does not match canonical SSA",
                    phi.id
                )));
            }
            match incoming_plan.disposition {
                PhiIncomingDisposition::RegionInput(region)
                | PhiIncomingDisposition::RegionResult(region) => {
                    if plan.region(region).is_none() {
                        return Err(StructureError::invalid(format!(
                            "{} incoming #{incoming_index} refers to missing region {}",
                            phi.id,
                            region.index()
                        )));
                    }
                    if region_seen_at[region.index()] != phi.id.index() {
                        region_seen_at[region.index()] = phi.id.index();
                        expected_by_region[region.index()].push(phi.id);
                    }
                }
                PhiIncomingDisposition::LoopCarried(region) => {
                    if !matches!(plan.region(region), Some(RegionPlan::Loop { .. })) {
                        return Err(StructureError::invalid(format!(
                            "{} incoming #{incoming_index} has non-loop carried owner {}",
                            phi.id,
                            region.index()
                        )));
                    }
                    if region_seen_at[region.index()] != phi.id.index() {
                        region_seen_at[region.index()] = phi.id.index();
                        expected_by_region[region.index()].push(phi.id);
                    }
                }
                PhiIncomingDisposition::EdgeCopy => {
                    if incoming.edge.is_none() {
                        return Err(StructureError::invalid(format!(
                            "{} synthetic incoming #{incoming_index} is edge-owned",
                            phi.id
                        )));
                    }
                }
                PhiIncomingDisposition::Dead => {
                    let unreachable_edge = incoming.edge.is_some_and(|edge| {
                        matches!(
                            plan.edge_plan(edge).map(|edge| edge.transfer),
                            Some(EdgeTransfer::Unreachable)
                        )
                    });
                    if !dataflow.phi_is_truly_dead(phi.id) && !unreachable_edge {
                        return Err(StructureError::invalid(format!(
                            "live reachable {} incoming #{incoming_index} is dead",
                            phi.id
                        )));
                    }
                }
                PhiIncomingDisposition::DiagnosticUnresolved => {
                    if !unresolved_requirements[phi.id.index()] {
                        return Err(StructureError::invalid(format!(
                            "{} incoming #{incoming_index} has no unresolved requirement",
                            phi.id
                        )));
                    }
                }
            }
            if incoming_requires_edge_copy(plan, phi.id, incoming_plan.disposition)
                && let Some(edge) = incoming.edge
            {
                let Some(copies) = expected_copies.get_mut(edge.index()) else {
                    return Err(StructureError::invalid(format!(
                        "{} incoming #{incoming_index} references missing edge {edge}",
                        phi.id
                    )));
                };
                let target =
                    canonical_targets.for_incoming(plan, phi, incoming, incoming_plan.disposition);
                copies.push(PhiEdgeCopy {
                    phi_id: target,
                    value: incoming.value,
                });
            }
        }
    }
    if plan.phis_by_block != expected_by_block || plan.phis_by_region != expected_by_region {
        return Err(StructureError::invalid(
            "value ownership reverse indexes are inconsistent",
        ));
    }
    if build_forwarded_action_heads(plan)? != plan.forward_action_head {
        return Err(StructureError::invalid(
            "forwarded phi action index is inconsistent",
        ));
    }
    for (edge_index, expected) in expected_copies.iter().enumerate() {
        let actual = &plan.edge_plans[edge_index].phi_copies;
        if actual != expected {
            return Err(StructureError::invalid(format!(
                "edge #{edge_index} phi copies do not match incoming ownership: expected={expected:?} actual={actual:?} transfer={:?}",
                plan.edge_plans[edge_index].transfer,
            )));
        }
    }
    Ok(())
}
