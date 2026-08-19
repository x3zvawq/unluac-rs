//! 提供冻结 StructurePlan 的查询 API 与 forward-route 迭代器；依赖 plan/navigation/terminator/value 子模块，不负责 evidence 候选；例如按 region、edge、phi 和 loop id 查询最终计划。

use super::*;

/// Structure 已完成冲突消解后的稠密 region/edge/value/cleanup 计划。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructurePlan {
    pub(in crate::structure) root: RegionId,
    pub(in crate::structure) regions: Vec<RegionPlan>,
    pub(in crate::structure) region_by_block: Vec<Option<RegionId>>,
    pub(in crate::structure) navigation: RegionNavigation,
    pub(in crate::structure) block_terminators: Vec<BlockTerminatorPlan>,
    pub(in crate::structure) block_emissions: Vec<BlockEmissionPlan>,
    pub(in crate::structure) edge_plans: Vec<EdgePlan>,
    pub(in crate::structure) forward_routes: Vec<ForwardRoutePlan>,
    pub(in crate::structure) forward_next: Vec<Option<EdgeRef>>,
    pub(in crate::structure) forward_preorder: Vec<usize>,
    pub(in crate::structure) forward_subtree_end: Vec<usize>,
    pub(in crate::structure) forward_depth: Vec<usize>,
    pub(in crate::structure) forward_owner_by_edge: Vec<Option<RegionId>>,
    pub(in crate::structure) forward_kind_by_edge: Vec<Option<ForwardRouteKind>>,
    pub(in crate::structure) forward_action_head: Vec<Option<EdgeRef>>,
    pub(in crate::structure) requirements: PlanRequirements,
    pub(in crate::structure) labels: Vec<LabelPlan>,
    pub(in crate::structure) label_by_block: Vec<Option<LabelPlanId>>,
    pub(in crate::structure) branches: Vec<BranchPlanData>,
    pub(in crate::structure) single_passes: Vec<SinglePassPlan>,
    pub(in crate::structure) single_pass_by_region: Vec<Option<SinglePassPlanId>>,
    pub(in crate::structure) loops: Vec<LoopPlanData>,
    pub(in crate::structure) loop_region_by_plan: Vec<RegionId>,
    pub(in crate::structure) loop_exit_tail_by_block: Vec<Option<LoopPlanId>>,
    pub(in crate::structure) loop_exit_tail_by_edge: Vec<Option<LoopPlanId>>,
    pub(in crate::structure) loop_exit_tail_by_cleanup_instr: Vec<Option<LoopPlanId>>,
    pub(in crate::structure) conditions: Vec<ConditionPlan>,
    pub(in crate::structure) condition_value_by_phi:
        Vec<Option<(ConditionPlanId, super::super::plan::ConditionNodeId)>>,
    pub(in crate::structure) absorbed_condition_by_block: Vec<Option<ConditionPlanId>>,
    pub(in crate::structure) value_decisions: Vec<ValueDecisionPlan>,
    pub(in crate::structure) value_decision_region_by_plan: Vec<RegionId>,
    pub(in crate::structure) value_decision_by_phi: Vec<Option<ValueDecisionPlanId>>,
    pub(in crate::structure) scopes: Vec<ScopePlan>,
    pub(in crate::structure) tbc_scopes: Vec<TbcScopePlan>,
    pub(in crate::structure) phis: Vec<super::super::plan::PhiPlan>,
    pub(in crate::structure) phis_by_block: Vec<Vec<PhiId>>,
    pub(in crate::structure) phis_by_region: Vec<Vec<PhiId>>,
    pub(in crate::structure) cleanup_dispositions: Vec<Option<CleanupDisposition>>,
}

impl StructurePlan {
    pub const fn root(&self) -> RegionId {
        self.root
    }

    pub fn region(&self, id: RegionId) -> Option<&RegionPlan> {
        self.regions.get(id.index())
    }

    pub fn regions(&self) -> impl ExactSizeIterator<Item = (RegionId, &RegionPlan)> {
        self.regions
            .iter()
            .enumerate()
            .map(|(index, region)| (RegionId(index), region))
    }

    pub fn region_for_block(&self, block: BlockRef) -> Option<RegionId> {
        self.region_by_block.get(block.index()).copied().flatten()
    }

    pub fn region_contains(&self, outer: RegionId, inner: RegionId) -> bool {
        self.navigation.contains(outer, inner)
    }

    pub fn edge_region_relation(&self, edge: EdgeRef) -> Option<EdgeRegionRelation> {
        self.navigation.edge_relation(edge)
    }

    pub fn region_boundary(&self, region: RegionId) -> Option<RegionBoundarySummary> {
        self.navigation.boundary(region)
    }

    pub(crate) fn region_postorder(&self) -> &[RegionId] {
        self.navigation.postorder()
    }

    pub fn block_terminator(&self, block: BlockRef) -> Option<&BlockTerminatorPlan> {
        self.block_terminators.get(block.index())
    }

    pub fn block_emission(&self, block: BlockRef) -> Option<BlockEmissionPlan> {
        self.block_emissions.get(block.index()).copied()
    }

    pub fn edge_plan(&self, edge: EdgeRef) -> Option<&EdgePlan> {
        self.edge_plans.get(edge.index())
    }

    pub fn forward_route(&self, id: ForwardRouteId) -> Option<&ForwardRoutePlan> {
        self.forward_routes.get(id.index())
    }

    pub fn forward_routes(
        &self,
    ) -> impl ExactSizeIterator<Item = (ForwardRouteId, &ForwardRoutePlan)> {
        self.forward_routes
            .iter()
            .enumerate()
            .map(|(index, route)| (ForwardRouteId(index), route))
    }

    pub fn forward_route_edges(
        &self,
        id: ForwardRouteId,
    ) -> impl ExactSizeIterator<Item = EdgeRef> + '_ {
        let route = self.forward_route(id);
        ForwardRouteEdges {
            next: &self.forward_next,
            current: route.map(|route| route.first),
            remaining: route.map_or(0, |route| route.len),
        }
    }

    pub(crate) fn forward_route_contains_edge(&self, id: ForwardRouteId, edge: EdgeRef) -> bool {
        let Some(route) = self.forward_route(id) else {
            return false;
        };
        self.forward_edge_is_ancestor(edge, route.first)
            && self.forward_edge_is_ancestor(route.last, edge)
    }

    pub(crate) fn forward_route_action_edges(
        &self,
        id: ForwardRouteId,
    ) -> impl Iterator<Item = EdgeRef> + '_ {
        let current = self.forward_route(id).and_then(|route| {
            self.forward_action_head
                .get(route.first.index())
                .copied()
                .flatten()
        });
        ForwardRouteActionEdges {
            plan: self,
            route: id,
            current,
        }
    }

    pub(crate) fn edge_action_is_forwarded_only(&self, edge: EdgeRef) -> bool {
        self.forward_kind_by_edge
            .get(edge.index())
            .copied()
            .flatten()
            == Some(ForwardRouteKind::ExclusiveBreak)
    }

    pub(crate) fn forward_path_contains_edge(
        &self,
        first: EdgeRef,
        last: EdgeRef,
        edge: EdgeRef,
    ) -> bool {
        self.forward_edge_is_ancestor(edge, first) && self.forward_edge_is_ancestor(last, edge)
    }

    fn forward_edge_is_ancestor(&self, ancestor: EdgeRef, edge: EdgeRef) -> bool {
        let Some(ancestor_start) = self.forward_preorder.get(ancestor.index()).copied() else {
            return false;
        };
        let Some(ancestor_end) = self.forward_subtree_end.get(ancestor.index()).copied() else {
            return false;
        };
        let Some(edge_start) = self.forward_preorder.get(edge.index()).copied() else {
            return false;
        };
        ancestor_start != usize::MAX
            && edge_start != usize::MAX
            && ancestor_start <= edge_start
            && edge_start < ancestor_end
    }

    pub fn requirements(&self) -> &PlanRequirements {
        &self.requirements
    }

    pub fn label(&self, id: LabelPlanId) -> Option<&LabelPlan> {
        self.labels.get(id.index())
    }

    pub fn label_for_block(&self, block: BlockRef) -> Option<LabelPlanId> {
        self.label_by_block.get(block.index()).copied().flatten()
    }

    pub fn labels(&self) -> impl ExactSizeIterator<Item = (LabelPlanId, &LabelPlan)> {
        self.labels
            .iter()
            .enumerate()
            .map(|(index, label)| (LabelPlanId(index), label))
    }

    pub fn branch(&self, id: BranchPlanId) -> Option<&BranchPlanData> {
        self.branches.get(id.index())
    }

    pub fn single_pass(&self, id: SinglePassPlanId) -> Option<&SinglePassPlan> {
        self.single_passes.get(id.index())
    }

    pub fn single_pass_for_region(
        &self,
        region: RegionId,
    ) -> Option<(SinglePassPlanId, &SinglePassPlan)> {
        let id = self
            .single_pass_by_region
            .get(region.index())
            .copied()
            .flatten()?;
        self.single_pass(id).map(|plan| (id, plan))
    }

    pub fn loop_(&self, id: LoopPlanId) -> Option<&LoopPlanData> {
        self.loops.get(id.index())
    }

    pub fn loop_protocol(&self, id: LoopPlanId) -> Option<&LoopVmProtocol> {
        self.loops.get(id.index())?.protocol.as_ref()
    }

    pub fn loop_value_actions(&self, id: LoopPlanId) -> Option<&LoopValueActions> {
        self.loops.get(id.index())?.value_actions.as_ref()
    }

    pub fn loop_region(&self, id: LoopPlanId) -> Option<RegionId> {
        self.loop_region_by_plan.get(id.index()).copied()
    }

    pub fn loop_exit_tail_for_block(
        &self,
        block: BlockRef,
    ) -> Option<(LoopPlanId, &LoopExitTailPlan)> {
        let id = self
            .loop_exit_tail_by_block
            .get(block.index())
            .copied()
            .flatten()?;
        self.loop_(id)?.exit_tail.as_ref().map(|tail| (id, tail))
    }

    pub fn loop_exit_tail_for_edge(
        &self,
        edge: EdgeRef,
    ) -> Option<(LoopPlanId, &LoopExitTailPlan)> {
        let id = self
            .loop_exit_tail_by_edge
            .get(edge.index())
            .copied()
            .flatten()?;
        self.loop_(id)?.exit_tail.as_ref().map(|tail| (id, tail))
    }

    pub fn loop_exit_tail_for_cleanup_instr(
        &self,
        instr: InstrRef,
    ) -> Option<(LoopPlanId, &LoopExitTailPlan)> {
        let id = self
            .loop_exit_tail_by_cleanup_instr
            .get(instr.index())
            .copied()
            .flatten()?;
        self.loop_(id)?.exit_tail.as_ref().map(|tail| (id, tail))
    }

    pub fn condition(&self, id: ConditionPlanId) -> Option<&ConditionPlan> {
        self.conditions.get(id.index())
    }

    pub fn condition_value_owner(
        &self,
        phi: PhiId,
    ) -> Option<(ConditionPlanId, super::super::plan::ConditionNodeId)> {
        self.condition_value_by_phi
            .get(phi.index())
            .copied()
            .flatten()
    }

    pub(crate) fn absorbed_condition_owner(&self, block: BlockRef) -> Option<ConditionPlanId> {
        self.absorbed_condition_by_block
            .get(block.index())
            .copied()
            .flatten()
    }

    pub fn value_decision(&self, id: ValueDecisionPlanId) -> Option<&ValueDecisionPlan> {
        self.value_decisions.get(id.index())
    }

    pub fn value_decision_region(&self, id: ValueDecisionPlanId) -> Option<RegionId> {
        self.value_decision_region_by_plan.get(id.index()).copied()
    }

    pub fn value_decision_owner(&self, phi: PhiId) -> Option<ValueDecisionPlanId> {
        self.value_decision_by_phi
            .get(phi.index())
            .copied()
            .flatten()
    }

    pub(crate) fn scope(&self, id: ScopePlanId) -> Option<&ScopePlan> {
        self.scopes.get(id.index())
    }

    pub fn tbc_scope(&self, id: TbcScopePlanId) -> Option<&TbcScopePlan> {
        self.tbc_scopes.get(id.index())
    }

    pub fn branches(&self) -> impl ExactSizeIterator<Item = (BranchPlanId, &BranchPlanData)> {
        self.branches
            .iter()
            .enumerate()
            .map(|(index, branch)| (BranchPlanId(index), branch))
    }

    pub fn single_passes(
        &self,
    ) -> impl ExactSizeIterator<Item = (SinglePassPlanId, &SinglePassPlan)> {
        self.single_passes
            .iter()
            .enumerate()
            .map(|(index, plan)| (SinglePassPlanId(index), plan))
    }

    pub fn loops(&self) -> impl ExactSizeIterator<Item = (LoopPlanId, &LoopPlanData)> {
        self.loops
            .iter()
            .enumerate()
            .map(|(index, loop_)| (LoopPlanId(index), loop_))
    }

    pub fn conditions(&self) -> impl ExactSizeIterator<Item = (ConditionPlanId, &ConditionPlan)> {
        self.conditions
            .iter()
            .enumerate()
            .map(|(index, condition)| (ConditionPlanId(index), condition))
    }

    pub fn value_decisions(
        &self,
    ) -> impl ExactSizeIterator<Item = (ValueDecisionPlanId, &ValueDecisionPlan)> {
        self.value_decisions
            .iter()
            .enumerate()
            .map(|(index, decision)| (ValueDecisionPlanId(index), decision))
    }

    pub fn phi_plan(&self, phi_id: PhiId) -> Option<&super::super::plan::PhiPlan> {
        self.phis.get(phi_id.index())
    }

    pub fn phis(&self) -> impl ExactSizeIterator<Item = &super::super::plan::PhiPlan> {
        self.phis.iter()
    }

    pub fn phis_in_block(&self, block: BlockRef) -> &[PhiId] {
        self.phis_by_block
            .get(block.index())
            .map_or(&[], Vec::as_slice)
    }

    pub fn phis_for_region(&self, region: RegionId) -> &[PhiId] {
        self.phis_by_region
            .get(region.index())
            .map_or(&[], Vec::as_slice)
    }

    pub fn cleanup_disposition(&self, instr: InstrRef) -> Option<CleanupDisposition> {
        self.cleanup_dispositions
            .get(instr.index())
            .copied()
            .flatten()
    }
}

struct ForwardRouteEdges<'a> {
    next: &'a [Option<EdgeRef>],
    current: Option<EdgeRef>,
    remaining: usize,
}

impl Iterator for ForwardRouteEdges<'_> {
    type Item = EdgeRef;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let edge = self.current?;
        self.remaining -= 1;
        self.current = self.next.get(edge.index()).copied().flatten();
        Some(edge)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for ForwardRouteEdges<'_> {}

struct ForwardRouteActionEdges<'a> {
    plan: &'a StructurePlan,
    route: ForwardRouteId,
    current: Option<EdgeRef>,
}

impl Iterator for ForwardRouteActionEdges<'_> {
    type Item = EdgeRef;

    fn next(&mut self) -> Option<Self::Item> {
        let edge = self
            .current
            .filter(|edge| self.plan.forward_route_contains_edge(self.route, *edge))?;
        self.current = self
            .plan
            .forward_next
            .get(edge.index())
            .copied()
            .flatten()
            .and_then(|next| {
                self.plan
                    .forward_action_head
                    .get(next.index())
                    .copied()
                    .flatten()
            });
        Some(edge)
    }
}
