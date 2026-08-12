//! 这个文件集中声明 Structure 的内部 evidence 与最终 `StructureFacts` 容器。
//!
//! branch/loop/short-circuit 类型只在 Structure 内参与冲突消解；对下游公开的事实已经
//! 收窄为冻结的 `StructurePlan + DebugBindingFacts + children`，HIR 不再读取 raw evidence
//! 做第二次取舍。

use std::collections::BTreeSet;

use crate::structure::{BlockRef, DefId, EdgeRef, PhiId, SsaValue};
use crate::transformer::{InstrRef, Reg, RegRange};

use super::cfg::GraphFacts;

use super::plan::{
    BlockEmissionPlan, BlockTerminatorPlan, BranchPlanData, BranchPlanId, CleanupDisposition,
    ConditionPlan, ConditionPlanId, EdgePlan, EdgeRegionRelation, ForwardRouteId, ForwardRouteKind,
    ForwardRoutePlan, LabelPlan, LabelPlanId, LoopExitTailPlan, LoopPlanData, LoopPlanId,
    LoopValueActions, LoopVmProtocol, PlanRequirements, RegionBoundarySummary, RegionId,
    RegionNavigation, RegionPlan, ScopePlanId, SinglePassPlan, SinglePassPlanId, TbcScopePlan,
    TbcScopePlanId, ValueDecisionPlan, ValueDecisionPlanId,
};

/// 一个 proto 已冻结的结构计划，以及它的子 proto 结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureFacts {
    pub plan: StructurePlan,
    pub debug_bindings: DebugBindingFacts,
    pub children: Vec<StructureFacts>,
}

/// debug local 在其源码生命周期入口对应的 canonical SSA 身份。
///
/// `scope` 是 Transformer 归一化 debug local arena 的稳定索引。这里不携带名称，避免
/// Structure 越权处理字符串和命名合法性；HIR 只需把这个索引与归一化 local 事实连接，
/// 就能在 table/closure 等跨多条指令的初始化之后仍找回正确 binding。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DebugBindingFact {
    pub scope: usize,
    pub reg: Reg,
    pub start_pc: u32,
    pub end_pc: u32,
    pub value: SsaValue,
}

/// 多个源码 scope 竞争同一 canonical SSA 时保留的拒绝证据。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugBindingConflict {
    pub value: SsaValue,
    pub scopes: Vec<usize>,
}

/// 一个 proto 已冻结的 debug binding 映射及被拒绝的冲突证据。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DebugBindingFacts {
    pub accepted: Vec<DebugBindingFact>,
    pub conflicts: Vec<DebugBindingConflict>,
}

/// Structure 已完成冲突消解后的稠密 region/edge/value/cleanup 计划。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructurePlan {
    pub(super) root: RegionId,
    pub(super) regions: Vec<RegionPlan>,
    pub(super) region_by_block: Vec<Option<RegionId>>,
    pub(super) navigation: RegionNavigation,
    pub(super) block_terminators: Vec<BlockTerminatorPlan>,
    pub(super) block_emissions: Vec<BlockEmissionPlan>,
    pub(super) edge_plans: Vec<EdgePlan>,
    pub(super) forward_routes: Vec<ForwardRoutePlan>,
    pub(super) forward_next: Vec<Option<EdgeRef>>,
    pub(super) forward_preorder: Vec<usize>,
    pub(super) forward_subtree_end: Vec<usize>,
    pub(super) forward_depth: Vec<usize>,
    pub(super) forward_owner_by_edge: Vec<Option<RegionId>>,
    pub(super) forward_kind_by_edge: Vec<Option<ForwardRouteKind>>,
    pub(super) forward_action_head: Vec<Option<EdgeRef>>,
    pub(super) requirements: PlanRequirements,
    pub(super) labels: Vec<LabelPlan>,
    pub(super) label_by_block: Vec<Option<LabelPlanId>>,
    pub(super) branches: Vec<BranchPlanData>,
    pub(super) single_passes: Vec<SinglePassPlan>,
    pub(super) single_pass_by_region: Vec<Option<SinglePassPlanId>>,
    pub(super) loops: Vec<LoopPlanData>,
    pub(super) loop_region_by_plan: Vec<RegionId>,
    pub(super) loop_exit_tail_by_block: Vec<Option<LoopPlanId>>,
    pub(super) loop_exit_tail_by_edge: Vec<Option<LoopPlanId>>,
    pub(super) loop_exit_tail_by_cleanup_instr: Vec<Option<LoopPlanId>>,
    pub(super) conditions: Vec<ConditionPlan>,
    pub(super) condition_value_by_phi: Vec<Option<(ConditionPlanId, super::plan::ConditionNodeId)>>,
    pub(super) absorbed_condition_by_block: Vec<Option<ConditionPlanId>>,
    pub(super) value_decisions: Vec<ValueDecisionPlan>,
    pub(super) value_decision_region_by_plan: Vec<RegionId>,
    pub(super) value_decision_by_phi: Vec<Option<ValueDecisionPlanId>>,
    pub(super) scopes: Vec<ScopePlan>,
    pub(super) tbc_scopes: Vec<TbcScopePlan>,
    pub(super) phis: Vec<super::plan::PhiPlan>,
    pub(super) phis_by_block: Vec<Vec<PhiId>>,
    pub(super) phis_by_region: Vec<Vec<PhiId>>,
    pub(super) cleanup_dispositions: Vec<Option<CleanupDisposition>>,
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
    ) -> Option<(ConditionPlanId, super::plan::ConditionNodeId)> {
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

    pub fn phi_plan(&self, phi_id: PhiId) -> Option<&super::plan::PhiPlan> {
        self.phis.get(phi_id.index())
    }

    pub fn phis(&self) -> impl ExactSizeIterator<Item = &super::plan::PhiPlan> {
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

impl StructureFacts {
    pub const fn plan(&self) -> &StructurePlan {
        &self.plan
    }

    pub const fn debug_bindings(&self) -> &DebugBindingFacts {
        &self.debug_bindings
    }
}

/// 显式 CFG edge 离开 predecessor 时需要执行的一条 phi copy。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhiEdgeCopy {
    pub phi_id: PhiId,
    pub value: SsaValue,
}

/// Structure 内部 evidence 可附带的既有 island 布局提示。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnstructuredRegionLayout {
    pub blocks: BTreeSet<BlockRef>,
    pub continuation: BlockRef,
}

/// 一个分支结构候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCandidate {
    pub header: BlockRef,
    pub then_entry: BlockRef,
    pub else_entry: Option<BlockRef>,
    pub merge: Option<BlockRef>,
    pub kind: BranchKind,
    pub invert_hint: bool,
}

/// 分支形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BranchKind {
    IfThen,
    IfElse,
    Guard,
}

/// 一个普通 branch 区域的共享边界事实。
///
/// 普通非回环 branch 的结构区域精确等于 `header` 的支配子树减去若干支配子树。
/// 必须冻结特殊改写的精确边界时，也只保存 dominator preorder 的连续区间，不再为
/// 每个嵌套 branch 复制完整 block 集。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRegionFact {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub kind: BranchKind,
    pub single_pass_fence: Option<SinglePassFenceFact>,
    pub(super) domain: BranchRegionDomain,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BranchRegionDomain {
    pub spans: Vec<BranchRegionSpan>,
    pub included_blocks: Vec<BlockRef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BranchRegionSpan {
    pub root: BlockRef,
    pub excluded_subtrees: Vec<BlockRef>,
}

impl BranchRegionDomain {
    pub(super) fn from_span(
        root: BlockRef,
        excluded_subtrees: impl IntoIterator<Item = BlockRef>,
    ) -> Self {
        Self {
            spans: vec![BranchRegionSpan {
                root,
                excluded_subtrees: excluded_subtrees.into_iter().collect(),
            }],
            included_blocks: Vec::new(),
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.spans.is_empty() && self.included_blocks.is_empty()
    }

    pub(super) fn contains(&self, graph_facts: &GraphFacts, block: BlockRef) -> bool {
        self.included_blocks.binary_search(&block).is_ok()
            || self.spans.iter().any(|span| {
                graph_facts.dominates(span.root, block)
                    && span
                        .excluded_subtrees
                        .iter()
                        .all(|excluded| !graph_facts.dominates(*excluded, block))
            })
    }
}

/// 编译器消去 `repeat ... until true` 回边后仍保留的单次 fence 控制事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinglePassFenceFact {
    pub exit: BlockRef,
    pub escape_edges: BTreeSet<EdgeRef>,
}

impl BranchRegionFact {
    pub(super) fn new(
        graph_facts: &GraphFacts,
        header: BlockRef,
        merge: BlockRef,
        kind: BranchKind,
        single_pass_fence: Option<SinglePassFenceFact>,
    ) -> Self {
        let excluded_subtrees = if let Some(fence) = &single_pass_fence {
            vec![merge, fence.exit]
        } else if graph_facts.dominates(merge, header) {
            Vec::new()
        } else {
            vec![merge]
        };
        let domain = BranchRegionDomain {
            spans: vec![BranchRegionSpan {
                root: header,
                excluded_subtrees,
            }],
            included_blocks: Vec::new(),
        };
        Self {
            header,
            merge,
            kind,
            single_pass_fence,
            domain,
        }
    }

    pub(super) fn replace_domain(&mut self, mut domain: BranchRegionDomain) {
        domain.included_blocks.sort_unstable();
        domain.included_blocks.dedup();
        self.domain = domain;
    }

    pub(super) fn preorder_intervals(
        &self,
        graph_facts: &GraphFacts,
    ) -> Result<Vec<std::ops::Range<usize>>, BlockRef> {
        let position = |block: BlockRef| {
            graph_facts
                .dominator_tree
                .preorder_index
                .get(block.index())
                .copied()
                .flatten()
                .ok_or(block)
        };
        let subtree_end = |block: BlockRef| {
            graph_facts
                .dominator_tree
                .subtree_end
                .get(block.index())
                .copied()
                .flatten()
                .ok_or(block)
        };

        let mut intervals = Vec::<std::ops::Range<usize>>::new();
        for span in &self.domain.spans {
            let start = position(span.root)?;
            let end = subtree_end(span.root)?;
            let mut holes = span
                .excluded_subtrees
                .iter()
                .copied()
                .map(|block| Ok(position(block)?..subtree_end(block)?))
                .collect::<Result<Vec<_>, BlockRef>>()?;
            holes.sort_unstable_by_key(|hole| (hole.start, hole.end));

            let mut cursor = start;
            for hole in holes {
                let hole_start = hole.start.max(start).min(end);
                let hole_end = hole.end.max(start).min(end);
                if cursor < hole_start {
                    intervals.push(cursor..hole_start);
                }
                cursor = cursor.max(hole_end);
            }
            if cursor < end {
                intervals.push(cursor..end);
            }
        }
        intervals.extend(
            self.domain
                .included_blocks
                .iter()
                .copied()
                .map(|block| position(block).map(|position| position..position + 1))
                .collect::<Result<Vec<_>, _>>()?,
        );
        intervals.sort_unstable_by_key(|interval| (interval.start, interval.end));
        let mut merged = Vec::<std::ops::Range<usize>>::with_capacity(intervals.len());
        for interval in intervals {
            if let Some(last) = merged.last_mut()
                && interval.start <= last.end
            {
                last.end = last.end.max(interval.end);
            } else if !interval.is_empty() {
                merged.push(interval);
            }
        }
        Ok(merged)
    }

    pub fn structured_blocks<'a>(
        &'a self,
        graph_facts: &'a GraphFacts,
    ) -> Result<impl Iterator<Item = BlockRef> + 'a, BlockRef> {
        let intervals = self.preorder_intervals(graph_facts)?;
        for interval in &intervals {
            if graph_facts
                .dominator_tree
                .order
                .get(interval.clone())
                .is_none()
            {
                return Err(self.header);
            }
        }
        Ok(intervals.into_iter().flat_map(|interval| {
            graph_facts
                .dominator_tree
                .order
                .get(interval)
                .into_iter()
                .flatten()
                .copied()
        }))
    }
}

/// 一个不可规约区域的共享边界事实。
///
/// 它只表达 SCC 的入口和覆盖 block，不替后层决定最终 `goto/label` 语法。
/// `goto / regions` 都消费这份事实，不应再各自重复做 SCC 入口扫描。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct IrreducibleRegion {
    pub entry: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry_edges: Vec<EdgeRef>,
}

/// 一个普通 branch 在 merge 点上产生的值合流候选。
///
/// 它和 `ShortCircuitCandidate::ValueMerge` 的区别是：这里不假设整片区域更像 `and/or`，
/// 只表达“这个结构化 branch 的两臂分别给 merge 提供了哪些值版本”。这样 HIR 可以
/// 统一决定要不要继续当成同一 lvalue、还是保守物化成 `Decision` / 临时值。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeCandidate {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub values: Vec<BranchValueMergeValue>,
}

/// 一个 merge 值在两臂上的来源分布。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeValue {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub then_arm: BranchValueMergeArm,
    pub else_arm: BranchValueMergeArm,
}

/// branch merge 某一臂已经收敛好的来源事实。
///
/// `preds` 保留结构边归属，`values` 记录这一臂在 merge 前实际可见的 canonical SSA
/// 身份。`entry_values` 是 branch header 带入的值，`update_values` 是各 arm 在本轮
/// 产生或传递更新的版本；同一个 Phi 可以同时属于两类。HIR 只消费这份分类，不再
/// 把 Phi 压回叶子 def 后重判来源。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeArm {
    pub preds: BTreeSet<BlockRef>,
    pub values: BTreeSet<SsaValue>,
    pub entry_values: BTreeSet<SsaValue>,
    pub update_values: BTreeSet<SsaValue>,
}

/// 一个循环候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCandidate {
    pub header: BlockRef,
    pub preheader: Option<BlockRef>,
    pub blocks: BTreeSet<BlockRef>,
    /// 源码 loop body 在词法上覆盖的 block。
    ///
    /// natural loop blocks 不包含提前退出 tail，也可能漏掉 repeat 分支进入的 nested
    /// loop。Structure 在这里统一保存源码 body 边界；HIR bindings 与结构降低只消费
    /// 这份事实，不回头用 CFG 扩张作用域。
    pub body_scope_blocks: BTreeSet<BlockRef>,
    /// 已被循环语法或规范化出口吸收、无需作为源码 body 单独降低的 block。
    pub control_blocks: BTreeSet<BlockRef>,
    /// VM latch 指向的重复终止块与 preheader 正常出口语义等价；源码只发射后者。
    pub normalized_exit_aliases: Vec<LoopExitAlias>,
    pub backedges: Vec<EdgeRef>,
    pub exits: BTreeSet<BlockRef>,
    pub continue_target: Option<BlockRef>,
    /// 已由当前循环认领的 branch -> continue target/pad 边。
    pub continue_edges: BTreeSet<EdgeRef>,
    /// 仅在短路候选参与 loop 形态精化时记录其条件入口。
    pub condition_header: Option<BlockRef>,
    pub kind_hint: LoopKindHint,
    pub source_bindings: Option<LoopSourceBindings>,
    pub header_value_merges: Vec<LoopValueMerge>,
    pub exit_value_merges: Vec<LoopExitValueMergeCandidate>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopExitAlias {
    pub block: BlockRef,
    pub continuation: BlockRef,
}

/// 循环头已经暴露给 HIR 的源码绑定证据。
///
/// 这里只记录“源码层确实会出现的绑定寄存器”，避免 HIR 再回头扫描 low-IR/CFG
/// 去猜 numeric-for / generic-for 的绑定槽位。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopSourceBindings {
    Numeric(Reg),
    Generic(RegRange),
}

/// loop merge 某一臂的稳定 incoming 事实。
///
/// 和 branch merge 不同，loop state 恢复需要保留“每个 predecessor 分别给了哪些 defs”，
/// 这样 HIR 才能直接消费 preheader/exit 的来源，不必再回头拆 `phi.incoming`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueIncoming {
    pub pred: Option<BlockRef>,
    pub value: SsaValue,
}

/// 一个 loop value merge 某一臂的 incoming 集合。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopValueArm {
    pub incomings: Vec<LoopValueIncoming>,
}

impl LoopValueArm {
    pub fn is_empty(&self) -> bool {
        self.incomings.is_empty()
    }

    pub fn contains_pred(&self, pred: BlockRef) -> bool {
        self.incomings
            .iter()
            .any(|incoming| incoming.pred == Some(pred))
    }

    pub fn values(&self) -> impl Iterator<Item = SsaValue> + '_ {
        self.incomings.iter().map(|incoming| incoming.value)
    }
}

/// 一个 loop header/exit 上的值合流候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueMerge {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub inside_arm: LoopValueArm,
    pub outside_arm: LoopValueArm,
}

/// 某个 loop exit block 上的值合流候选集合。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExitValueMergeCandidate {
    pub exit: BlockRef,
    pub values: Vec<LoopValueMerge>,
}

/// 循环形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum LoopKindHint {
    WhileLike,
    WhileTrueLike,
    RepeatLike,
    NumericForLike,
    GenericForLike,
    Unknown,
}

/// 一个短路表达式候选。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitCandidate {
    pub header: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry: ShortCircuitNodeRef,
    pub nodes: Vec<ShortCircuitNode>,
    pub exit: ShortCircuitExit,
    pub result_reg: Option<Reg>,
    pub result_phi_id: Option<PhiId>,
    pub entry_value: Option<SsaValue>,
    pub value_incomings: Vec<ShortCircuitValueIncoming>,
    pub reducible: bool,
}

impl ShortCircuitCandidate {
    pub(crate) fn branch_exit_leaf_preds(&self, want_truthy: bool) -> BTreeSet<BlockRef> {
        self.nodes
            .iter()
            .filter_map(|node| {
                let matches_exit = if want_truthy {
                    matches!(&node.truthy, ShortCircuitTarget::TruthyExit)
                        || matches!(&node.falsy, ShortCircuitTarget::TruthyExit)
                } else {
                    matches!(&node.truthy, ShortCircuitTarget::FalsyExit)
                        || matches!(&node.falsy, ShortCircuitTarget::FalsyExit)
                };
                matches_exit.then_some(node.header)
            })
            .collect()
    }
}

/// 值型 short-circuit merge 每个叶子最终送进 merge 的 canonical SSA 值。
///
/// 这份事实和 `result_phi_id` 一起构成了“叶子 -> merge 值身份”的前层表达，避免 HIR
/// 再顺着 `PhiCandidate.incoming` 去拆 value leaf。`latest_local_def` 进一步把
/// “这个 leaf block 自己最后一次写 result_reg 的 def”前移出来，避免 HIR 再回头扫描
/// block 指令去找叶子值来源。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitValueIncoming {
    pub pred: BlockRef,
    pub value: SsaValue,
    pub latest_local_def: Option<DefId>,
}

/// 短路 DAG 中的稳定节点引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ShortCircuitNodeRef(pub usize);

impl ShortCircuitNodeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个短路决策节点。
///
/// 这里显式用 `truthy/falsy` 语义连边，而不是 raw `then/else`。原因是结构层的职责
/// 是把 CFG 重新翻译成“按 Lua 求值语义理解”的候选，方便 HIR 直接基于真值流恢复
/// `and/or`，而不用再次反查 `negated` 和 branch 边方向。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitNode {
    pub id: ShortCircuitNodeRef,
    pub header: BlockRef,
    pub truthy: ShortCircuitTarget,
    pub falsy: ShortCircuitTarget,
}

/// 短路 DAG 上的目标。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitTarget {
    /// 继续进入下一个短路决策节点。
    Node(ShortCircuitNodeRef),
    /// 值型短路的一条叶子。`BlockRef` 指向把值送进 merge 的前驱 block。
    Value(BlockRef),
    /// 条件型短路的“整体为真”出口。
    TruthyExit,
    /// 条件型短路的“整体为假”出口。
    FalsyExit,
}

/// 短路控制流最终如何离开候选区域。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitExit {
    /// 这条短路 DAG 最终在某个 block 合流，并通常伴随 phi/result 语义。
    ValueMerge(BlockRef),
    /// 这条短路 DAG 最终直接分流到“整体为真/整体为假”的两个出口。
    BranchExit { truthy: BlockRef, falsy: BlockRef },
}

/// 结构候选尚未吸收的一条控制边证据。
///
/// 这只是 Structure 内部冻结最终 edge transfer 的输入，不是对下游公开的
/// `goto` 语法需求。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(super) struct ResidualTransferEvidence {
    pub(super) edge: EdgeRef,
    pub(super) reason: GotoReason,
}

/// 最终计划为什么需要把这条边表达为显式 `goto`。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum GotoReason {
    IrreducibleFlow,
    MultiEntryRegion,
    UnstructuredBreakLike,
    UnstructuredContinueLike,
    CrossLoopContinueLike,
}

/// 某片 block 集合的区域事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionFact {
    pub blocks: BTreeSet<BlockRef>,
    pub entry: BlockRef,
    pub exits: BTreeSet<BlockRef>,
}

/// 已冻结的词法 cleanup scope。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopePlan {
    pub entry: BlockRef,
    pub exit: Option<BlockRef>,
    pub close_points: Vec<InstrRef>,
}
