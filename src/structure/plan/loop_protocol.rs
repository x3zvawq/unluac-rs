//! 冻结 loop 的 VM 协议与值动作批次。
//!
//! `loops.rs` 只负责识别候选形态；这里把最终 loop 会如何进入 body、如何回边、以及
//! numeric/generic-for 的 phi copy 应在什么阶段执行一次性写死。HIR 只能消费这些
//! 稳定协议，不能再扫整张 CFG 回推 loop 形状或值写回时序。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{
    BlockRef, BlockTerminatorKind, Cfg, DataflowFacts, EdgeRef, GotoReason, GraphFacts,
    LoopSourceBindings, PhiId, SsaValue, StructurePlan,
};
use crate::transformer::{
    GenericForCallInstr, GenericForLoopInstr, GenericForPrepInstr, InstrRef, LowInstr,
    LoweredProto, Reg, RegRange,
};

use super::{
    ConditionPlanId, EdgeTransfer, LoopConditionPrefixPlacement, LoopKindHint, LoopPlanData,
    RegionId, RegionPlan, StructureError,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopConditionProtocol {
    pub condition: ConditionPlanId,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    pub body_on_truthy: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopRepeatForm {
    Native,
    TailBranchRepeat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopRepeatProtocol {
    pub condition: LoopConditionProtocol,
    pub prefix_placement: LoopConditionPrefixPlacement,
    pub form: LoopRepeatForm,
    /// condition 成功后仍需在原生 repeat 外执行的祖先 transfer/value actions。
    pub exit_after_loop: bool,
    pub value_plan: LoopRepeatValuePlan,
}

/// 原生 repeat 退出时延迟提交的结果。每个结果使用独立、不可观察的 staging temp；
/// condition 路径和所有 early break 都先写 stage，离开 loop 后才提交 final phi。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopRepeatStagedResult {
    pub target: PhiId,
    pub normal_value: SsaValue,
}

/// repeat terminal edge 的唯一值协议。Structure 证明 staged result 覆盖全部退出路径后，
/// HIR 才能选择原生 `repeat ... until`，不得把 final captured local 提前暴露在 loop 内。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopRepeatValuePlan {
    /// 可在原生 repeat 的 `until` 条件求值前执行的 loop-carried copies。
    pub backedge_copies: Vec<crate::structure::PhiEdgeCopy>,
    pub exit_copies: Vec<crate::structure::PhiEdgeCopy>,
    /// 祖先 VM-for 已由源码循环语法隐式推进的控制槽，不得在内层 repeat 退出前读取。
    /// 这些 copy 仍由外层 loop-carried owner 消费，不是无 owner 的丢弃动作。
    pub outer_loop_owned_exit_copies: Vec<crate::structure::PhiEdgeCopy>,
    pub staged_results: Vec<LoopRepeatStagedResult>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumericForProtocol {
    pub init_instr: InstrRef,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    /// source body 是否存在一条不经显式 break/continue/goto 的正常 latch 路径。
    pub body_completes_normally: bool,
    pub index: Reg,
    pub limit: Reg,
    pub step: Reg,
    pub binding: Reg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenericForProtocol {
    pub prep_instr: Option<InstrRef>,
    pub call_instr: InstrRef,
    pub loop_instr: InstrRef,
    pub body_edge: EdgeRef,
    pub exit_edge: EdgeRef,
    /// source body 是否存在一条不经显式 break/continue/goto 的正常 latch 路径。
    pub body_completes_normally: bool,
    pub iterator: RegRange,
    pub bindings: RegRange,
    pub immediate_break: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopVmProtocol {
    While(LoopConditionProtocol),
    Repeat(LoopRepeatProtocol),
    WhileTrue,
    NumericFor(NumericForProtocol),
    GenericFor(GenericForProtocol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdgeCopyOrigin {
    pub edge: EdgeRef,
    pub target: PhiId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopValueSource {
    Ssa(SsaValue),
    Binding(Reg),
    Carried(PhiId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueWrite {
    pub target: PhiId,
    pub source: LoopValueSource,
    pub origins: Vec<EdgeCopyOrigin>,
}

/// 提前离开本轮源码 body 的 edge 对 IterationEpilogue 结果槽的冻结写回。
/// 即使当前值等于旧槽也显式写入 canonical incoming，避免再引入一套 carried 等价证明。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopIterationDisposition {
    pub loop_region: RegionId,
    pub target: PhiId,
    pub incoming: SsaValue,
    pub source: LoopValueSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopValuePhase {
    BeforeLoop,
    BodyPrologue,
    IterationEpilogue,
    LatchEpilogue,
    AfterLoop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueActionBatch {
    pub phase: LoopValuePhase,
    pub writes: Vec<LoopValueWrite>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopValueActions {
    pub batches: Vec<LoopValueActionBatch>,
    pub elided: Vec<EdgeCopyOrigin>,
}

#[derive(Default)]
struct FrozenExitActions {
    before_loop: Vec<LoopValueWrite>,
    iteration_epilogue: Vec<LoopValueWrite>,
    after_loop: Vec<LoopValueWrite>,
    elided: Vec<EdgeCopyOrigin>,
}

#[derive(Clone, Copy, Default)]
struct PhiUseExtent {
    first_region: usize,
    last_region: usize,
    has_region: bool,
    has_unowned_use: bool,
}

impl PhiUseExtent {
    fn include_region(&mut self, position: usize) {
        if self.has_region {
            self.first_region = self.first_region.min(position);
            self.last_region = self.last_region.max(position);
        } else {
            self.first_region = position;
            self.last_region = position;
            self.has_region = true;
        }
    }

    fn merge(&mut self, other: Self) {
        if other.has_region {
            self.include_region(other.first_region);
            self.include_region(other.last_region);
        }
        self.has_unowned_use |= other.has_unowned_use;
    }
}

/// loop value 分类只依赖冻结 SSA/containment，因此为整个 proto 一次性建立稠密摘要。
///
/// phi graph 先收缩 SCC，再沿 condensation DAG 传播 instruction-use 的 region
/// preorder 范围。一个 control region 的 subtree 也是连续 preorder 区间，所以
/// `phi_observed_outside` 无需再为每个 copy 递归遍历整张 use graph。
struct LoopValueAnalysis {
    vm_for_control: Vec<bool>,
    use_extents: Vec<PhiUseExtent>,
    absorbed_owner_by_edge: Vec<Option<super::LoopPlanId>>,
}

#[derive(Clone, Copy)]
struct LoopValueContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    plan: &'a StructurePlan,
    analysis: &'a LoopValueAnalysis,
    owner: RegionId,
    control: RegionId,
    payload: &'a LoopPlanData,
}

impl LoopValueAnalysis {
    fn build(
        proto: &LoweredProto,
        cfg: &Cfg,
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
            for edge in absorbed_value_edges(cfg, plan, region, payload)? {
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

    fn value_is_vm_for_control(
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

    fn phi_observed_outside(&self, plan: &StructurePlan, control: RegionId, phi: PhiId) -> bool {
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

fn def_is_vm_for_control(
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

pub(super) fn finalize(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let analysis = LoopValueAnalysis::build(proto, cfg, dataflow, plan)?;
    let body_completion = freeze_vm_for_body_completion(cfg, plan)?;
    let frozen = plan
        .loops
        .iter()
        .enumerate()
        .map(|(index, payload)| {
            let region = plan
                .loop_region_by_plan
                .get(index)
                .copied()
                .ok_or_else(|| StructureError::invalid("loop region reverse index is stale"))?;
            let protocol = freeze_protocol(&LoopProtocolContext {
                proto,
                cfg,
                dataflow,
                plan,
                analysis: &analysis,
                region,
                payload,
                body_completes_normally: body_completion[index],
            })?;
            let value_actions =
                freeze_value_actions(proto, cfg, dataflow, plan, &analysis, region, payload)?;
            Ok((protocol, value_actions))
        })
        .collect::<Result<Vec<_>, StructureError>>()?;
    for (payload, (protocol, actions)) in plan.loops.iter_mut().zip(frozen) {
        payload.protocol = Some(protocol);
        payload.value_actions = Some(actions);
    }
    freeze_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, &analysis)?;
    Ok(())
}

/// 证明最终 loop protocol/value-action arena 与被语法吸收的 CFG edge 完全一致。
///
/// 每个 origin 只遍历一次；随后按 edge 用 phi-id epoch 对照 canonical copy，因此不会
/// 为 `(edge, phi)` 建稀疏全对索引，也不会重新执行 SSA 来源分析。
pub(super) fn validate(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let analysis = LoopValueAnalysis::build(proto, cfg, dataflow, plan)?;
    let body_completion = freeze_vm_for_body_completion(cfg, plan)?;
    if plan
        .loops
        .iter()
        .any(|payload| payload.protocol.is_none() || payload.value_actions.is_none())
    {
        return Err(StructureError::invalid(
            "loop payload is missing its frozen protocol/value actions",
        ));
    }

    let absorbed_owner = analysis.absorbed_owner_by_edge.clone();
    let mut origins_by_edge = vec![Vec::<PhiId>::new(); cfg.edges.len()];
    let mut partial_elided_by_edge = vec![Vec::<PhiId>::new(); cfg.edges.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        let loop_id = super::LoopPlanId(index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop protocol has no owning region"))?;
        let protocol = plan
            .loop_protocol(loop_id)
            .ok_or_else(|| StructureError::invalid("loop protocol arena is sparse"))?;
        let expected = freeze_protocol(&LoopProtocolContext {
            proto,
            cfg,
            dataflow,
            plan,
            analysis: &analysis,
            region,
            payload,
            body_completes_normally: body_completion[index],
        })?;
        if *protocol != expected {
            return Err(StructureError::invalid(format!(
                "loop protocol #{} changed after freezing",
                loop_id.index()
            )));
        }
        if let LoopVmProtocol::Repeat(repeat) = protocol {
            validate_repeat_outer_loop_owned_exit_copies(
                proto, cfg, dataflow, plan, &analysis, region, repeat,
            )?;
        }

        let actions = plan
            .loop_value_actions(loop_id)
            .ok_or_else(|| StructureError::invalid("loop value-action arena is sparse"))?;
        let expected_actions =
            freeze_value_actions(proto, cfg, dataflow, plan, &analysis, region, payload)?;
        if *actions != expected_actions {
            return Err(StructureError::invalid(format!(
                "loop value actions #{} changed after freezing",
                loop_id.index()
            )));
        }
        let is_vm_for = matches!(
            protocol,
            LoopVmProtocol::NumericFor(_) | LoopVmProtocol::GenericFor(_)
        );
        if !is_vm_for && (!actions.batches.is_empty() || !actions.elided.is_empty()) {
            return Err(StructureError::invalid(format!(
                "non-for loop #{} owns VM value actions",
                loop_id.index()
            )));
        }

        for batch in &actions.batches {
            for write in &batch.writes {
                if write.origins.is_empty()
                    || dataflow.phi_candidate(write.target).is_none()
                    || !loop_value_source_is_valid(dataflow, payload, write.source)
                {
                    return Err(StructureError::invalid(format!(
                        "loop value action #{} has an invalid target, source, or empty origin set",
                        loop_id.index()
                    )));
                }
                for origin in &write.origins {
                    if origin.target != write.target {
                        return Err(StructureError::invalid(format!(
                            "loop value action #{} origin changes phi target",
                            loop_id.index()
                        )));
                    }
                    record_origin(cfg, &absorbed_owner, &mut origins_by_edge, loop_id, *origin)?;
                }
            }
        }
        for origin in &actions.elided {
            match absorbed_owner.get(origin.edge.index()).copied().flatten() {
                Some(owner) if owner == loop_id => {
                    record_origin(cfg, &absorbed_owner, &mut origins_by_edge, loop_id, *origin)?;
                }
                None if cfg.edges.get(origin.edge.index()).is_some()
                    && payload
                        .control_edges
                        .backedges
                        .binary_search(&origin.edge)
                        .is_ok()
                    && plan.edge_plan(origin.edge).is_some_and(|edge| {
                        edge.owner == region || plan.region_contains(region, edge.owner)
                    }) =>
                {
                    partial_elided_by_edge[origin.edge.index()].push(origin.target);
                }
                _ => {
                    return Err(StructureError::invalid(format!(
                        "loop value action #{} cites an invalid edge origin",
                        loop_id.index()
                    )));
                }
            }
        }
    }

    let mut seen_phi = vec![0usize; dataflow.phi_candidates.len()];
    let mut epoch = 0usize;
    for (edge_index, owner) in absorbed_owner.into_iter().enumerate() {
        let Some(loop_id) = owner else {
            if !origins_by_edge[edge_index].is_empty() {
                return Err(StructureError::invalid(
                    "loop value action escaped its absorbed edge set",
                ));
            }
            continue;
        };
        epoch = epoch.checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop value-action validation epoch overflow")
        })?;
        let edge = EdgeRef(edge_index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop value action lost its owner"))?;
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("absorbed loop edge has no final plan"))?;
        // 一条 VM-for syntax edge 仍只有一个最终 transfer owner，但它也可能在
        // containment 上结束一个内层 for 并自然落入祖先结构。例如 Luau 会把空
        // generic-for 的 exit 直接折叠成外层 for 的 LoopBack。只有无需额外语句的
        // 祖先 transfer 能被语法吸收；Break/Continue/Goto 必须由 HIR 显式发射。
        let ancestor_implicit_transfer = edge_plan.owner != region
            && plan.region_contains(edge_plan.owner, region)
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::LoopBack(_)
            );
        if edge_plan.owner != region && !ancestor_implicit_transfer {
            return Err(StructureError::invalid(format!(
                "absorbed loop edge {edge} {} -> {} ({:?}) is owned by region #{} instead of loop region #{}",
                cfg.edges[edge.index()].from,
                cfg.edges[edge.index()].to,
                edge_plan.transfer,
                edge_plan.owner.index(),
                region.index(),
            )));
        }
        for target in &origins_by_edge[edge_index] {
            let slot = seen_phi.get_mut(target.index()).ok_or_else(|| {
                StructureError::invalid("loop value action references a missing phi")
            })?;
            if *slot == epoch {
                return Err(StructureError::invalid(format!(
                    "edge {edge} phi {target} has multiple loop value dispositions"
                )));
            }
            *slot = epoch;
        }
        let matching_copies = edge_plan
            .phi_copies
            .iter()
            .filter(|copy| {
                seen_phi
                    .get(copy.phi_id.index())
                    .is_some_and(|seen| *seen == epoch)
            })
            .count();
        let missing_origin = matching_copies != origins_by_edge[edge_index].len();
        let undispositioned_owned_copy = edge_plan.owner == region
            && edge_plan.phi_copies.len() != origins_by_edge[edge_index].len();
        if missing_origin || undispositioned_owned_copy {
            return Err(StructureError::invalid(format!(
                "absorbed loop edge {edge} does not disposition every canonical phi copy exactly once"
            )));
        }
    }
    for (edge_index, targets) in partial_elided_by_edge.into_iter().enumerate() {
        if targets.is_empty() {
            continue;
        }
        epoch = epoch.checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop value-action validation epoch overflow")
        })?;
        for target in &targets {
            let slot = seen_phi.get_mut(target.index()).ok_or_else(|| {
                StructureError::invalid("loop value action references a missing phi")
            })?;
            if std::mem::replace(slot, epoch) == epoch {
                return Err(StructureError::invalid(
                    "one backedge phi copy has multiple loop value dispositions",
                ));
            }
        }
        let edge = EdgeRef(edge_index);
        let matching = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("elided loop backedge has no final plan"))?
            .phi_copies
            .iter()
            .filter(|copy| {
                seen_phi
                    .get(copy.phi_id.index())
                    .is_some_and(|seen| *seen == epoch)
            })
            .count();
        if matching != targets.len() {
            return Err(StructureError::invalid(format!(
                "loop backedge {edge} does not contain every elided phi copy exactly once"
            )));
        }
    }
    validate_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, &analysis)?;
    Ok(())
}

fn freeze_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<(), StructureError> {
    let frozen =
        build_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, analysis)?;
    for (edge, dispositions) in plan.edge_plans.iter_mut().zip(frozen) {
        if !edge.iteration.is_empty() {
            return Err(StructureError::invalid(
                "iteration edge dispositions were finalized more than once",
            ));
        }
        edge.iteration = dispositions;
    }
    Ok(())
}

fn validate_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<(), StructureError> {
    let expected =
        build_iteration_edge_dispositions(proto, cfg, graph_facts, dataflow, plan, analysis)?;
    let mut seen_target_at = vec![usize::MAX; dataflow.phi_candidates.len()];
    for (edge_index, (edge, expected)) in plan.edge_plans.iter().zip(expected).enumerate() {
        if edge.iteration != expected {
            return Err(StructureError::invalid(format!(
                "edge {} iteration dispositions changed after freezing",
                edge.edge
            )));
        }
        for disposition in &edge.iteration {
            let slot = seen_target_at
                .get_mut(disposition.target.index())
                .ok_or_else(|| {
                    StructureError::invalid("iteration edge action targets a missing phi")
                })?;
            if std::mem::replace(slot, edge_index) == edge_index {
                return Err(StructureError::invalid(format!(
                    "edge {} writes one iteration result more than once",
                    edge.edge
                )));
            }
        }
    }
    Ok(())
}

fn build_iteration_edge_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
) -> Result<Vec<Vec<LoopIterationDisposition>>, StructureError> {
    let mut canonical_moves = crate::structure::phi_facts::CanonicalMoveIndex::new(proto, dataflow);
    let mut by_edge = vec![Vec::new(); cfg.edges.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        let loop_id = super::LoopPlanId(index);
        let region = plan
            .loop_region(loop_id)
            .ok_or_else(|| StructureError::invalid("loop iteration action has no owner"))?;
        let control = loop_control_region(plan, region)?;
        let context = LoopValueContext {
            proto,
            cfg,
            dataflow,
            plan,
            analysis,
            owner: region,
            control,
            payload,
        };
        let actions = plan.loop_value_actions(loop_id).ok_or_else(|| {
            StructureError::invalid("loop iteration action has no finalized value protocol")
        })?;
        let writes = actions
            .batches
            .iter()
            .filter(|batch| batch.phase == LoopValuePhase::IterationEpilogue)
            .flat_map(|batch| batch.writes.iter())
            .collect::<Vec<_>>();
        if writes.is_empty() {
            continue;
        }
        for edge in payload
            .control_edges
            .continues
            .iter()
            .copied()
            .filter(|edge| {
                plan.edge_plan(*edge)
                    .is_some_and(|edge_plan| iteration_edge_bypasses_tail(edge_plan, region))
            })
        {
            let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
                StructureError::invalid("loop iteration action references a missing edge plan")
            })?;
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop iteration action references a missing CFG edge")
            })?;
            let value_block = edge_plan
                .forward_route
                .and_then(|route| plan.forward_route(route))
                .and_then(|route| cfg.edges.get(route.last.index()))
                .map_or(cfg_edge.from, |edge| edge.from);
            for write in &writes {
                let reg = dataflow
                    .phi_candidate(write.target)
                    .ok_or_else(|| {
                        StructureError::invalid("loop iteration action targets a missing phi")
                    })?
                    .reg;
                let incoming =
                    canonical_moves.resolve(dataflow.block_exit_value(value_block, reg))?;
                if !value_is_available_at_edge_action(
                    cfg,
                    graph_facts,
                    dataflow,
                    edge_plan,
                    incoming,
                ) {
                    return Err(StructureError::invalid(format!(
                        "loop iteration result {} is unavailable before edge {edge}",
                        write.target
                    )));
                }
                let source =
                    classify_value_source(&context, incoming, write.target)?.ok_or_else(|| {
                        StructureError::invalid(
                            "loop iteration result resolves to an implicit VM-for control value",
                        )
                    })?;
                by_edge[edge.index()].push(LoopIterationDisposition {
                    loop_region: region,
                    target: write.target,
                    incoming,
                    source,
                });
            }
        }
    }
    let mut seen_target_at = vec![usize::MAX; dataflow.phi_candidates.len()];
    for (edge_index, dispositions) in by_edge.iter().enumerate() {
        for disposition in dispositions {
            let slot = seen_target_at
                .get_mut(disposition.target.index())
                .ok_or_else(|| {
                    StructureError::invalid("iteration edge action targets a missing phi")
                })?;
            if std::mem::replace(slot, edge_index) == edge_index {
                return Err(StructureError::invalid(
                    "one edge has conflicting loop iteration result owners",
                ));
            }
        }
    }
    Ok(by_edge)
}

fn iteration_edge_bypasses_tail(edge: &super::EdgePlan, owner: RegionId) -> bool {
    matches!(edge.transfer, EdgeTransfer::Continue(region) if region == owner)
        || matches!(
            edge.transfer,
            EdgeTransfer::Goto(
                _,
                GotoReason::UnstructuredContinueLike | GotoReason::CrossLoopContinueLike
            )
        )
}

fn value_is_available_at_edge_action(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    edge_plan: &super::EdgePlan,
    value: SsaValue,
) -> bool {
    let Some(edge) = cfg.edges.get(edge_plan.edge.index()) else {
        return false;
    };
    match value {
        SsaValue::Entry(_) => true,
        SsaValue::Phi(phi) => dataflow
            .phi_candidate(phi)
            .is_some_and(|phi| graph_facts.dominates(phi.block, edge.from)),
        SsaValue::Def(def) => dataflow.defs.get(def.index()).is_some_and(|definition| {
            if definition.block != edge.from {
                return graph_facts.dominates(definition.block, edge.from);
            }
            let action_limit = edge_plan
                .actions_before_trailing_cleanup()
                .map_or(cfg.blocks[edge.from.index()].instrs.end(), |range| {
                    range.start.index()
                });
            definition.instr.index() < action_limit
        }),
    }
}

fn absorbed_value_edges(
    cfg: &Cfg,
    plan: &StructurePlan,
    owner: RegionId,
    payload: &LoopPlanData,
) -> Result<Vec<EdgeRef>, StructureError> {
    let control = loop_control_region(plan, owner)?;
    let mut edges = payload
        .control_edges
        .preheader_body
        .into_iter()
        .chain(payload.control_edges.preheader_exit)
        .chain(payload.control_edges.body.iter().copied())
        .chain(payload.control_edges.exit.iter().copied())
        .chain(
            payload
                .control_edges
                .backedges
                .iter()
                .copied()
                .filter(|edge| {
                    cfg.edges
                        .get(edge.index())
                        .is_some_and(|cfg_edge| block_is_in_region(plan, control, cfg_edge.from))
                }),
        )
        .collect::<Vec<_>>();
    edges.sort_by_key(|edge| edge.index());
    edges.dedup();
    Ok(edges)
}

fn record_origin(
    cfg: &Cfg,
    absorbed_owner: &[Option<super::LoopPlanId>],
    origins_by_edge: &mut [Vec<PhiId>],
    loop_id: super::LoopPlanId,
    origin: EdgeCopyOrigin,
) -> Result<(), StructureError> {
    if cfg.edges.get(origin.edge.index()).is_none()
        || absorbed_owner.get(origin.edge.index()).copied().flatten() != Some(loop_id)
    {
        return Err(StructureError::invalid(format!(
            "loop value action #{} cites a non-absorbed edge origin",
            loop_id.index()
        )));
    }
    origins_by_edge[origin.edge.index()].push(origin.target);
    Ok(())
}

fn loop_value_source_is_valid(
    dataflow: &DataflowFacts,
    payload: &LoopPlanData,
    source: LoopValueSource,
) -> bool {
    match source {
        LoopValueSource::Ssa(SsaValue::Entry(_)) => true,
        LoopValueSource::Ssa(SsaValue::Def(def)) => dataflow.defs.get(def.index()).is_some(),
        LoopValueSource::Ssa(SsaValue::Phi(phi)) => dataflow.phi_candidate(phi).is_some(),
        LoopValueSource::Binding(reg) => match payload.source_bindings {
            Some(LoopSourceBindings::Numeric(binding)) => reg == binding,
            Some(LoopSourceBindings::Generic(bindings)) => {
                reg.index() >= bindings.start.index()
                    && reg.index() < bindings.start.index() + bindings.len
            }
            None => false,
        },
        LoopValueSource::Carried(phi) => payload
            .header_values
            .iter()
            .any(|value| value.phi_id == phi),
    }
}

fn loop_control_region(plan: &StructurePlan, owner: RegionId) -> Result<RegionId, StructureError> {
    match plan.region(owner) {
        Some(RegionPlan::Loop { control, .. }) => Ok(*control),
        _ => Err(StructureError::invalid(format!(
            "loop payload owner #{} is not a loop region",
            owner.index()
        ))),
    }
}

fn block_is_in_region(plan: &StructurePlan, region: RegionId, block: BlockRef) -> bool {
    plan.region_for_block(block)
        .is_some_and(|owner| plan.region_contains(region, owner))
}

#[derive(Clone, Copy)]
struct LoopProtocolContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    plan: &'a StructurePlan,
    analysis: &'a LoopValueAnalysis,
    region: RegionId,
    payload: &'a LoopPlanData,
    body_completes_normally: bool,
}

fn freeze_protocol(context: &LoopProtocolContext<'_>) -> Result<LoopVmProtocol, StructureError> {
    let LoopProtocolContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        region,
        payload,
        body_completes_normally,
    } = *context;
    Ok(match payload.kind {
        LoopKindHint::WhileLike => LoopVmProtocol::While(freeze_condition_protocol(plan, payload)?),
        LoopKindHint::RepeatLike => {
            let condition = freeze_condition_protocol(plan, payload)?;
            let prefix_placement = payload.condition_prefix_placement.ok_or_else(|| {
                StructureError::invalid("repeat loop is missing its condition prefix placement")
            })?;
            let context = LoopValueContext {
                proto,
                cfg,
                dataflow,
                plan,
                analysis,
                owner: region,
                control: loop_control_region(plan, region)?,
                payload,
            };
            let value_plan =
                freeze_repeat_value_plan(&context, condition.body_edge, condition.exit_edge)?;
            let plain_backedge = edge_emits_no_stmt(plan, condition.body_edge)
                || repeat_backedge_copies_are_movable(
                    plan,
                    region,
                    condition.body_edge,
                    &value_plan,
                )?;
            let plain_break =
                repeat_exit_is_plain_break(plan, region, condition.exit_edge, &value_plan)?;
            let staged_break =
                repeat_exit_is_staged_break(plan, region, condition.exit_edge, &value_plan)?;
            let exit_after_loop =
                repeat_exit_can_follow_native(plan, region, payload, condition.exit_edge)?;
            let has_direct_continue = payload.control_edges.continues.iter().copied().any(|edge| {
                plan.edge_plan(edge).is_some_and(|edge| {
                    matches!(
                        edge.transfer,
                        EdgeTransfer::Continue(_) | EdgeTransfer::Goto(..)
                    )
                })
            });
            let form = if plain_backedge && (plain_break || staged_break || exit_after_loop) {
                LoopRepeatForm::Native
            } else {
                LoopRepeatForm::TailBranchRepeat
            };
            if (has_direct_continue || exit_after_loop) && form != LoopRepeatForm::Native {
                return Err(StructureError::invalid(format!(
                    "repeat requiring native exit has no complete protocol: backedge={} plain={}, exit={} plain={} staged={} post={}, backedge-plan={:?}, exit-plan={:?}, values={:?}",
                    condition.body_edge,
                    plain_backedge,
                    condition.exit_edge,
                    plain_break,
                    staged_break,
                    exit_after_loop,
                    plan.edge_plan(condition.body_edge),
                    plan.edge_plan(condition.exit_edge),
                    value_plan,
                )));
            }
            LoopVmProtocol::Repeat(LoopRepeatProtocol {
                condition,
                prefix_placement,
                form,
                exit_after_loop,
                value_plan,
            })
        }
        LoopKindHint::NumericForLike => LoopVmProtocol::NumericFor(freeze_numeric_for_protocol(
            proto,
            plan,
            region,
            payload,
            body_completes_normally,
        )?),
        LoopKindHint::GenericForLike => LoopVmProtocol::GenericFor(freeze_generic_for_protocol(
            proto,
            cfg,
            plan,
            region,
            payload,
            body_completes_normally,
        )?),
        LoopKindHint::WhileTrueLike => LoopVmProtocol::WhileTrue,
        LoopKindHint::Unknown => {
            if payload.condition.is_some()
                && (!payload.control_edges.body.is_empty()
                    || !payload.control_edges.exit.is_empty())
            {
                LoopVmProtocol::While(freeze_condition_protocol(plan, payload)?)
            } else {
                LoopVmProtocol::WhileTrue
            }
        }
    })
}

fn freeze_condition_protocol(
    plan: &StructurePlan,
    payload: &LoopPlanData,
) -> Result<LoopConditionProtocol, StructureError> {
    let condition_id = payload
        .condition
        .ok_or_else(|| StructureError::invalid("loop is missing its frozen condition plan"))?;
    let condition = plan
        .condition(condition_id)
        .ok_or_else(|| StructureError::invalid("loop condition references a missing payload"))?;
    let truthy_body = edge_is_loop_body(payload, condition.truthy);
    let falsy_body = edge_is_loop_body(payload, condition.falsy);
    let truthy_exit = edge_is_loop_exit(payload, condition.truthy);
    let falsy_exit = edge_is_loop_exit(payload, condition.falsy);
    if truthy_body == falsy_body || truthy_exit == falsy_exit || !(truthy_exit || falsy_exit) {
        return Err(StructureError::invalid(format!(
            "loop condition terminals contradict frozen syntax roles: truthy={} body={} exit={}, falsy={} body={} exit={}, control={:?}",
            condition.truthy,
            truthy_body,
            truthy_exit,
            condition.falsy,
            falsy_body,
            falsy_exit,
            payload.control_edges,
        )));
    }
    let body_on_truthy = truthy_body;
    Ok(LoopConditionProtocol {
        condition: condition_id,
        body_edge: if body_on_truthy {
            condition.truthy
        } else {
            condition.falsy
        },
        exit_edge: if body_on_truthy {
            condition.falsy
        } else {
            condition.truthy
        },
        body_on_truthy,
    })
}

fn freeze_numeric_for_protocol(
    proto: &LoweredProto,
    plan: &StructurePlan,
    region: RegionId,
    payload: &LoopPlanData,
    body_completes_normally: bool,
) -> Result<NumericForProtocol, StructureError> {
    let preheader = payload
        .preheader_block
        .ok_or_else(|| StructureError::invalid("numeric-for loop has no frozen preheader block"))?;
    let terminator = plan
        .block_terminator(preheader)
        .ok_or_else(|| StructureError::invalid("numeric-for preheader has no terminator plan"))?;
    let BlockTerminatorKind::NumericForInit { instr, body, exit } = terminator.kind else {
        return Err(StructureError::invalid(
            "numeric-for preheader does not end with NumericForInit",
        ));
    };
    let Some(LowInstr::NumericForInit(init)) = proto.instrs.get(instr.index()) else {
        return Err(StructureError::invalid(
            "numeric-for protocol references a non-init opcode",
        ));
    };
    if payload.control_edges.preheader_body != Some(body)
        || payload.control_edges.preheader_exit != Some(exit)
        || !matches!(payload.source_bindings, Some(LoopSourceBindings::Numeric(reg)) if reg == init.binding)
    {
        return Err(StructureError::invalid(format!(
            "numeric-for loop #{} contradicts its VM preheader contract",
            region.index()
        )));
    }
    Ok(NumericForProtocol {
        init_instr: instr,
        body_edge: body,
        exit_edge: exit,
        body_completes_normally,
        index: init.index,
        limit: init.limit,
        step: init.step,
        binding: init.binding,
    })
}

fn freeze_generic_for_protocol(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    region: RegionId,
    payload: &LoopPlanData,
    body_completes_normally: bool,
) -> Result<GenericForProtocol, StructureError> {
    let header_terminator = plan
        .block_terminator(payload.header)
        .ok_or_else(|| StructureError::invalid("generic-for header has no terminator plan"))?;
    let BlockTerminatorKind::GenericForLoop {
        instr: loop_instr_ref,
        body,
        exit,
    } = header_terminator.kind
    else {
        return Err(StructureError::invalid(
            "generic-for header does not end with GenericForLoop",
        ));
    };
    let Some((call_instr_ref, call, loop_instr)) =
        generic_for_header_instrs(proto, header_terminator)
    else {
        return Err(StructureError::invalid(
            "generic-for header has no stable call/loop pair",
        ));
    };
    let preheader = payload
        .preheader_block
        .ok_or_else(|| StructureError::invalid("generic-for loop has no frozen preheader block"))?;
    let preheader_terminator = plan
        .block_terminator(preheader)
        .ok_or_else(|| StructureError::invalid("generic-for preheader has no terminator plan"))?;
    let (prep_instr, iterator) = generic_for_source(proto, preheader, preheader_terminator, call)?;
    if !payload.control_edges.body.contains(&body) || !payload.control_edges.exit.contains(&exit) {
        return Err(StructureError::invalid(format!(
            "generic-for loop #{} contradicts its syntax edges: body={body} in {:?}, exit={exit} in {:?}",
            region.index(),
            payload.control_edges.body,
            payload.control_edges.exit,
        )));
    }
    if !matches!(
        payload.source_bindings,
        Some(LoopSourceBindings::Generic(bindings)) if bindings == loop_instr.bindings
    ) {
        return Err(StructureError::invalid(format!(
            "generic-for loop #{} contradicts its selected bindings",
            region.index()
        )));
    }
    Ok(GenericForProtocol {
        prep_instr,
        call_instr: call_instr_ref,
        loop_instr: loop_instr_ref,
        body_edge: body,
        exit_edge: exit,
        body_completes_normally,
        iterator,
        bindings: loop_instr.bindings,
        immediate_break: super::super::helpers::share_transparent_jump_target(
            proto,
            cfg,
            loop_instr.exit_target,
            loop_instr.body_target,
        ),
    })
}

/// 一次 edge sweep 冻结 VM-for body 是否存在普通完成路径。
///
/// HIR 形状会受表达式内联和可读性规范化影响，不能再检查 lowering 后最后一条语句。
/// region relation 已把跨 `body -> control` 的物理边投影到 loop 的直接 child，因此一条
/// edge 最多证明一个 loop，不会按 loop 重扫整个 CFG。显式 continue/goto 是终止当前
/// HIR body 的语句；自然边、普通条件 arm、本 loop 回边，以及最后一个 structured
/// child 被自身语法吸收的 exit，都会让外围 body 在 child 之后继续。
fn freeze_vm_for_body_completion(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<Vec<bool>, StructureError> {
    let mut completion = vec![false; plan.loops.len()];
    let mut body_tail = vec![None; plan.loops.len()];
    for (index, payload) in plan.loops.iter().enumerate() {
        if !matches!(
            payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) {
            continue;
        }
        let region = plan
            .loop_region_by_plan
            .get(index)
            .copied()
            .ok_or_else(|| StructureError::invalid("loop region reverse index is stale"))?;
        let body = match plan.region(region) {
            Some(RegionPlan::Loop { body, .. }) => *body,
            _ => {
                return Err(StructureError::invalid(
                    "VM-for protocol owner is not a loop region",
                ));
            }
        };
        let Some(RegionPlan::Sequence { children, .. }) = plan.region(body) else {
            return Err(StructureError::invalid(
                "VM-for body partition is not a sequence region",
            ));
        };
        completion[index] = children.is_empty();
        body_tail[index] = children.last().copied();
    }

    for edge in &plan.edge_plans {
        let cfg_edge = cfg.edges.get(edge.edge.index()).ok_or_else(|| {
            StructureError::invalid("planned VM-for completion edge is outside the CFG arena")
        })?;
        let relation = plan
            .edge_region_relation(edge.edge)
            .ok_or_else(|| StructureError::invalid("planned edge has no region relation"))?;
        let Some(loop_region) = relation.lca else {
            continue;
        };
        let Some(RegionPlan::Loop {
            plan: loop_id,
            body,
            control,
            ..
        }) = plan.region(loop_region)
        else {
            continue;
        };
        let Some(payload) = plan.loops.get(loop_id.index()) else {
            return Err(StructureError::invalid(
                "loop region references a missing payload",
            ));
        };
        if !matches!(
            payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) || relation.source_child != Some(*body)
            || relation.target_child != Some(*control)
        {
            continue;
        }
        let Some(tail) = body_tail[loop_id.index()] else {
            continue;
        };
        let Some(source_owner) = relation.source_owner else {
            continue;
        };
        if !region_completion_port_accepts(plan, tail, source_owner, cfg_edge.from) {
            continue;
        }
        let nested_structured_exit = plan.region_contains(tail, edge.owner)
            && matches!(
                edge.transfer,
                EdgeTransfer::Break(_) | EdgeTransfer::BranchArm(super::BranchArm::LoopExit)
            );
        let completes = matches!(
            edge.transfer,
            EdgeTransfer::Fallthrough
                | EdgeTransfer::BranchArm(super::BranchArm::Truthy | super::BranchArm::Falsy)
        ) || matches!(edge.transfer, EdgeTransfer::LoopBack(owner) if owner == loop_region)
            || nested_structured_exit;
        if completes {
            completion[loop_id.index()] = true;
        }
    }
    Ok(completion)
}

fn region_completion_port_accepts(
    plan: &StructurePlan,
    tail: RegionId,
    source_owner: RegionId,
    source_block: BlockRef,
) -> bool {
    if !plan
        .navigation
        .region_can_complete_from(tail, source_owner, source_block)
    {
        return false;
    }

    let mut current = Some(source_owner);
    while let Some(region) = current {
        if matches!(plan.region(region), Some(RegionPlan::Unstructured { .. }))
            && !plan
                .navigation
                .region_can_complete_from(region, source_owner, source_block)
        {
            return false;
        }
        if region == tail {
            return true;
        }
        current = plan
            .navigation
            .parent
            .get(region.index())
            .copied()
            .flatten();
    }
    false
}

fn freeze_value_actions(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    payload: &LoopPlanData,
) -> Result<LoopValueActions, StructureError> {
    if !matches!(
        payload.kind,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        return Ok(LoopValueActions::default());
    }
    let control = loop_control_region(plan, owner)?;
    let context = LoopValueContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        owner,
        control,
        payload,
    };
    let mut actions = LoopValueActions::default();
    if let Some(edge) = payload.control_edges.preheader_body {
        let copies = edge_copies(plan, owner, edge)?;
        let (before, body, elided) = classify_edge_copies(&context, copies)?;
        push_batch(&mut actions.batches, LoopValuePhase::BeforeLoop, before);
        push_batch(&mut actions.batches, LoopValuePhase::BodyPrologue, body);
        actions.elided.extend(elided);
    }

    let mut latch_edges = payload.control_edges.body.clone();
    latch_edges.extend(
        payload
            .control_edges
            .backedges
            .iter()
            .copied()
            .filter(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|cfg_edge| block_is_in_region(plan, control, cfg_edge.from))
            }),
    );
    latch_edges.sort_by_key(|edge| edge.index());
    latch_edges.dedup();
    let latch_copies = uniform_edge_copies(plan, owner, &latch_edges)?;
    let (iteration, elided) = classify_latch_copies(&context, latch_copies)?;
    actions.elided.extend(elided);
    push_batch(
        &mut actions.batches,
        if payload.kind == LoopKindHint::GenericForLike {
            LoopValuePhase::BodyPrologue
        } else {
            LoopValuePhase::LatchEpilogue
        },
        iteration,
    );

    // 普通 body 回边仍由自己的 region 执行真实 carried copy；但 VM-for 的隐藏
    // control copy 已被循环语法消费，不能因此物化一个源码 local。
    for edge in payload.control_edges.backedges.iter().copied() {
        if latch_edges.binary_search(&edge).is_ok() {
            continue;
        }
        if analysis
            .absorbed_owner_by_edge
            .get(edge.index())
            .copied()
            .flatten()
            .and_then(|loop_id| plan.loop_region(loop_id))
            .is_some_and(|absorbed_owner| absorbed_owner != owner)
        {
            continue;
        }
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("loop backedge has no final edge plan"))?;
        for copy in &edge_plan.phi_copies {
            let origin = EdgeCopyOrigin {
                edge,
                target: copy.phi_id,
            };
            if classify_copy_source(&context, copy.value, copy.phi_id, &[origin])?.is_none() {
                actions.elided.push(origin);
            }
        }
    }

    let exit = freeze_exit_actions(&context)?;
    push_batch(
        &mut actions.batches,
        LoopValuePhase::BeforeLoop,
        exit.before_loop,
    );
    push_batch(
        &mut actions.batches,
        LoopValuePhase::IterationEpilogue,
        exit.iteration_epilogue,
    );
    push_batch(
        &mut actions.batches,
        LoopValuePhase::AfterLoop,
        exit.after_loop,
    );
    actions.elided.extend(exit.elided);
    actions.elided.sort();
    actions.elided.dedup();
    Ok(actions)
}

fn freeze_exit_actions(
    context: &LoopValueContext<'_>,
) -> Result<FrozenExitActions, StructureError> {
    let LoopValueContext {
        dataflow,
        plan,
        owner,
        payload,
        ..
    } = *context;
    let preheader = payload
        .control_edges
        .preheader_exit
        .map(|edge| edge_copies(plan, owner, edge))
        .transpose()?
        .unwrap_or_default();
    let normal = uniform_edge_copies(plan, owner, &payload.control_edges.exit)?;
    if preheader.is_empty() && normal.is_empty() {
        return Ok(FrozenExitActions::default());
    }

    let mut by_target = BTreeMap::<
        PhiId,
        (
            Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
            Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
        ),
    >::new();
    for (edge, copy) in preheader {
        by_target.entry(copy.phi_id).or_default().0 = Some((
            copy.value,
            vec![EdgeCopyOrigin {
                edge,
                target: copy.phi_id,
            }],
        ));
    }
    for (copy, origins) in normal {
        let entry = by_target.entry(copy.phi_id).or_default();
        match &mut entry.1 {
            Some((value, existing_origins)) if *value == copy.value => {
                existing_origins.extend(origins);
            }
            Some(_) => {
                return Err(StructureError::invalid(
                    "loop exit syntax edges disagree on their frozen copies",
                ));
            }
            slot @ None => {
                *slot = Some((copy.value, origins));
            }
        }
    }

    let break_targets = payload
        .break_edges
        .iter()
        .copied()
        .filter(|edge| {
            !payload.control_edges.exit.contains(edge)
                && payload.control_edges.preheader_exit != Some(*edge)
        })
        .flat_map(|edge| {
            plan.edge_plan(edge)
                .into_iter()
                .flat_map(|plan| plan.phi_copies.iter().map(|copy| copy.phi_id))
        })
        .collect::<BTreeSet<_>>();

    let mut actions = FrozenExitActions::default();
    for (target, (zero_value, normal_value)) in by_target {
        if break_targets.contains(&target) {
            let (value, origins) = common_exit_value(
                target,
                zero_value,
                normal_value,
                "for early-break state has no common normal default",
            )?;
            match classify_copy_source(context, value, target, &origins)? {
                Some(source) => actions.before_loop.push(LoopValueWrite {
                    target,
                    source,
                    origins,
                }),
                None => actions.elided.extend(origins),
            }
            continue;
        }

        let reg = dataflow
            .phi_candidate(target)
            .ok_or_else(|| StructureError::invalid("for exit action targets a missing phi"))?
            .reg;
        if let Some(header) = payload.header_values.iter().find(|value| value.reg == reg) {
            let zero_matches = zero_value.as_ref().is_none_or(|(value, _)| {
                header
                    .outside_arm
                    .values()
                    .any(|incoming| incoming == *value)
            });
            let normal_matches = normal_value.as_ref().is_none_or(|(value, _)| {
                *value == SsaValue::Phi(header.phi_id)
                    || header
                        .inside_arm
                        .values()
                        .any(|incoming| incoming == *value)
            });
            if !zero_matches || !normal_matches {
                return Err(StructureError::invalid(
                    "for exit actions contradict the selected loop state",
                ));
            }
            let mut origins = Vec::new();
            if let Some((_, source)) = zero_value {
                origins.extend(source);
            }
            if let Some((_, source)) = normal_value {
                origins.extend(source);
            }
            origins.sort();
            origins.dedup();
            actions.after_loop.push(LoopValueWrite {
                target,
                source: LoopValueSource::Carried(header.phi_id),
                origins,
            });
            continue;
        }

        if let (Some((zero, zero_origins)), Some((normal, normal_origins))) =
            (zero_value.as_ref(), normal_value.as_ref())
            && zero != normal
        {
            if let Some(source) = classify_copy_source(context, *zero, target, zero_origins)? {
                actions.before_loop.push(LoopValueWrite {
                    target,
                    source,
                    origins: zero_origins.clone(),
                });
            } else {
                actions.elided.extend(zero_origins.iter().copied());
            }
            if let Some(source) = classify_copy_source(context, *normal, target, normal_origins)? {
                actions.iteration_epilogue.push(LoopValueWrite {
                    target,
                    source,
                    origins: normal_origins.clone(),
                });
            } else {
                actions.elided.extend(normal_origins.iter().copied());
            }
            continue;
        }

        let (value, origins) = common_exit_value(
            target,
            zero_value,
            normal_value,
            "for exit actions have no common state identity",
        )?;
        match classify_copy_source(context, value, target, &origins)? {
            Some(source) => actions.after_loop.push(LoopValueWrite {
                target,
                source,
                origins,
            }),
            None => actions.elided.extend(origins),
        }
    }
    Ok(actions)
}

fn common_exit_value(
    target: PhiId,
    zero_value: Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
    normal_value: Option<(SsaValue, Vec<EdgeCopyOrigin>)>,
    error: &str,
) -> Result<(SsaValue, Vec<EdgeCopyOrigin>), StructureError> {
    match (zero_value, normal_value) {
        (Some((zero, mut zero_origins)), Some((normal, normal_origins))) if zero == normal => {
            zero_origins.extend(normal_origins);
            zero_origins.sort();
            zero_origins.dedup();
            Ok((zero, zero_origins))
        }
        (Some((value, origins)), None) | (None, Some((value, origins))) => Ok((value, origins)),
        (zero, normal) => Err(StructureError::invalid(format!(
            "{error}: {target} zero={zero:?} normal={normal:?}"
        ))),
    }
}

type ClassifiedEdgeCopies = (
    Vec<LoopValueWrite>,
    Vec<LoopValueWrite>,
    Vec<EdgeCopyOrigin>,
);

fn classify_edge_copies(
    context: &LoopValueContext<'_>,
    copies: Vec<(EdgeRef, crate::structure::PhiEdgeCopy)>,
) -> Result<ClassifiedEdgeCopies, StructureError> {
    let mut before = Vec::new();
    let mut body = Vec::new();
    let mut elided = Vec::new();
    for (edge, copy) in copies {
        let mut origins = vec![EdgeCopyOrigin {
            edge,
            target: copy.phi_id,
        }];
        origins.sort();
        let Some(source) = classify_copy_source(context, copy.value, copy.phi_id, &origins)? else {
            elided.extend(origins);
            continue;
        };
        let write = LoopValueWrite {
            target: copy.phi_id,
            source,
            origins,
        };
        if matches!(write.source, LoopValueSource::Binding(_)) {
            body.push(write);
        } else {
            before.push(write);
        }
    }
    Ok((before, body, elided))
}

fn classify_latch_copies(
    context: &LoopValueContext<'_>,
    copies: Vec<(crate::structure::PhiEdgeCopy, Vec<EdgeCopyOrigin>)>,
) -> Result<(Vec<LoopValueWrite>, Vec<EdgeCopyOrigin>), StructureError> {
    let mut writes = Vec::new();
    let mut elided = Vec::new();
    for (copy, mut origins) in copies {
        origins.sort();
        let Some(source) = classify_latch_copy_source(context, copy.value, copy.phi_id, &origins)?
        else {
            elided.extend(origins);
            continue;
        };
        writes.push(LoopValueWrite {
            target: copy.phi_id,
            source,
            origins,
        });
    }
    Ok((writes, elided))
}

fn classify_latch_copy_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
    origins: &[EdgeCopyOrigin],
) -> Result<Option<LoopValueSource>, StructureError> {
    if context.payload.kind == LoopKindHint::NumericForLike
        && target_is_vm_for_control(
            context.proto,
            context.dataflow,
            context.plan,
            context.payload,
            target,
        )
        && context
            .analysis
            .value_is_vm_for_control(context.proto, context.dataflow, value)
    {
        // 下一轮 body 会先由 BodyPrologue 重新绑定；normal latch 的同值写回不可观察。
        // 仍调用通用分类以保留 escape 校验，不能把同一规则扩大到 preheader。
        return classify_value_source(context, value, target).map(|_| None);
    }
    classify_copy_source(context, value, target, origins)
}

fn classify_copy_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
    origins: &[EdgeCopyOrigin],
) -> Result<Option<LoopValueSource>, StructureError> {
    if !origins.is_empty()
        && origins.iter().all(|origin| {
            edge_copy_is_ancestor_vm_control(
                context.proto,
                context.dataflow,
                context.plan,
                context.analysis,
                context.owner,
                origin.edge,
                crate::structure::PhiEdgeCopy {
                    phi_id: target,
                    value,
                },
            )
        })
    {
        return Ok(None);
    }
    classify_value_source(context, value, target)
}

fn classify_value_source(
    context: &LoopValueContext<'_>,
    value: SsaValue,
    target: PhiId,
) -> Result<Option<LoopValueSource>, StructureError> {
    if target_is_vm_for_control(
        context.proto,
        context.dataflow,
        context.plan,
        context.payload,
        target,
    ) {
        let numeric_binding = context.payload.kind == LoopKindHint::NumericForLike;
        let syntax_region = if numeric_binding {
            context.owner
        } else {
            context.control
        };
        if context
            .analysis
            .phi_observed_outside(context.plan, syntax_region, target)
        {
            return Err(StructureError::invalid(format!(
                "VM for-control value {value:?} for {target} escapes loop header {} syntax region #{}",
                context.payload.header,
                syntax_region.index(),
            )));
        }
        if !numeric_binding
            || numeric_binding_is_protocol_only(context.proto, context.dataflow, target)
        {
            return Ok(None);
        }
    }
    if let Some(binding) = binding_source(context.dataflow, context.payload, value) {
        return Ok(Some(LoopValueSource::Binding(binding)));
    }
    if context
        .analysis
        .value_is_vm_for_control(context.proto, context.dataflow, value)
    {
        if context
            .analysis
            .phi_observed_outside(context.plan, context.control, target)
        {
            return Err(StructureError::invalid(format!(
                "VM for-control value {value:?} for {target} escapes loop header {} control region #{}",
                context.payload.header,
                context.control.index(),
            )));
        }
        return Ok(None);
    }
    Ok(Some(LoopValueSource::Ssa(value)))
}

fn numeric_binding_is_protocol_only(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    target: PhiId,
) -> bool {
    dataflow
        .phi_phi_uses
        .get(target.index())
        .is_some_and(Vec::is_empty)
        && dataflow.phi_uses.get(target.index()).is_some_and(|uses| {
            uses.iter().all(|site| {
                matches!(
                    proto.instrs.get(site.instr.index()),
                    Some(LowInstr::NumericForLoop(loop_))
                        if loop_.index == loop_.binding && site.reg == loop_.binding
                )
            })
        })
}

fn target_is_vm_for_control(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    payload: &LoopPlanData,
    target: PhiId,
) -> bool {
    let Some(candidate) = dataflow.phi_candidate(target) else {
        return false;
    };
    match payload.source_bindings {
        Some(LoopSourceBindings::Numeric(binding)) => {
            payload.kind == LoopKindHint::NumericForLike
                && candidate.block == payload.header
                && candidate.reg == binding
        }
        Some(LoopSourceBindings::Generic(_)) if payload.kind == LoopKindHint::GenericForLike => {
            let Some(terminator) = plan.block_terminator(payload.header) else {
                return false;
            };
            let Some((_, call, loop_)) = generic_for_header_instrs(proto, terminator) else {
                return false;
            };
            candidate.block == payload.header
                && candidate.reg == call.control
                && candidate.reg == loop_.control_target
        }
        _ => false,
    }
}

fn binding_source(
    dataflow: &DataflowFacts,
    payload: &LoopPlanData,
    value: SsaValue,
) -> Option<Reg> {
    let reg = match value {
        SsaValue::Def(def) => dataflow.def_reg(def),
        SsaValue::Phi(phi) => dataflow.phi_candidate(phi)?.reg,
        SsaValue::Entry(reg) => reg,
    };
    match payload.source_bindings? {
        LoopSourceBindings::Numeric(binding) if reg == binding => Some(reg),
        LoopSourceBindings::Generic(bindings)
            if reg.index() >= bindings.start.index()
                && reg.index() < bindings.start.index() + bindings.len =>
        {
            Some(reg)
        }
        _ => None,
    }
}

fn edge_copies(
    plan: &StructurePlan,
    owner: RegionId,
    edge: EdgeRef,
) -> Result<Vec<(EdgeRef, crate::structure::PhiEdgeCopy)>, StructureError> {
    let plan = plan
        .edge_plan(edge)
        .ok_or_else(|| StructureError::invalid("loop syntax edge has no final edge plan"))?;
    Ok(if plan.owner == owner {
        plan.phi_copies
            .iter()
            .copied()
            .map(|copy| (edge, copy))
            .collect()
    } else {
        Vec::new()
    })
}

fn uniform_edge_copies(
    plan: &StructurePlan,
    owner: RegionId,
    edges: &[EdgeRef],
) -> Result<Vec<(crate::structure::PhiEdgeCopy, Vec<EdgeCopyOrigin>)>, StructureError> {
    let Some(first) = edges.first().copied() else {
        return Ok(Vec::new());
    };
    let first_copies = edge_copies(plan, owner, first)?;
    let mut uniform = first_copies
        .iter()
        .map(|(_, copy)| {
            (
                *copy,
                vec![EdgeCopyOrigin {
                    edge: first,
                    target: copy.phi_id,
                }],
            )
        })
        .collect::<Vec<_>>();
    for edge in &edges[1..] {
        let copies = edge_copies(plan, owner, *edge)?;
        if copies.len() != uniform.len()
            || copies
                .iter()
                .map(|(_, copy)| *copy)
                .zip(uniform.iter().map(|(copy, _)| *copy))
                .any(|(left, right)| left != right)
        {
            return Err(StructureError::invalid(
                "alternative for syntax edges require different value actions",
            ));
        }
        for ((_, copy), (_, origins)) in copies.into_iter().zip(uniform.iter_mut()) {
            origins.push(EdgeCopyOrigin {
                edge: *edge,
                target: copy.phi_id,
            });
        }
    }
    Ok(uniform)
}

fn push_batch(
    batches: &mut Vec<LoopValueActionBatch>,
    phase: LoopValuePhase,
    writes: Vec<LoopValueWrite>,
) {
    if writes.is_empty() {
        return;
    }
    batches.push(LoopValueActionBatch { phase, writes });
}

fn edge_is_loop_body(payload: &LoopPlanData, edge: EdgeRef) -> bool {
    payload.control_edges.preheader_body == Some(edge) || payload.control_edges.body.contains(&edge)
}

fn edge_is_loop_exit(payload: &LoopPlanData, edge: EdgeRef) -> bool {
    payload.control_edges.preheader_exit == Some(edge) || payload.control_edges.exit.contains(&edge)
}

fn edge_emits_no_stmt(plan: &StructurePlan, edge: EdgeRef) -> bool {
    plan.edge_plan(edge).is_some_and(|edge_plan| {
        edge_plan.phi_copies.is_empty()
            && edge_plan.actions_before_trailing_cleanup().is_none()
            && !matches!(
                edge_plan.transfer,
                EdgeTransfer::Break(_) | EdgeTransfer::Continue(_) | EdgeTransfer::Goto(..)
            )
            && plan.loop_exit_tail_for_edge(edge).is_none()
    })
}

fn freeze_repeat_value_plan(
    context: &LoopValueContext<'_>,
    backedge: EdgeRef,
    exit: EdgeRef,
) -> Result<LoopRepeatValuePlan, StructureError> {
    let LoopValueContext {
        proto,
        cfg,
        dataflow,
        plan,
        analysis,
        owner,
        payload,
        ..
    } = *context;
    let Some(edge_plan) = plan.edge_plan(exit) else {
        return Err(StructureError::invalid(
            "repeat exit has no final edge plan",
        ));
    };
    let early_breaks = payload
        .break_edges
        .iter()
        .copied()
        .filter(|edge| *edge != exit)
        .collect::<Vec<_>>();
    let early_break_copies = early_breaks
        .iter()
        .map(|edge| crate::structure::phi_facts::effective_edge_copies(cfg, dataflow, plan, *edge))
        .collect::<Result<Vec<_>, _>>()?;
    let mut value_plan = LoopRepeatValuePlan::default();
    let backedge_plan = plan
        .edge_plan(backedge)
        .ok_or_else(|| StructureError::invalid("repeat backedge has no final edge plan"))?;
    if matches!(backedge_plan.transfer, EdgeTransfer::LoopBack(target) if target == owner)
        && backedge_plan.actions_before_trailing_cleanup().is_none()
        && backedge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(backedge).is_none()
    {
        value_plan
            .backedge_copies
            .extend(crate::structure::phi_facts::effective_edge_copies(
                cfg, dataflow, plan, backedge,
            )?);
    }
    value_plan
        .exit_copies
        .extend(crate::structure::phi_facts::effective_edge_copies(
            cfg, dataflow, plan, exit,
        )?);
    for copy in value_plan.exit_copies.iter().copied() {
        if edge_copy_is_ancestor_vm_control(proto, dataflow, plan, analysis, owner, exit, copy) {
            value_plan.outer_loop_owned_exit_copies.push(copy);
        }
    }
    if !matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
        || edge_plan.actions_before_trailing_cleanup().is_some()
        || edge_plan.forward_route.is_some()
        || plan.loop_exit_tail_for_edge(exit).is_some()
    {
        return Ok(value_plan);
    }
    let Some(condition_header) = payload
        .condition
        .and_then(|condition| plan.condition(condition))
        .and_then(|condition| condition.header())
    else {
        return Ok(value_plan);
    };
    let local_exit_copies = locally_owned_repeat_exit_copies(&value_plan).collect::<Vec<_>>();
    let mut early_break_coverage = vec![0usize; dataflow.phi_candidates.len()];
    let mut duplicate_early_break_copy = vec![false; dataflow.phi_candidates.len()];
    let mut seen_at_break = vec![usize::MAX; dataflow.phi_candidates.len()];
    let mut early_break_transfers_valid = true;
    for (break_index, (edge, copies)) in early_breaks.iter().zip(&early_break_copies).enumerate() {
        early_break_transfers_valid &= plan
            .edge_plan(*edge)
            .is_some_and(|edge_plan| {
                matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
            });
        for early in copies {
            let Some(seen) = seen_at_break.get_mut(early.phi_id.index()) else {
                continue;
            };
            if *seen == break_index {
                duplicate_early_break_copy[early.phi_id.index()] = true;
            } else {
                *seen = break_index;
                early_break_coverage[early.phi_id.index()] += 1;
            }
        }
    }
    for copy in &local_exit_copies {
        let early_breaks_cover_target = early_break_transfers_valid
            && (early_breaks.is_empty()
                || early_break_coverage.get(copy.phi_id.index()).copied()
                    == Some(early_breaks.len())
                    && !duplicate_early_break_copy
                        .get(copy.phi_id.index())
                        .copied()
                        .unwrap_or(true));
        if copy.value == SsaValue::Phi(copy.phi_id)
            || !repeat_normal_value_is_stable(
                plan,
                dataflow,
                payload.header,
                condition_header,
                copy.value,
            )
            || !early_breaks_cover_target
        {
            value_plan.staged_results.clear();
            return Ok(value_plan);
        }
        value_plan.staged_results.push(LoopRepeatStagedResult {
            target: copy.phi_id,
            normal_value: copy.value,
        });
    }
    Ok(value_plan)
}

fn edge_copy_is_ancestor_vm_control(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    exit: EdgeRef,
    copy: crate::structure::PhiEdgeCopy,
) -> bool {
    let Some(phi) = plan.phi_plan(copy.phi_id) else {
        return false;
    };
    let mut incomings = phi
        .incomings
        .iter()
        .filter(|incoming| incoming.edge == Some(exit));
    let Some(incoming) = incomings.next() else {
        return false;
    };
    let super::PhiIncomingDisposition::LoopCarried(region) = incoming.disposition else {
        return false;
    };
    if incomings.next().is_some()
        || incoming.value != copy.value
        || region == owner
        || !plan.region_contains(region, owner)
    {
        return false;
    }
    let Some(RegionPlan::Loop {
        plan: loop_id,
        control,
        ..
    }) = plan.region(region)
    else {
        return false;
    };
    let Some(payload) = plan.loop_(*loop_id) else {
        return false;
    };
    matches!(
        payload.kind,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) && analysis.value_is_vm_for_control(proto, dataflow, copy.value)
        && !analysis.phi_observed_outside(plan, *control, copy.phi_id)
}

fn validate_repeat_outer_loop_owned_exit_copies(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    analysis: &LoopValueAnalysis,
    owner: RegionId,
    repeat: &LoopRepeatProtocol,
) -> Result<(), StructureError> {
    let exit = repeat.condition.exit_edge;
    if repeat.value_plan.exit_copies
        != crate::structure::phi_facts::effective_edge_copies(cfg, dataflow, plan, exit)?
    {
        return Err(StructureError::invalid(
            "repeat exit value plan does not match its canonical edge copies",
        ));
    }

    let mut exit_values = vec![None; dataflow.phi_candidates.len()];
    for copy in &repeat.value_plan.exit_copies {
        let slot = exit_values
            .get_mut(copy.phi_id.index())
            .ok_or_else(|| StructureError::invalid("repeat exit copy targets a missing phi"))?;
        if slot.replace(copy.value).is_some() {
            return Err(StructureError::invalid(
                "repeat exit contains duplicate canonical phi copies",
            ));
        }
    }
    let mut marked = vec![false; dataflow.phi_candidates.len()];
    for copy in &repeat.value_plan.outer_loop_owned_exit_copies {
        let slot = marked.get_mut(copy.phi_id.index()).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy targets a missing phi")
        })?;
        if std::mem::replace(slot, true)
            || exit_values.get(copy.phi_id.index()).copied().flatten() != Some(copy.value)
        {
            return Err(StructureError::invalid(
                "repeat exit has duplicate or non-canonical outer-loop-owned copies",
            ));
        }

        let phi = plan.phi_plan(copy.phi_id).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy targets a missing phi")
        })?;
        let mut incomings = phi
            .incomings
            .iter()
            .filter(|incoming| incoming.edge == Some(exit));
        let incoming = incomings.next().ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy has no exact phi incoming")
        })?;
        let super::PhiIncomingDisposition::LoopCarried(outer) = incoming.disposition else {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy is not owned by LoopCarried",
            ));
        };
        if incomings.next().is_some()
            || incoming.value != copy.value
            || outer == owner
            || !plan.region_contains(outer, owner)
        {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy has an ambiguous or non-ancestor owner",
            ));
        }
        let Some(RegionPlan::Loop {
            plan: outer_loop,
            control,
            ..
        }) = plan.region(outer)
        else {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy owner is not a loop region",
            ));
        };
        let outer_payload = plan.loop_(*outer_loop).ok_or_else(|| {
            StructureError::invalid("repeat outer-loop-owned copy owner has no loop payload")
        })?;
        if !matches!(
            outer_payload.kind,
            LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
        ) || !analysis.value_is_vm_for_control(proto, dataflow, copy.value)
            || analysis.phi_observed_outside(plan, *control, copy.phi_id)
        {
            return Err(StructureError::invalid(
                "repeat outer-loop-owned copy is not an unobservable ancestor VM-for control value",
            ));
        }
    }

    for copy in &repeat.value_plan.exit_copies {
        let proven =
            edge_copy_is_ancestor_vm_control(proto, dataflow, plan, analysis, owner, exit, *copy);
        if proven != marked.get(copy.phi_id.index()).copied().unwrap_or(false) {
            return Err(StructureError::invalid(
                "repeat exit copy partition disagrees with its outer loop-carried owner proof",
            ));
        }
    }
    Ok(())
}

fn repeat_normal_value_is_stable(
    plan: &StructurePlan,
    dataflow: &DataflowFacts,
    loop_header: BlockRef,
    condition_header: BlockRef,
    value: SsaValue,
) -> bool {
    match value {
        SsaValue::Entry(_) => true,
        SsaValue::Phi(phi) => plan
            .phi_plan(phi)
            .is_some_and(|phi| phi.block == condition_header),
        SsaValue::Def(def) => dataflow.defs.get(def.index()).is_some_and(|definition| {
            definition.block == condition_header
                || dataflow.block_entry_value(loop_header, definition.reg) == value
        }),
    }
}

fn locally_owned_repeat_exit_copies(
    value_plan: &LoopRepeatValuePlan,
) -> impl Iterator<Item = crate::structure::PhiEdgeCopy> + '_ {
    let mut outer = value_plan
        .outer_loop_owned_exit_copies
        .iter()
        .copied()
        .peekable();
    value_plan.exit_copies.iter().copied().filter(move |copy| {
        if outer.peek() == Some(copy) {
            outer.next();
            false
        } else {
            true
        }
    })
}

fn repeat_backedge_copies_are_movable(
    plan: &StructurePlan,
    owner: RegionId,
    backedge: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(backedge)
        .ok_or_else(|| StructureError::invalid("repeat backedge has no final edge plan"))?;
    Ok(!value_plan.backedge_copies.is_empty()
        && matches!(edge_plan.transfer, EdgeTransfer::LoopBack(target) if target == owner)
        && edge_plan.phi_copies == value_plan.backedge_copies
        && edge_plan.actions_before_trailing_cleanup().is_none()
        && edge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(backedge).is_none())
}

fn repeat_exit_is_plain_break(
    plan: &StructurePlan,
    owner: RegionId,
    exit: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let Some(edge_plan) = plan.edge_plan(exit) else {
        return Err(StructureError::invalid(
            "repeat exit has no final edge plan",
        ));
    };
    Ok(
        (matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
            || edge_plan.transfer == EdgeTransfer::BranchArm(super::BranchArm::LoopExit))
            && plan.loop_exit_tail_for_edge(exit).is_none()
            && locally_owned_repeat_exit_copies(value_plan)
                .next()
                .is_none(),
    )
}

fn repeat_exit_is_staged_break(
    plan: &StructurePlan,
    owner: RegionId,
    exit: EdgeRef,
    value_plan: &LoopRepeatValuePlan,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(exit)
        .ok_or_else(|| StructureError::invalid("repeat exit has no final edge plan"))?;
    let staged_targets = value_plan
        .staged_results
        .iter()
        .map(|result| result.target)
        .collect::<BTreeSet<_>>();
    let exit_targets = locally_owned_repeat_exit_copies(value_plan)
        .filter(|copy| copy.value != SsaValue::Phi(copy.phi_id))
        .map(|copy| copy.phi_id)
        .collect::<BTreeSet<_>>();
    Ok(!exit_targets.is_empty()
        && staged_targets == exit_targets
        && matches!(edge_plan.transfer, EdgeTransfer::Break(target) if target == owner)
        && edge_plan.actions_before_trailing_cleanup().is_none()
        && edge_plan.forward_route.is_none()
        && plan.loop_exit_tail_for_edge(exit).is_none())
}

fn repeat_exit_can_follow_native(
    plan: &StructurePlan,
    owner: RegionId,
    payload: &LoopPlanData,
    exit: EdgeRef,
) -> Result<bool, StructureError> {
    let edge_plan = plan
        .edge_plan(exit)
        .ok_or_else(|| StructureError::invalid("repeat exit has no final edge plan"))?;
    let has_early_break = payload.break_edges.iter().copied().any(|edge| {
        edge != exit
            && plan.edge_plan(edge).is_some_and(
                |edge| matches!(edge.transfer, EdgeTransfer::Break(target) if target == owner),
            )
    });
    if has_early_break
        || edge_plan.actions_before_trailing_cleanup().is_some()
        || plan.loop_exit_tail_for_edge(exit).is_some()
    {
        return Ok(false);
    }
    Ok(match edge_plan.transfer {
        EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_) | EdgeTransfer::Goto(..) => true,
        EdgeTransfer::LoopBack(target)
        | EdgeTransfer::Break(target)
        | EdgeTransfer::Continue(target) => target != owner,
        EdgeTransfer::Unreachable | EdgeTransfer::Return | EdgeTransfer::TailCall => false,
    })
}

fn generic_for_header_instrs(
    proto: &LoweredProto,
    terminator: &crate::structure::BlockTerminatorPlan,
) -> Option<(InstrRef, GenericForCallInstr, GenericForLoopInstr)> {
    let BlockTerminatorKind::GenericForLoop {
        instr: loop_instr_ref,
        ..
    } = terminator.kind
    else {
        return None;
    };
    let call_index = loop_instr_ref.index().checked_sub(1)?;
    if call_index < terminator.instrs.start.index() {
        return None;
    }
    let call_instr_ref = InstrRef(call_index);
    let LowInstr::GenericForCall(call) = proto.instrs.get(call_instr_ref.index())? else {
        return None;
    };
    let LowInstr::GenericForLoop(loop_instr) = proto.instrs.get(loop_instr_ref.index())? else {
        return None;
    };
    if call.results != crate::transformer::ResultPack::Fixed(loop_instr.bindings) {
        return None;
    }
    Some((call_instr_ref, *call, *loop_instr))
}

fn generic_for_source(
    proto: &LoweredProto,
    preheader: BlockRef,
    terminator: &crate::structure::BlockTerminatorPlan,
    call: GenericForCallInstr,
) -> Result<(Option<InstrRef>, RegRange), StructureError> {
    let prep_instr_ref = match terminator.kind {
        BlockTerminatorKind::Jump { instr, .. }
            if instr.index() > terminator.instrs.start.index() =>
        {
            Some(InstrRef(instr.index() - 1))
        }
        _ => None,
    };
    let Some((prep_instr_ref, prep)) =
        prep_instr_ref.and_then(|instr_ref| match proto.instrs.get(instr_ref.index())? {
            LowInstr::GenericForPrep(prep) => Some((instr_ref, *prep)),
            _ => None,
        })
    else {
        if call.state != Reg(call.iterator.index() + 1)
            || call.control != Reg(call.iterator.index() + 2)
        {
            return Err(StructureError::invalid(format!(
                "generic-for preheader {preheader} has no stable iterator triple",
            )));
        }
        return Ok((None, crate::transformer::RegRange::new(call.iterator, 3)));
    };
    validate_generic_prep(prep, call)?;
    Ok((
        Some(prep_instr_ref),
        crate::transformer::RegRange::new(prep.iterator, 4),
    ))
}

fn validate_generic_prep(
    prep: GenericForPrepInstr,
    call: GenericForCallInstr,
) -> Result<(), StructureError> {
    if prep.iterator != call.iterator
        || prep.state != call.state
        || prep.state != Reg(prep.iterator.index() + 1)
        || prep.control_source != Reg(prep.iterator.index() + 2)
        || prep.closing_source != Reg(prep.iterator.index() + 3)
        || prep.control_target != call.control
    {
        return Err(StructureError::invalid(
            "generic-for prep/call contract changed after planning",
        ));
    }
    Ok(())
}
