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

/// 完成最终 plan 的 value ownership，并把 canonical copies 直接写入对应 edge。
///
/// 这一步只消费已选中的 region payload。任何无法证明唯一 owner 的 live incoming 都
/// 显式标记为 `DiagnosticUnresolved`，不能再交给 HIR 猜一个 predecessor。
pub(super) fn finalize_phi_ownership(
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

fn collect_dense_edge_actions(
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
struct CanonicalBreakTarget {
    owner: RegionId,
    target: PhiId,
}

/// numeric/generic-for 的 exit phi 到 canonical header phi 的稠密反向索引。
///
/// 构建只遍历一次最终 loop payload；之后每个 incoming 的 canonical target 查询均为
/// O(1)，不会再对同一 loop 的 header/exit values 做交叉扫描。
pub(super) struct CanonicalEdgeCopyTargets {
    by_phi: Vec<Option<CanonicalBreakTarget>>,
}

impl CanonicalEdgeCopyTargets {
    pub(super) fn build(plan: &StructurePlan, phi_count: usize) -> Result<Self, StructureError> {
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

    pub(super) fn for_incoming(
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

pub(super) fn build_forwarded_action_heads(
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

pub(super) fn effective_edge_copies(
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

struct ForwardedActionComposer {
    route_epoch: usize,
    batch_epoch: usize,
    query_epoch: usize,
    current_route: Option<super::plan::ForwardRouteId>,
    def_memo_epoch: Vec<usize>,
    def_memo_value: Vec<SsaValue>,
    def_visiting_epoch: Vec<usize>,
    phi_value_epoch: Vec<usize>,
    phi_values: Vec<SsaValue>,
    phi_resolved_epoch: Vec<usize>,
    phi_resolved_values: Vec<SsaValue>,
    phi_query_epoch: Vec<usize>,
    target_batch_epoch: Vec<usize>,
    touched: Vec<PhiId>,
    def_path: Vec<crate::structure::DefId>,
    phi_path: Vec<PhiId>,
    pending: Vec<(PhiId, SsaValue)>,
}

impl ForwardedActionComposer {
    fn new(dataflow: &DataflowFacts) -> Self {
        Self {
            route_epoch: 0,
            batch_epoch: 0,
            query_epoch: 0,
            current_route: None,
            def_memo_epoch: vec![0; dataflow.defs.len()],
            def_memo_value: vec![SsaValue::Entry(Reg(0)); dataflow.defs.len()],
            def_visiting_epoch: vec![0; dataflow.defs.len()],
            phi_value_epoch: vec![0; dataflow.phi_candidates.len()],
            phi_values: vec![SsaValue::Entry(Reg(0)); dataflow.phi_candidates.len()],
            phi_resolved_epoch: vec![0; dataflow.phi_candidates.len()],
            phi_resolved_values: vec![SsaValue::Entry(Reg(0)); dataflow.phi_candidates.len()],
            phi_query_epoch: vec![0; dataflow.phi_candidates.len()],
            target_batch_epoch: vec![0; dataflow.phi_candidates.len()],
            touched: Vec::new(),
            def_path: Vec::new(),
            phi_path: Vec::new(),
            pending: Vec::new(),
        }
    }

    fn begin_route(
        &mut self,
        route: Option<super::plan::ForwardRouteId>,
    ) -> Result<(), StructureError> {
        self.route_epoch = self
            .route_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action route epoch overflow"))?;
        self.touched.clear();
        self.pending.clear();
        self.current_route = route;
        Ok(())
    }

    fn install_entry(&mut self, copies: &[PhiEdgeCopy]) -> Result<(), StructureError> {
        let batch = self.next_batch()?;
        for copy in copies {
            self.record_pending(copy.phi_id, copy.value, batch)?;
        }
        self.commit_pending()
    }

    fn apply_forwarded_batch(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        copies: &[PhiEdgeCopy],
        collapse_defs: bool,
    ) -> Result<(), StructureError> {
        let batch = self.next_batch()?;
        for copy in copies {
            let value = self.resolve_forwarded_value(
                cfg,
                dataflow,
                plan,
                copy.value,
                batch,
                collapse_defs,
            )?;
            self.record_pending(copy.phi_id, value, batch)?;
        }
        self.commit_pending()
    }

    fn next_batch(&mut self) -> Result<usize, StructureError> {
        self.batch_epoch = self
            .batch_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action batch epoch overflow"))?;
        self.pending.clear();
        Ok(self.batch_epoch)
    }

    fn record_pending(
        &mut self,
        target: PhiId,
        value: SsaValue,
        batch: usize,
    ) -> Result<(), StructureError> {
        let seen = self
            .target_batch_epoch
            .get_mut(target.index())
            .ok_or_else(|| {
                StructureError::invalid(format!("forwarded action targets missing {target}"))
            })?;
        if *seen == batch {
            return Err(StructureError::invalid(format!(
                "forwarded action batch writes {target} more than once"
            )));
        }
        *seen = batch;
        self.pending.push((target, value));
        Ok(())
    }

    fn commit_pending(&mut self) -> Result<(), StructureError> {
        for (target, value) in self.pending.drain(..) {
            let Some(epoch) = self.phi_value_epoch.get_mut(target.index()) else {
                return Err(StructureError::invalid(format!(
                    "forwarded action targets missing {target}"
                )));
            };
            if *epoch != self.route_epoch {
                self.touched.push(target);
            }
            *epoch = self.route_epoch;
            self.phi_values[target.index()] = value;
        }
        Ok(())
    }

    fn resolve_forwarded_value(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        mut value: SsaValue,
        batch: usize,
        collapse_defs: bool,
    ) -> Result<SsaValue, StructureError> {
        self.query_epoch = self
            .query_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action query epoch overflow"))?;
        self.phi_path.clear();
        let mut cycle = false;
        loop {
            if collapse_defs {
                value = self.collapse_forwarded_defs(cfg, dataflow, plan, value)?;
            }
            let SsaValue::Phi(phi) = value else {
                break;
            };
            let Some(value_epoch) = self.phi_value_epoch.get(phi.index()).copied() else {
                return Err(StructureError::invalid(format!(
                    "forwarded action references missing {phi}"
                )));
            };
            if self.phi_resolved_epoch[phi.index()] == batch {
                value = self.phi_resolved_values[phi.index()];
                break;
            }
            if value_epoch != self.route_epoch {
                break;
            }
            if self.phi_query_epoch[phi.index()] == self.query_epoch {
                cycle = true;
                break;
            }
            self.phi_query_epoch[phi.index()] = self.query_epoch;
            self.phi_path.push(phi);
            value = self.phi_values[phi.index()];
        }
        if !cycle {
            for phi in &self.phi_path {
                self.phi_resolved_epoch[phi.index()] = batch;
                self.phi_resolved_values[phi.index()] = value;
            }
        }
        Ok(value)
    }

    fn collapse_forwarded_defs(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        mut value: SsaValue,
    ) -> Result<SsaValue, StructureError> {
        self.def_path.clear();
        while let SsaValue::Def(def) = value {
            let Some(definition) = dataflow.defs.get(def.index()) else {
                return Err(StructureError::invalid(format!(
                    "forwarded action references missing {def}"
                )));
            };
            if self.def_memo_epoch[def.index()] == self.route_epoch {
                value = self.def_memo_value[def.index()];
                break;
            }
            if self.def_visiting_epoch[def.index()] == self.route_epoch {
                // 非法循环别名没有可继续证明的来源；保留重复处的 canonical def。
                break;
            }
            self.def_visiting_epoch[def.index()] = self.route_epoch;
            self.def_path.push(def);
            let Some(route) = self.current_route else {
                break;
            };
            if !cfg
                .succs
                .get(definition.block.index())
                .is_some_and(|edges| {
                    edges
                        .iter()
                        .any(|edge| plan.forward_route_contains_edge(route, *edge))
                })
            {
                break;
            }
            let uses = dataflow
                .use_values
                .get(definition.instr.index())
                .ok_or_else(|| {
                    StructureError::invalid(format!("{def} has no canonical use-value summary"))
                })?;
            let mut sources = uses.fixed.values();
            let Some(source) = sources.next() else {
                break;
            };
            if sources.next().is_some() {
                break;
            }
            value = source;
        }
        for def in &self.def_path {
            self.def_memo_epoch[def.index()] = self.route_epoch;
            self.def_memo_value[def.index()] = value;
        }
        Ok(value)
    }

    fn finish(&self) -> Result<Vec<PhiEdgeCopy>, StructureError> {
        self.touched
            .iter()
            .map(|phi_id| {
                if self.phi_value_epoch.get(phi_id.index()).copied() != Some(self.route_epoch) {
                    return Err(StructureError::invalid(format!(
                        "forwarded action lost the final value for {phi_id}"
                    )));
                }
                Ok(PhiEdgeCopy {
                    phi_id: *phi_id,
                    value: self.phi_values[phi_id.index()],
                })
            })
            .collect()
    }
}

fn install_phi_plans(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &mut StructurePlan,
    dispositions: Vec<Vec<PhiIncomingDisposition>>,
) -> Result<(), StructureError> {
    let mut phis = Vec::with_capacity(dataflow.phi_candidates.len());
    let mut phis_by_block = vec![Vec::new(); cfg.blocks.len()];
    let mut phis_by_region = vec![Vec::new(); plan.regions().len()];
    let mut region_seen_at = vec![usize::MAX; plan.regions().len()];

    for (phi, owners) in dataflow.phi_candidates.iter().zip(dispositions) {
        if phi.incoming.len() != owners.len() {
            return Err(StructureError::invalid(format!(
                "{} has {} owners for {} incomings",
                phi.id,
                owners.len(),
                phi.incoming.len()
            )));
        }
        let Some(block_phis) = phis_by_block.get_mut(phi.block.index()) else {
            return Err(StructureError::invalid(format!(
                "{} target block is outside the CFG arena",
                phi.id
            )));
        };
        block_phis.push(phi.id);

        let incomings = phi
            .incoming
            .iter()
            .zip(owners)
            .map(|(incoming, disposition)| PhiIncomingPlan {
                edge: incoming.edge,
                value: incoming.value,
                disposition,
            })
            .collect::<Vec<_>>();
        for incoming in &incomings {
            let Some(region) = incoming.disposition.region() else {
                continue;
            };
            let Some(seen) = region_seen_at.get_mut(region.index()) else {
                return Err(StructureError::invalid(format!(
                    "{} refers to missing value owner region {}",
                    phi.id,
                    region.index()
                )));
            };
            if *seen == phi.id.index() {
                continue;
            }
            *seen = phi.id.index();
            phis_by_region[region.index()].push(phi.id);
        }
        phis.push(PhiPlan {
            phi: phi.id,
            block: phi.block,
            reg: phi.reg,
            incomings,
        });
    }

    plan.phis = phis;
    plan.phis_by_block = phis_by_block;
    plan.phis_by_region = phis_by_region;
    Ok(())
}

fn validate_phi_arena(dataflow: &DataflowFacts) -> Result<(), StructureError> {
    for (index, phi) in dataflow.phi_candidates.iter().enumerate() {
        if phi.id.index() != index {
            return Err(StructureError::invalid(format!(
                "phi arena slot {index} contains {}",
                phi.id
            )));
        }
    }
    Ok(())
}

fn regions_owned_by_island_graph(plan: &StructurePlan) -> Result<Vec<bool>, StructureError> {
    let region_count = plan.regions().len();
    let mut resolved = vec![None; region_count];
    let mut visiting = vec![false; region_count];

    for start in 0..region_count {
        if resolved[start].is_some() {
            continue;
        }
        let mut path = Vec::new();
        let mut current = Some(RegionId(start));
        let inherited = loop {
            let Some(region) = current else {
                break false;
            };
            let Some(region_plan) = plan.region(region) else {
                return Err(StructureError::invalid(format!(
                    "region {} has a missing containment node",
                    region.index()
                )));
            };
            if let Some(flag) = resolved[region.index()] {
                break flag;
            }
            if visiting[region.index()] {
                return Err(StructureError::invalid(format!(
                    "region containment contains a cycle at {}",
                    region.index()
                )));
            }
            visiting[region.index()] = true;
            path.push(region);
            current = region_plan.parent();
        };

        let mut inherited = inherited;
        while let Some(region) = path.pop() {
            inherited = match plan.region(region) {
                Some(RegionPlan::Unstructured { .. }) => true,
                Some(
                    RegionPlan::Branch { .. }
                    | RegionPlan::ValueDecision { .. }
                    | RegionPlan::Loop { .. },
                ) => false,
                Some(RegionPlan::Block { .. } | RegionPlan::Sequence { .. }) => inherited,
                None => {
                    return Err(StructureError::invalid(format!(
                        "missing region {}",
                        region.index()
                    )));
                }
            };
            resolved[region.index()] = Some(inherited);
            visiting[region.index()] = false;
        }
    }

    Ok(resolved
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect())
}

fn claim_selected_region_values(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
) -> Result<(), StructureError> {
    let mut loop_incomings = LoopIncomingClassifier::new(dataflow)?;
    for (region_id, region) in plan.regions() {
        match region {
            RegionPlan::Branch {
                plan: branch_id,
                condition: _,
                ..
            } => {
                let branch = plan.branch(*branch_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "branch region {} references missing plan {}",
                        region_id.index(),
                        branch_id.index()
                    ))
                })?;
                claim_condition_values(
                    dataflow,
                    plan,
                    owner_index,
                    dispositions,
                    region_id,
                    branch.condition,
                )?;
                if let Some(merge) = &branch.value_plan {
                    for value in &merge.values {
                        claim_branch_result(dataflow, owner_index, dispositions, region_id, value)?;
                    }
                }
            }
            RegionPlan::Loop { plan: loop_id, .. } => {
                let loop_plan = plan.loop_(*loop_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop region {} references missing plan {}",
                        region_id.index(),
                        loop_id.index()
                    ))
                })?;
                if let Some(condition) = loop_plan.condition {
                    claim_condition_values(
                        dataflow,
                        plan,
                        owner_index,
                        dispositions,
                        region_id,
                        condition,
                    )?;
                }
                for value in &loop_plan.carried_values {
                    claim_loop_header_value(
                        dataflow,
                        owner_index,
                        dispositions,
                        region_id,
                        value,
                        &mut loop_incomings,
                    )?;
                }
                for exit in &loop_plan.exit_values {
                    for value in &exit.values {
                        claim_loop_result(
                            dataflow,
                            owner_index,
                            dispositions,
                            region_id,
                            value,
                            &mut loop_incomings,
                        )?;
                    }
                }
            }
            RegionPlan::ValueDecision { plan: decision, .. } => {
                let decision = plan.value_decision(*decision).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "value decision region {} references a missing payload",
                        region_id.index()
                    ))
                })?;
                for phi_id in std::iter::once(decision.result_phi)
                    .chain(decision.absorbed_phis.iter().copied())
                {
                    let phi = require_phi(dataflow, phi_id)?;
                    for slot in &mut dispositions[phi.id.index()] {
                        claim_owner(
                            owner_index,
                            slot,
                            PhiIncomingDisposition::RegionResult(region_id),
                        );
                    }
                }
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::Unstructured { .. } => {}
        }
    }
    Ok(())
}

fn claim_condition_values(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    condition: crate::structure::ConditionPlanId,
) -> Result<(), StructureError> {
    let condition = plan.condition(condition).ok_or_else(|| {
        StructureError::invalid("selected region references a missing condition value plan")
    })?;
    for node in &condition.nodes {
        let Some(value) = node.materialized_value else {
            continue;
        };
        let phi = require_phi(dataflow, value.phi)?;
        for slot in &mut dispositions[phi.id.index()] {
            claim_owner(
                owner_index,
                slot,
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}

pub(super) fn incoming_requires_edge_copy(
    plan: &StructurePlan,
    phi: PhiId,
    disposition: PhiIncomingDisposition,
) -> bool {
    !matches!(
        disposition,
        PhiIncomingDisposition::Dead | PhiIncomingDisposition::DiagnosticUnresolved
    ) && !(matches!(disposition, PhiIncomingDisposition::RegionResult(_))
        && (plan.condition_value_owner(phi).is_some() || plan.value_decision_owner(phi).is_some()))
}

fn claim_branch_result(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &BranchValueMergeValue,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    for (incoming_index, incoming) in phi.incoming.iter().enumerate() {
        if incoming.pred.is_some_and(|pred| {
            value.then_arm.preds.contains(&pred) || value.else_arm.preds.contains(&pred)
        }) {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}

fn claim_loop_header_value(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &LoopValueMerge,
    classifier: &mut LoopIncomingClassifier,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    let classes = classifier.classify(phi, &value.inside_arm, &value.outside_arm)?;
    for (incoming_index, class) in classes.into_iter().enumerate() {
        if class == (LOOP_INSIDE | LOOP_OUTSIDE) {
            return Err(StructureError::invalid(format!(
                "{} incoming #{incoming_index} belongs to both loop arms",
                phi.id
            )));
        }
        let owner = if class == LOOP_INSIDE {
            Some(PhiIncomingDisposition::LoopCarried(region))
        } else if class == LOOP_OUTSIDE {
            Some(PhiIncomingDisposition::RegionInput(region))
        } else {
            None
        };
        if let Some(owner) = owner {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                owner,
            );
        }
    }
    Ok(())
}

fn claim_loop_result(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
    region: RegionId,
    value: &LoopValueMerge,
    classifier: &mut LoopIncomingClassifier,
) -> Result<(), StructureError> {
    let phi = require_phi(dataflow, value.phi_id)?;
    let classes = classifier.classify(phi, &value.inside_arm, &value.outside_arm)?;
    for (incoming_index, class) in classes.into_iter().enumerate() {
        if class == (LOOP_INSIDE | LOOP_OUTSIDE) {
            return Err(StructureError::invalid(format!(
                "{} incoming #{incoming_index} belongs to both loop result arms",
                phi.id
            )));
        }
        if class & LOOP_INSIDE != 0 {
            claim_owner(
                owner_index,
                &mut dispositions[phi.id.index()][incoming_index],
                PhiIncomingDisposition::RegionResult(region),
            );
        }
    }
    Ok(())
}

const LOOP_INSIDE: u8 = 1;
const LOOP_OUTSIDE: u8 = 2;

/// 把 loop arm evidence 一次投影到 canonical incoming ordinal。
///
/// 同一 predecessor 的平行 CFG edge 读取相同 block-exit SSA 值，因此用稠密 block
/// 下标标记 arm membership；epoch 避免为每个 phi 清空整张 block arena。
struct LoopIncomingClassifier {
    epoch: usize,
    pred_epochs: Vec<usize>,
    pred_values: Vec<SsaValue>,
    pred_classes: Vec<u8>,
    synthetic_epoch: usize,
    synthetic_value: SsaValue,
    synthetic_class: u8,
}

impl LoopIncomingClassifier {
    fn new(dataflow: &DataflowFacts) -> Result<Self, StructureError> {
        let max_pred = dataflow
            .phi_candidates
            .iter()
            .flat_map(|phi| phi.incoming.iter().filter_map(|incoming| incoming.pred))
            .map(BlockRef::index)
            .max();
        let len = max_pred
            .map(|pred| {
                pred.checked_add(1).ok_or_else(|| {
                    StructureError::invalid("phi predecessor index overflows its dense arena")
                })
            })
            .transpose()?
            .unwrap_or(0);
        let mut pred_epochs = Vec::new();
        pred_epochs
            .try_reserve_exact(len)
            .map_err(|_| StructureError::invalid("phi predecessor arena is too large"))?;
        pred_epochs.resize(len, 0);
        Ok(Self {
            epoch: 0,
            pred_epochs,
            pred_values: vec![SsaValue::Entry(Reg(0)); len],
            pred_classes: vec![0; len],
            synthetic_epoch: 0,
            synthetic_value: SsaValue::Entry(Reg(0)),
            synthetic_class: 0,
        })
    }

    fn classify(
        &mut self,
        phi: &PhiCandidate,
        inside: &LoopValueArm,
        outside: &LoopValueArm,
    ) -> Result<Vec<u8>, StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("loop incoming classifier epoch overflow"))?;
        for incoming in &phi.incoming {
            self.record_canonical(phi.id, incoming.pred, incoming.value)?;
        }
        self.mark_arm(phi.id, inside, LOOP_INSIDE)?;
        self.mark_arm(phi.id, outside, LOOP_OUTSIDE)?;
        phi.incoming
            .iter()
            .map(|incoming| self.class_for(phi.id, incoming.pred, incoming.value))
            .collect()
    }

    fn record_canonical(
        &mut self,
        phi: PhiId,
        pred: Option<BlockRef>,
        value: SsaValue,
    ) -> Result<(), StructureError> {
        let (epoch, stored, class) = match pred {
            Some(pred) => {
                let index = pred.index();
                let Some(epoch) = self.pred_epochs.get_mut(index) else {
                    return Err(StructureError::invalid(format!(
                        "{phi} predecessor {pred} is outside the dense block arena"
                    )));
                };
                (
                    epoch,
                    &mut self.pred_values[index],
                    &mut self.pred_classes[index],
                )
            }
            None => (
                &mut self.synthetic_epoch,
                &mut self.synthetic_value,
                &mut self.synthetic_class,
            ),
        };
        if *epoch == self.epoch {
            if *stored != value {
                return Err(StructureError::invalid(format!(
                    "{phi} has inconsistent SSA values from one predecessor"
                )));
            }
        } else {
            *epoch = self.epoch;
            *stored = value;
            *class = 0;
        }
        Ok(())
    }

    fn mark_arm(&mut self, phi: PhiId, arm: &LoopValueArm, bit: u8) -> Result<(), StructureError> {
        for incoming in &arm.incomings {
            let (epoch, stored, class) = match incoming.pred {
                Some(pred) => {
                    let index = pred.index();
                    let Some(epoch) = self.pred_epochs.get(index) else {
                        return Err(StructureError::invalid(format!(
                            "{phi} loop arm predecessor {pred} is outside the dense block arena"
                        )));
                    };
                    (
                        epoch,
                        &self.pred_values[index],
                        &mut self.pred_classes[index],
                    )
                }
                None => (
                    &self.synthetic_epoch,
                    &self.synthetic_value,
                    &mut self.synthetic_class,
                ),
            };
            if *epoch != self.epoch || *stored != incoming.value {
                return Err(StructureError::invalid(format!(
                    "{phi} loop arm contains a non-canonical incoming"
                )));
            }
            *class |= bit;
        }
        Ok(())
    }

    fn class_for(
        &self,
        phi: PhiId,
        pred: Option<BlockRef>,
        value: SsaValue,
    ) -> Result<u8, StructureError> {
        let (epoch, stored, class) = match pred {
            Some(pred) => {
                let index = pred.index();
                let Some(epoch) = self.pred_epochs.get(index) else {
                    return Err(StructureError::invalid(format!(
                        "{phi} predecessor {pred} is outside the dense block arena"
                    )));
                };
                (epoch, &self.pred_values[index], self.pred_classes[index])
            }
            None => (
                &self.synthetic_epoch,
                &self.synthetic_value,
                self.synthetic_class,
            ),
        };
        if *epoch != self.epoch || *stored != value {
            return Err(StructureError::invalid(format!(
                "{phi} canonical incoming changed during loop classification"
            )));
        }
        Ok(class)
    }
}

fn require_phi(dataflow: &DataflowFacts, phi_id: PhiId) -> Result<&PhiCandidate, StructureError> {
    dataflow.phi_candidate(phi_id).ok_or_else(|| {
        StructureError::invalid(format!("selected value owner references missing {phi_id}"))
    })
}

fn claim_idom_inputs(
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

fn propagate_transitive_region_owners(
    dataflow: &DataflowFacts,
    owner_index: &RegionOwnerIndex,
    dispositions: &mut [Vec<Option<PhiIncomingDisposition>>],
) -> Result<(), StructureError> {
    fn consume_ready_uses(
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
struct RegionOwnerIndex {
    enter: Vec<usize>,
    exit: Vec<usize>,
    inside_branch: Vec<bool>,
    value_decision: Vec<bool>,
}

impl RegionOwnerIndex {
    fn new(plan: &StructurePlan) -> Result<Self, StructureError> {
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

    fn contains(&self, ancestor: RegionId, region: RegionId) -> bool {
        self.enter
            .get(ancestor.index())
            .zip(self.exit.get(ancestor.index()))
            .zip(self.enter.get(region.index()))
            .is_some_and(|((enter, exit), region)| *enter <= *region && *region < *exit)
    }

    fn inside_branch(&self, region: RegionId) -> bool {
        self.inside_branch
            .get(region.index())
            .copied()
            .unwrap_or(false)
    }

    fn is_value_decision(&self, region: RegionId) -> bool {
        self.value_decision
            .get(region.index())
            .copied()
            .unwrap_or(false)
    }

    fn more_specific(&self, left: RegionId, right: RegionId) -> Option<RegionId> {
        if self.contains(left, right) {
            Some(right)
        } else if self.contains(right, left) {
            Some(left)
        } else {
            None
        }
    }
}

fn claim_owner(
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

fn merge_structured_owners(
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

fn install_unresolved_requirements(
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

fn validate_phi_ownership(
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

fn extend_branch_value_arm(
    header: BlockRef,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    entry_value: SsaValue,
    arm: &mut BranchValueMergeArm,
    incoming: &crate::structure::PhiIncoming,
) {
    let Some(pred) = incoming.pred else {
        return;
    };
    arm.preds.insert(pred);
    arm.values.insert(incoming.value);
    let carries_entry = dataflow.value_contains(incoming.value, entry_value);
    // 非循环 header 的当前入口值不可能包含一个由 header 严格支配的定义；若能从
    // header 之后重新流回入口，就已经构成 backedge。顺序 branch 的 preserved arm
    // 因而无需反复展开随前序分支增长的整条 Phi 链。
    let needs_dominated_update_check = carries_entry
        && (incoming.value != entry_value || graph_facts.loop_headers.contains(&header));
    let is_dominated_update = needs_dominated_update_check
        && dataflow.leaf_defs(incoming.value).iter().any(|def| {
            let block = dataflow.def_block(*def);
            block != header && graph_facts.dominator_tree.dominates(header, block)
        });
    if carries_entry {
        arm.entry_values.insert(incoming.value);
    }
    if !carries_entry || is_dominated_update {
        arm.update_values.insert(incoming.value);
    }
}
