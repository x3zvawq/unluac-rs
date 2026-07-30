//! 这个文件实现词法 scope 计划提取与 cleanup owner 消解。
//!
//! 它依赖 graph facts 和显式 `Close` 指令，负责把真正含 cleanup 的 block 整理成
//! `ScopePlan`。
//! 它不会越权恢复最终词法块，只保留 HIR 需要的 entry/exit/close-point 事实。
//!
//! 例子：
//! - 不含 `Close` 的 loop/branch 不会产生空的 scope 候选
//! - 含 `Close` 的普通 block 会产出 scope 候选，让后面的结构化阶段直接知道
//!   这些 cleanup 点属于词法边界，而不是把 `Close` 当普通语句往后拖
//! - 每条 `Close/Tbc` 最终取得唯一 `CleanupDisposition`；for 词法边界只有在覆盖的
//!   显式 TBC 全部属于唯一 loop owner 时才交给该循环，HIR 不再重跑活跃性分析

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::structure::{BlockRef, Cfg, GraphFacts, StructurePlan};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg};

use super::common::ScopePlan;
use super::plan::{
    CleanupDisposition, LabelPlacement, LoopPlanData, RegionId, RegionPlan, ScopePlanId,
    StructureError, TbcScopePlan, TbcScopePlanId,
};

/// 显式 TBC 声明沿 CFG 传播后的 VM 作用域事实。
pub(super) struct TbcFlowFacts {
    active_in: Vec<BTreeSet<InstrRef>>,
    active_out: Vec<BTreeSet<InstrRef>>,
    close_origins: BTreeMap<InstrRef, BTreeSet<InstrRef>>,
}

impl TbcFlowFacts {
    pub(super) fn active_at_entry(&self, block: BlockRef) -> Option<&BTreeSet<InstrRef>> {
        self.active_in.get(block.index())
    }

    pub(super) fn active_after_block(&self, block: BlockRef) -> Option<&BTreeSet<InstrRef>> {
        self.active_out.get(block.index())
    }
}

pub(super) fn analyze_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Vec<ScopePlan> {
    let close_points_by_block = collect_close_points_by_block(proto, cfg);
    let mut scopes = close_points_by_block
        .into_iter()
        .map(|(block, close_points)| ScopePlan {
            entry: block,
            exit: immediate_postdom_exit(cfg, graph_facts, block),
            close_points,
        })
        .collect::<Vec<_>>();

    scopes.sort_by_key(|scope| {
        (
            scope.entry,
            scope.exit,
            scope
                .close_points
                .iter()
                .map(|instr| instr.index())
                .collect::<Vec<_>>(),
        )
    });
    scopes.dedup_by(|left, right| {
        left.entry == right.entry
            && left.exit == right.exit
            && left.close_points == right.close_points
    });
    scopes
}

pub(super) fn analyze_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(Vec<Option<CleanupDisposition>>, Vec<TbcScopePlan>), StructureError> {
    let tbc_flow = analyze_tbc_flow(proto, cfg);
    let explicit_tbc_close_origins = &tbc_flow.close_origins;
    let mut lexical_owners = vec![None; proto.instrs.len()];
    for (index, scope) in plan.scopes.iter().enumerate() {
        for close in &scope.close_points {
            let Some(&close_block) = cfg.instr_to_block.get(close.index()) else {
                return Err(StructureError::invalid(format!(
                    "scope cleanup {close} has no CFG block"
                )));
            };
            if scope.entry == close_block {
                let Some(slot) = lexical_owners.get_mut(close.index()) else {
                    return Err(StructureError::invalid(format!(
                        "scope cleanup {close} is outside the instruction arena"
                    )));
                };
                if slot.replace(ScopePlanId(index)).is_some() {
                    return Err(StructureError::invalid(format!(
                        "cleanup {close} has multiple lexical scope owners"
                    )));
                }
            }
        }
    }

    let layout_rank = block_layout_ranks(plan, cfg)?;
    let mut scope_groups = BTreeMap::<Vec<InstrRef>, Vec<InstrRef>>::new();
    for (&close, origins) in explicit_tbc_close_origins {
        if explicit_tbc_loop_owner(proto, cfg, plan, close, origins).is_none() {
            scope_groups
                .entry(origins.iter().copied().collect())
                .or_default()
                .push(close);
        }
    }
    let mut tbc_scopes = Vec::with_capacity(scope_groups.len());
    let mut tbc_scope_by_close = vec![None; proto.instrs.len()];
    for (origins, mut closes) in scope_groups {
        closes.sort_by_key(|close| {
            let block = cfg.instr_to_block[close.index()];
            (layout_rank[block.index()], close.index())
        });
        let boundary = closes[0];
        let id = TbcScopePlanId(tbc_scopes.len());
        for close in &closes {
            tbc_scope_by_close[close.index()] = Some((id, *close == boundary));
        }
        tbc_scopes.push(TbcScopePlan {
            origins,
            boundary,
            exits: closes
                .into_iter()
                .filter(|close| *close != boundary)
                .collect(),
        });
    }

    let mut dispositions = vec![None; proto.instrs.len()];
    for block in cfg.block_order.iter().copied() {
        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            let instr_ref = InstrRef(instr_index);
            let reachable = cfg.reachable_blocks.contains(&block);
            dispositions[instr_index] = match &proto.instrs[instr_index] {
                LowInstr::Close(_) | LowInstr::Tbc(_) if !reachable => {
                    Some(CleanupDisposition::Unreachable)
                }
                LowInstr::Tbc(_) => Some(CleanupDisposition::ExplicitTbc),
                LowInstr::Close(_) if explicit_tbc_close_origins.contains_key(&instr_ref) => {
                    let origins = explicit_tbc_close_origins.get(&instr_ref).ok_or_else(|| {
                        StructureError::invalid(format!(
                            "cleanup {instr_ref} lost its explicit TBC origins"
                        ))
                    })?;
                    Some(
                        if let Some(region) =
                            explicit_tbc_loop_owner(proto, cfg, plan, instr_ref, origins)
                        {
                            CleanupDisposition::LoopTbcBoundary(region)
                        } else {
                            let (scope, boundary) =
                                tbc_scope_by_close[instr_index].ok_or_else(|| {
                                    StructureError::invalid(format!(
                                        "cleanup {instr_ref} has no explicit TBC scope owner"
                                    ))
                                })?;
                            if boundary {
                                CleanupDisposition::ExplicitTbcBoundary(scope)
                            } else {
                                CleanupDisposition::ExplicitTbcExit(scope)
                            }
                        },
                    )
                }
                LowInstr::Close(_) => {
                    let owner = lexical_owners
                        .get(instr_index)
                        .copied()
                        .flatten()
                        .ok_or_else(|| {
                            StructureError::invalid(format!(
                                "reachable cleanup {instr_ref} has no lexical scope owner"
                            ))
                        })?;
                    Some(CleanupDisposition::LexicalScope(owner))
                }
                _ => None,
            };
        }
    }
    validate_cleanup_dispositions(
        proto,
        cfg,
        plan,
        explicit_tbc_close_origins,
        &dispositions,
        &tbc_scopes,
    )?;
    Ok((dispositions, tbc_scopes))
}

/// 把 label 相对入口 cleanup 的位置冻结进最终计划。
///
/// TBC join 的 must-active 集合可能为空，但某条入边仍携带活跃声明，并由目标 block
/// 开头的 `Close` 归一化。label 若放在该 Close 前面，HIR 词法化后会错误地落进
/// `<close>` local 的作用域；因此只允许它越过连续、已有唯一 owner 的 boundary。
pub(super) fn finalize_label_placements(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let flow = analyze_tbc_flow(proto, cfg);
    let mut finalized = Vec::with_capacity(plan.labels.len());
    for label in &plan.labels {
        let range = cfg
            .blocks
            .get(label.block.index())
            .ok_or_else(|| StructureError::invalid("label block is outside the CFG arena"))?
            .instrs;
        let mut barriers = flow
            .active_at_entry(label.block)
            .ok_or_else(|| StructureError::invalid("label block has no TBC entry facts"))?
            .clone();
        let mut placement = label.placement;
        if placement == LabelPlacement::BeforeBlock {
            for instr_index in range.start.index()..range.end() {
                let instr_ref = InstrRef(instr_index);
                let Some(CleanupDisposition::ExplicitTbcBoundary(scope_id)) =
                    plan.cleanup_disposition(instr_ref)
                else {
                    break;
                };
                if !matches!(proto.instrs.get(instr_index), Some(LowInstr::Close(_))) {
                    return Err(StructureError::invalid(format!(
                        "label cleanup boundary {instr_ref} is not a Close instruction"
                    )));
                }
                let scope = plan.tbc_scope(scope_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "label cleanup boundary {instr_ref} references missing TBC scope"
                    ))
                })?;
                for origin in &scope.origins {
                    barriers.remove(origin);
                }
                placement = LabelPlacement::AfterCleanup(instr_ref);
            }
        }
        finalized.push((barriers.into_iter().collect::<Vec<_>>(), placement));
    }
    for (label, (barriers, placement)) in plan.labels.iter_mut().zip(finalized) {
        label.tbc_barriers = barriers;
        label.placement = placement;
    }
    Ok(())
}

fn block_layout_ranks(plan: &StructurePlan, cfg: &Cfg) -> Result<Vec<usize>, StructureError> {
    enum Work {
        Region(RegionId),
        Block(BlockRef),
    }

    let mut ranks = vec![usize::MAX; cfg.blocks.len()];
    let mut next = 0usize;
    let mut stack = vec![Work::Region(plan.root())];
    while let Some(work) = stack.pop() {
        let block = match work {
            Work::Block(block) => Some(block),
            Work::Region(region) => {
                let node = plan.region(region).ok_or_else(|| {
                    StructureError::invalid("TBC layout references a missing region")
                })?;
                match node {
                    RegionPlan::Block { block, .. } => Some(*block),
                    RegionPlan::Sequence { children, .. } => {
                        stack.extend(children.iter().rev().copied().map(Work::Region));
                        None
                    }
                    RegionPlan::Branch {
                        condition,
                        then_arm,
                        else_arm,
                        ..
                    } => {
                        if let Some(else_arm) = else_arm {
                            stack.push(Work::Region(*else_arm));
                        }
                        stack.push(Work::Region(*then_arm));
                        stack.push(Work::Region(*condition));
                        None
                    }
                    RegionPlan::ValueDecision { plan: decision, .. } => {
                        let decision = plan.value_decision(*decision).ok_or_else(|| {
                            StructureError::invalid(
                                "TBC layout references a missing value decision",
                            )
                        })?;
                        stack.extend(decision.blocks.iter().rev().copied().map(Work::Block));
                        None
                    }
                    RegionPlan::Loop {
                        preheader,
                        control,
                        body,
                        normal_tail,
                        ..
                    } => {
                        if let Some(normal_tail) = normal_tail {
                            stack.push(Work::Region(*normal_tail));
                        }
                        stack.push(Work::Region(*body));
                        stack.push(Work::Region(*control));
                        if let Some(preheader) = preheader {
                            stack.push(Work::Region(*preheader));
                        }
                        None
                    }
                    RegionPlan::Unstructured { layout, .. } => {
                        for item in layout.iter().rev() {
                            stack.push(match item {
                                super::plan::UnstructuredLayoutItem::Block(block) => {
                                    Work::Block(*block)
                                }
                                super::plan::UnstructuredLayoutItem::Region(region) => {
                                    Work::Region(*region)
                                }
                            });
                        }
                        None
                    }
                }
            }
        };
        if let Some(block) = block {
            let slot = ranks.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid("TBC layout block is outside the CFG arena")
            })?;
            if *slot == usize::MAX {
                *slot = next;
                next += 1;
            }
        }
    }
    Ok(ranks)
}

fn validate_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    explicit_tbc_close_origins: &BTreeMap<InstrRef, BTreeSet<InstrRef>>,
    dispositions: &[Option<CleanupDisposition>],
    tbc_scopes: &[TbcScopePlan],
) -> Result<(), StructureError> {
    if dispositions.len() != proto.instrs.len() {
        return Err(StructureError::invalid(format!(
            "cleanup arena has {} slots for {} instructions",
            dispositions.len(),
            proto.instrs.len()
        )));
    }
    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        let Some(&block) = cfg.instr_to_block.get(instr_index) else {
            return Err(StructureError::invalid(format!(
                "instruction @{instr_index} has no CFG block"
            )));
        };
        let disposition = dispositions[instr_index];
        match (instr, disposition) {
            (LowInstr::Close(_) | LowInstr::Tbc(_), Some(CleanupDisposition::Unreachable)) => {
                if cfg.reachable_blocks.contains(&block) {
                    return Err(StructureError::invalid(format!(
                        "reachable cleanup @{instr_index} is marked unreachable"
                    )));
                }
            }
            (LowInstr::Tbc(_), Some(CleanupDisposition::ExplicitTbc)) => {
                if !cfg.reachable_blocks.contains(&block) {
                    return Err(StructureError::invalid(format!(
                        "unreachable TBC @{instr_index} is marked explicit"
                    )));
                }
            }
            (LowInstr::Close(_), Some(CleanupDisposition::LoopTbcBoundary(region))) => {
                let instr_ref = InstrRef(instr_index);
                let Some(origins) = explicit_tbc_close_origins.get(&instr_ref) else {
                    return Err(StructureError::invalid(format!(
                        "loop-owned cleanup @{instr_index} has no explicit TBC origins"
                    )));
                };
                if !cfg.reachable_blocks.contains(&block)
                    || explicit_tbc_loop_owner(proto, cfg, plan, instr_ref, origins) != Some(region)
                {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} does not belong to loop region {}",
                        region.index()
                    )));
                }
            }
            (
                LowInstr::Close(_),
                Some(
                    CleanupDisposition::ExplicitTbcBoundary(scope_id)
                    | CleanupDisposition::ExplicitTbcExit(scope_id),
                ),
            ) => {
                let Some(scope) = tbc_scopes.get(scope_id.index()) else {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} references a missing TBC scope"
                    )));
                };
                let instr_ref = InstrRef(instr_index);
                let role_matches = match disposition {
                    Some(CleanupDisposition::ExplicitTbcBoundary(_)) => scope.boundary == instr_ref,
                    Some(CleanupDisposition::ExplicitTbcExit(_)) => {
                        scope.exits.contains(&instr_ref)
                    }
                    _ => false,
                };
                if !cfg.reachable_blocks.contains(&block)
                    || explicit_tbc_close_origins
                        .get(&instr_ref)
                        .is_none_or(|origins| {
                            !origins.iter().copied().eq(scope.origins.iter().copied())
                        })
                    || !role_matches
                {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} has a stale explicit TBC scope owner"
                    )));
                }
            }
            (LowInstr::Close(_), Some(CleanupDisposition::LexicalScope(id))) => {
                let Some(owner) = plan.scope(id) else {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} refers to missing scope {}",
                        id.index()
                    )));
                };
                if owner.entry != block || !owner.close_points.contains(&InstrRef(instr_index)) {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} is outside lexical scope {}",
                        id.index()
                    )));
                }
            }
            (LowInstr::Close(_) | LowInstr::Tbc(_), _) => {
                return Err(StructureError::invalid(format!(
                    "cleanup @{instr_index} has no matching disposition"
                )));
            }
            (_, None) => {}
            (_, Some(_)) => {
                return Err(StructureError::invalid(format!(
                    "non-cleanup @{instr_index} has a cleanup disposition"
                )));
            }
        }
    }
    Ok(())
}

pub(super) fn analyze_tbc_flow(proto: &LoweredProto, cfg: &Cfg) -> TbcFlowFacts {
    if !proto
        .instrs
        .iter()
        .any(|instr| matches!(instr, LowInstr::Tbc(_)))
    {
        return TbcFlowFacts {
            active_in: vec![BTreeSet::new(); cfg.blocks.len()],
            active_out: vec![BTreeSet::new(); cfg.blocks.len()],
            close_origins: BTreeMap::new(),
        };
    }

    let mut active_by_reg_out =
        vec![BTreeMap::<usize, BTreeSet<InstrRef>>::new(); cfg.blocks.len()];
    let mut close_points = BTreeMap::new();
    let mut pending = VecDeque::from(cfg.block_order.clone());
    let mut queued = vec![true; cfg.blocks.len()];

    while let Some(block) = pending.pop_front() {
        queued[block.index()] = false;
        if !cfg.reachable_blocks.contains(&block) || block == cfg.exit_block {
            continue;
        }

        let mut active = BTreeMap::<usize, BTreeSet<InstrRef>>::new();
        for predecessor in cfg.preds[block.index()]
            .iter()
            .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        {
            for (reg, origins) in &active_by_reg_out[predecessor.index()] {
                active.entry(*reg).or_default().extend(origins);
            }
        }
        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            match &proto.instrs[instr_index] {
                LowInstr::Tbc(tbc) => {
                    active.insert(tbc.reg.index(), BTreeSet::from([InstrRef(instr_index)]));
                }
                LowInstr::Close(close) => {
                    let covered = active
                        .range(close.from.index()..)
                        .flat_map(|(_, origins)| origins.iter().copied())
                        .collect::<BTreeSet<_>>();
                    if !covered.is_empty() {
                        close_points
                            .entry(InstrRef(instr_index))
                            .or_insert_with(BTreeSet::new)
                            .extend(covered);
                    }
                    active.retain(|reg, _| *reg < close.from.index());
                }
                _ => {}
            }
        }

        if active == active_by_reg_out[block.index()] {
            continue;
        }
        active_by_reg_out[block.index()] = active;
        for edge_ref in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge_ref.index()].to;
            if !queued[successor.index()] {
                queued[successor.index()] = true;
                pending.push_back(successor);
            }
        }
    }

    let (active_in, active_out) = analyze_definite_tbc_flow(proto, cfg);
    TbcFlowFacts {
        active_in,
        active_out,
        close_origins: close_points,
    }
}

/// label 的词法 barrier 是“所有到达路径都已进入”的 TBC scope，而不是任一路径上
/// 可能活跃的 scope。may-active 仍用于 Close origin 归属；这里单独做 must 分析，避免
/// join block 把合法的外部 goto 错判成跳进局部作用域。
fn analyze_definite_tbc_flow(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> (Vec<BTreeSet<InstrRef>>, Vec<BTreeSet<InstrRef>>) {
    let origin_regs = proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instr)| match instr {
            LowInstr::Tbc(tbc) => Some((InstrRef(index), tbc.reg.index())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let universe = origin_regs.keys().copied().collect::<BTreeSet<_>>();
    let mut active_in = vec![BTreeSet::new(); cfg.blocks.len()];
    let mut active_out = vec![universe; cfg.blocks.len()];
    let mut pending = VecDeque::from(cfg.block_order.clone());
    let mut queued = vec![true; cfg.blocks.len()];

    while let Some(block) = pending.pop_front() {
        queued[block.index()] = false;
        if !cfg.reachable_blocks.contains(&block) || block == cfg.exit_block {
            active_out[block.index()].clear();
            continue;
        }

        let reachable_predecessors = cfg.preds[block.index()]
            .iter()
            .map(|edge| cfg.edges[edge.index()].from)
            .filter(|pred| cfg.reachable_blocks.contains(pred))
            .collect::<Vec<_>>();
        let mut active = if block == cfg.entry_block || reachable_predecessors.is_empty() {
            BTreeSet::new()
        } else {
            let mut predecessors = reachable_predecessors.into_iter();
            let first = predecessors
                .next()
                .map(|pred| active_out[pred.index()].clone())
                .unwrap_or_default();
            predecessors.fold(first, |mut intersection, pred| {
                intersection.retain(|origin| active_out[pred.index()].contains(origin));
                intersection
            })
        };
        active_in[block.index()] = active.clone();

        let range = cfg.blocks[block.index()].instrs;
        for instr_index in range.start.index()..range.end() {
            match &proto.instrs[instr_index] {
                LowInstr::Tbc(tbc) => {
                    let reg = tbc.reg.index();
                    active.retain(|origin| origin_regs.get(origin).copied() != Some(reg));
                    active.insert(InstrRef(instr_index));
                }
                LowInstr::Close(close) => {
                    active.retain(|origin| {
                        origin_regs
                            .get(origin)
                            .is_some_and(|reg| *reg < close.from.index())
                    });
                }
                _ => {}
            }
        }
        if active == active_out[block.index()] {
            continue;
        }
        active_out[block.index()] = active;
        for edge in &cfg.succs[block.index()] {
            let successor = cfg.edges[edge.index()].to;
            if !queued[successor.index()] {
                queued[successor.index()] = true;
                pending.push_back(successor);
            }
        }
    }

    (active_in, active_out)
}

pub(super) fn validate_label_tbc_barriers(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let flow = analyze_tbc_flow(proto, cfg);
    for (id, label) in plan.labels() {
        let mut expected = flow.active_at_entry(label.block).cloned().ok_or_else(|| {
            StructureError::invalid(format!(
                "label #{} target {} has no TBC entry facts",
                id.index(),
                label.block
            ))
        })?;
        if let LabelPlacement::AfterCleanup(last) = label.placement {
            let range = cfg
                .blocks
                .get(label.block.index())
                .ok_or_else(|| StructureError::invalid("label block is outside the CFG arena"))?
                .instrs;
            if last.index() < range.start.index() || last.index() >= range.end() {
                return Err(StructureError::invalid(format!(
                    "label #{} cleanup placement is outside its target block",
                    id.index()
                )));
            }
            for instr_index in range.start.index()..=last.index() {
                let instr_ref = InstrRef(instr_index);
                let Some(CleanupDisposition::ExplicitTbcBoundary(scope_id)) =
                    plan.cleanup_disposition(instr_ref)
                else {
                    return Err(StructureError::invalid(format!(
                        "label #{} crosses a non-boundary instruction",
                        id.index()
                    )));
                };
                let scope = plan.tbc_scope(scope_id).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "label #{} references a missing TBC boundary owner",
                        id.index()
                    ))
                })?;
                for origin in &scope.origins {
                    expected.remove(origin);
                }
            }
        }
        if !label
            .tbc_barriers
            .iter()
            .copied()
            .eq(expected.iter().copied())
        {
            return Err(StructureError::invalid(format!(
                "label #{} has stale TBC entry barriers",
                id.index()
            )));
        }
    }

    for edge_plan in &plan.edge_plans {
        let super::plan::EdgeTransfer::Goto(label_id, _) = edge_plan.transfer else {
            continue;
        };
        let label = plan.label(label_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "goto edge {} references missing label #{}",
                edge_plan.edge,
                label_id.index()
            ))
        })?;
        let source = cfg
            .edges
            .get(edge_plan.edge.index())
            .map(|edge| edge.from)
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "goto edge {} has a stale source route",
                    edge_plan.edge
                ))
            })?;
        let active = flow.active_after_block(source).ok_or_else(|| {
            StructureError::invalid(format!(
                "goto edge {} source {source} has no TBC exit facts",
                edge_plan.edge
            ))
        })?;
        if label
            .tbc_barriers
            .iter()
            .any(|barrier| !active.contains(barrier))
        {
            return Err(StructureError::invalid(format!(
                "goto edge {} enters the TBC scope of label #{}",
                edge_plan.edge,
                label_id.index()
            )));
        }
    }
    Ok(())
}

fn explicit_tbc_loop_owner(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    close_instr: InstrRef,
    covered_tbc_instrs: &BTreeSet<InstrRef>,
) -> Option<RegionId> {
    let close_block = *cfg.instr_to_block.get(close_instr.index())?;
    let LowInstr::Close(close) = proto.instrs.get(close_instr.index())? else {
        return None;
    };

    // 从声明所在的 leaf region 向外找，天然按最终 containment 的“最内层优先”顺序
    // 消解 owner；不再为每个 cleanup 扫描全部 loop candidates。
    let first_tbc = covered_tbc_instrs.first()?;
    let first_block = *cfg.instr_to_block.get(first_tbc.index())?;
    let mut region = plan.region_for_block(first_block);
    while let Some(region_id) = region {
        let region_plan = plan.region(region_id)?;
        if let RegionPlan::Loop {
            plan: loop_id,
            preheader,
            control,
            body,
            ..
        } = region_plan
        {
            let candidate = plan.loop_(*loop_id)?;
            if loop_tbc_base_is_owned(proto, cfg, candidate, close.from)
                && covered_tbc_instrs.iter().all(|tbc| {
                    cfg.instr_to_block.get(tbc.index()).is_some_and(|block| {
                        loop_iteration_scope_contains(plan, candidate, *control, *body, *block)
                    })
                })
                && loop_tbc_boundary_location_is_owned(
                    &LoopTbcOwnershipContext {
                        proto,
                        cfg,
                        plan,
                        candidate,
                        loop_region: region_id,
                        preheader: *preheader,
                        control: *control,
                        body: *body,
                    },
                    close_block,
                    close_instr,
                )
            {
                return Some(region_id);
            }
        }
        region = region_plan.parent();
    }
    None
}

fn loop_tbc_base_is_owned(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &LoopPlanData,
    close_from: Reg,
) -> bool {
    match candidate.kind {
        super::common::LoopKindHint::NumericForLike
        | super::common::LoopKindHint::GenericForLike => loop_lexical_base(proto, cfg, candidate)
            .is_some_and(|base| close_from.index() >= base.index()),
        // 普通 loop body 每轮同样形成词法域；只要 origin 全部位于最终 loop scope，
        // 且 close 位置通过下面的边界校验，就不能把 VM 展开的 CLOSE 留到 AST。
        super::common::LoopKindHint::WhileLike
        | super::common::LoopKindHint::WhileTrueLike
        | super::common::LoopKindHint::RepeatLike
        | super::common::LoopKindHint::Unknown => true,
    }
}

fn loop_lexical_base(proto: &LoweredProto, cfg: &Cfg, candidate: &LoopPlanData) -> Option<Reg> {
    match candidate.kind {
        super::common::LoopKindHint::NumericForLike => {
            let preheader = candidate.preheader_block?;
            let LowInstr::NumericForInit(init) = cfg.terminator(&proto.instrs, preheader)? else {
                return None;
            };
            Some(init.index)
        }
        super::common::LoopKindHint::GenericForLike => {
            let range = cfg.blocks[candidate.header.index()].instrs;
            (range.start.index()..range.end()).find_map(|index| match proto.instrs[index] {
                LowInstr::GenericForCall(call) => Some(call.iterator),
                _ => None,
            })
        }
        _ => None,
    }
}

struct LoopTbcOwnershipContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    plan: &'a StructurePlan,
    candidate: &'a LoopPlanData,
    loop_region: RegionId,
    preheader: Option<RegionId>,
    control: RegionId,
    body: RegionId,
}

fn loop_tbc_boundary_location_is_owned(
    context: &LoopTbcOwnershipContext<'_>,
    close_block: BlockRef,
    close_instr: InstrRef,
) -> bool {
    let LoopTbcOwnershipContext {
        proto,
        cfg,
        plan,
        candidate,
        loop_region,
        preheader: _,
        control,
        body,
    } = *context;
    if !loop_tbc_boundary_entries_are_owned(context, close_block) {
        return false;
    }

    let range = cfg.blocks[close_block.index()].instrs;
    if block_is_outside_region(plan, loop_region, close_block) {
        return (range.start.index()..close_instr.index())
            .all(|index| matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_)));
    }
    if !loop_iteration_scope_contains(plan, candidate, control, body, close_block)
        || (close_instr.index() + 1..range.end()).any(|index| {
            !matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_))
                && !proto.instrs[index].is_control_terminator()
        })
    {
        return false;
    }
    if candidate.continue_target == Some(close_block)
        || block_is_in_region(plan, control, close_block)
    {
        return true;
    }
    if candidate.kind == super::common::LoopKindHint::RepeatLike
        && cfg.unique_reachable_successor(close_block) == Some(candidate.header)
    {
        return true;
    }
    cfg.unique_reachable_successor(close_block)
        .is_some_and(|successor| block_is_outside_region(plan, loop_region, successor))
}

fn loop_tbc_boundary_entries_are_owned(
    context: &LoopTbcOwnershipContext<'_>,
    close_block: BlockRef,
) -> bool {
    let LoopTbcOwnershipContext {
        proto,
        cfg,
        plan,
        candidate,
        loop_region,
        preheader,
        control,
        body,
    } = *context;
    let mut pending = vec![close_block];
    let mut visited = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if !visited.insert(block) {
            continue;
        }
        for edge_ref in &cfg.preds[block.index()] {
            let predecessor = cfg.edges[edge_ref.index()].from;
            if !cfg.reachable_blocks.contains(&predecessor)
                || loop_iteration_scope_contains(plan, candidate, control, body, predecessor)
                || (candidate.preheader_block == Some(predecessor)
                    && preheader
                        .is_some_and(|region| block_is_in_region(plan, region, predecessor))
                    && matches!(
                        candidate.kind,
                        super::common::LoopKindHint::NumericForLike
                            | super::common::LoopKindHint::GenericForLike
                    ))
            {
                continue;
            }
            if !block_is_outside_region(plan, loop_region, predecessor)
                || cfg.unique_reachable_successor(predecessor) != Some(block)
                || !block_is_cleanup_pad(proto, cfg, predecessor)
            {
                return false;
            }
            pending.push(predecessor);
        }
    }
    true
}

fn loop_iteration_scope_contains(
    plan: &StructurePlan,
    candidate: &LoopPlanData,
    control: RegionId,
    body: RegionId,
    block: BlockRef,
) -> bool {
    block_is_in_region(plan, body, block)
        || candidate.kind == super::common::LoopKindHint::RepeatLike
            && block_is_in_region(plan, control, block)
}

fn block_is_in_region(plan: &StructurePlan, region: RegionId, block: BlockRef) -> bool {
    plan.region_for_block(block)
        .is_some_and(|owner| plan.region_contains(region, owner))
}

fn block_is_outside_region(plan: &StructurePlan, region: RegionId, block: BlockRef) -> bool {
    plan.region_for_block(block)
        .is_none_or(|owner| !plan.region_contains(region, owner))
}

fn block_is_cleanup_pad(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let Some(last) = range.last() else {
        return false;
    };
    (range.start.index()..last.index())
        .all(|index| matches!(proto.instrs[index], LowInstr::Close(_)))
        && matches!(
            proto.instrs[last.index()],
            LowInstr::Close(_) | LowInstr::Jump(_)
        )
}

fn collect_close_points_by_block(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> BTreeMap<BlockRef, Vec<InstrRef>> {
    let mut close_points_by_block = BTreeMap::<BlockRef, Vec<InstrRef>>::new();

    for (instr_index, instr) in proto.instrs.iter().enumerate() {
        if !matches!(instr, LowInstr::Close(_instr)) {
            continue;
        }

        let block = cfg.instr_to_block[instr_index];
        if !cfg.reachable_blocks.contains(&block) {
            continue;
        }

        close_points_by_block
            .entry(block)
            .or_default()
            .push(InstrRef(instr_index));
    }

    close_points_by_block
}

fn immediate_postdom_exit(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BlockRef> {
    graph_facts.post_dominator_tree.parent[block.index()].filter(|exit| *exit != cfg.exit_block)
}
