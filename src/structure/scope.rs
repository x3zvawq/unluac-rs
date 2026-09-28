//! 提取词法 scope 并确定显式 cleanup 的唯一 owner。
//!
//! 消费图、资源及结构候选，向 HIR 发布边界与清理处置。

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ops::Range,
};

use crate::structure::{BlockRef, Cfg, DebugBindingFacts, GraphFacts, StructurePlan};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg};

use super::common::ScopePlan;
use super::plan::{
    CleanupDisposition, LabelPlacement, LoopPlanData, RegionId, RegionPlan, ScopePlanId,
    StructureError,
};

/// 显式 TBC 声明沿 CFG 传播后的 VM 作用域事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TbcFlowFacts {
    // must 用于 label 可见性；may 用于每个真实 cleanup occurrence 的关闭集合。
    active_in: Vec<BTreeSet<InstrRef>>,
    active_out: Vec<BTreeSet<InstrRef>>,
    may_out: Vec<BTreeSet<InstrRef>>,
    close_origins: BTreeMap<InstrRef, BTreeSet<InstrRef>>,
}

impl TbcFlowFacts {
    pub(super) fn close_origins(&self, instr: InstrRef) -> Option<&BTreeSet<InstrRef>> {
        self.close_origins.get(&instr)
    }

    pub(super) fn active_at_entry(&self, block: BlockRef) -> Option<&BTreeSet<InstrRef>> {
        self.active_in.get(block.index())
    }

    pub(super) fn active_after_block(&self, block: BlockRef) -> Option<&BTreeSet<InstrRef>> {
        self.active_out.get(block.index())
    }

    /// 纯清理 pad 已关闭所有 may-active 资源，且每条显式 Close 都关闭调用方所属的 origin。
    /// 调用方另证无 loop owner 和隐式入边；不能用 must-out 为空替代逐路径已清空。
    pub(super) fn fully_closed_local_pad(
        &self,
        proto: &LoweredProto,
        cfg: &Cfg,
        block: BlockRef,
        owns_origin: impl Fn(InstrRef) -> bool,
    ) -> bool {
        if !self.may_out[block.index()].is_empty() || !block_is_cleanup_pad(proto, cfg, block) {
            return false;
        }
        let range = cfg.blocks[block.index()].instrs;
        let mut has_close = false;
        for index in range.start.index()..range.end() {
            let LowInstr::Close(close) = &proto.instrs[index] else {
                continue;
            };
            has_close = true;
            if close.kind != crate::transformer::CloseKind::Explicit
                || self.close_origins(InstrRef(index)).is_none_or(|origins| {
                    origins.is_empty() || !origins.iter().copied().all(&owns_origin)
                })
            {
                return false;
            }
        }
        has_close
    }
}

#[derive(Clone, Copy)]
enum CleanupContinuation {
    Effect,
    End,
    Next(BlockRef),
}

struct CleanupBlock {
    last_effect: Option<usize>,
    tail: CleanupContinuation,
}

#[derive(Clone, Copy)]
struct BranchClose<'a> {
    instr: InstrRef,
    position: usize,
    origins: &'a BTreeSet<InstrRef>,
}

#[derive(Clone, Copy)]
enum CleanupVisit {
    Unknown,
    Active,
    Done(bool),
}

/// Close 身份/origins 来自 TBC flow，范围来自实际 container；不以 header 支配子树
/// 替代成员关系。完整 block 的透明链结果只在一次候选查询内共享。
pub(super) struct BranchCleanupFacts<'a> {
    cfg: &'a Cfg,
    positions: &'a [Option<usize>],
    closes: Vec<BranchClose<'a>>,
    blocks: Vec<CleanupBlock>,
    visits: Vec<CleanupVisit>,
    touched: Vec<BlockRef>,
}

impl<'a> BranchCleanupFacts<'a> {
    pub(super) fn new(
        proto: &LoweredProto,
        cfg: &'a Cfg,
        graph_facts: &'a GraphFacts,
        flow: &'a TbcFlowFacts,
    ) -> Self {
        let positions = &graph_facts.dominator_tree.preorder_index;
        let mut closes = flow
            .close_origins
            .iter()
            .filter_map(|(&instr, origins)| {
                Some(BranchClose {
                    instr,
                    position: positions[cfg.instr_to_block[instr.index()].index()]?,
                    origins,
                })
            })
            .collect::<Vec<_>>();
        closes.sort_unstable_by_key(|close| (close.position, close.instr));
        let block_count = if closes.is_empty() {
            0
        } else {
            cfg.blocks.len()
        };
        let blocks = cfg
            .blocks
            .iter()
            .take(block_count)
            .enumerate()
            .map(|(index, block)| {
                let last_effect =
                    (block.instrs.start.index()..block.instrs.end())
                        .rev()
                        .find(|&index| {
                            !matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Jump(_))
                        });
                let tail = match cfg.succs[index].as_slice() {
                    [] => CleanupContinuation::End,
                    [edge] => CleanupContinuation::Next(cfg.edges[edge.index()].to),
                    _ => CleanupContinuation::Effect,
                };
                CleanupBlock { last_effect, tail }
            })
            .collect();
        Self {
            cfg,
            positions,
            closes,
            blocks,
            visits: vec![CleanupVisit::Unknown; block_count],
            touched: Vec::new(),
        }
    }

    pub(super) fn crosses_cleanup(&mut self, header: BlockRef, ranges: &[Range<usize>]) -> bool {
        let cfg = self.cfg;
        let positions = self.positions;
        let contains = |block: BlockRef| {
            positions[block.index()].is_some_and(|position| {
                let index = ranges.partition_point(|range| range.end <= position);
                ranges
                    .get(index)
                    .is_some_and(|range| range.contains(&position))
            })
        };
        let crosses = 'candidate: {
            for range in ranges {
                let start = self
                    .closes
                    .partition_point(|close| close.position < range.start);
                let end = self
                    .closes
                    .partition_point(|close| close.position < range.end);
                for index in start..end {
                    let close = self.closes[index];
                    let block = cfg.instr_to_block[close.instr.index()];
                    // header prefix 在 If 外原位发射，只有其它 Close 才可能将关闭后的
                    // continuation 隐藏进 arm；origins 仍按真实候选成员关系判断。
                    if block == header
                        || !close.origins.iter().any(|origin| {
                            let owner = cfg.instr_to_block[origin.index()];
                            owner == header || !contains(owner)
                        })
                    {
                        continue;
                    }
                    let facts = &self.blocks[block.index()];
                    if facts
                        .last_effect
                        .is_some_and(|effect| effect > close.instr.index())
                        || self.crosses_continuation(facts.tail, &contains)
                    {
                        break 'candidate true;
                    }
                }
            }
            false
        };
        for block in self.touched.drain(..) {
            self.visits[block.index()] = CleanupVisit::Unknown;
        }
        crosses
    }

    fn crosses_continuation(
        &mut self,
        mut step: CleanupContinuation,
        contains: &impl Fn(BlockRef) -> bool,
    ) -> bool {
        let start = self.touched.len();
        let crosses = loop {
            let block = match step {
                CleanupContinuation::Effect => break true,
                CleanupContinuation::End => break false,
                CleanupContinuation::Next(block) => block,
            };
            if block == self.cfg.exit_block || !contains(block) {
                break false;
            }
            match self.visits[block.index()] {
                CleanupVisit::Done(result) => break result,
                CleanupVisit::Active => break true,
                CleanupVisit::Unknown => {}
            }
            self.visits[block.index()] = CleanupVisit::Active;
            self.touched.push(block);
            let facts = &self.blocks[block.index()];
            step = if facts.last_effect.is_some() {
                CleanupContinuation::Effect
            } else {
                facts.tail
            };
        };
        // 这里只记完整 block 入口的结果，不能把 Close 的中途 suffix 结果写回。
        for block in &self.touched[start..] {
            self.visits[block.index()] = CleanupVisit::Done(crosses);
        }
        crosses
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

pub(super) fn finalize_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    debug_bindings: &DebugBindingFacts,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let mut lexical_owners = vec![None; proto.instrs.len()];
    for (index, scope) in plan.scopes.iter().enumerate() {
        for &close in &scope.close_points {
            if cfg.instr_to_block[close.index()] == scope.entry
                && lexical_owners[close.index()]
                    .replace(ScopePlanId(index))
                    .is_some()
            {
                return Err(StructureError::invalid(
                    "cleanup has multiple lexical scope owners",
                ));
            }
        }
    }
    let mut dispositions = vec![None; proto.instrs.len()];
    for &block in &cfg.block_order {
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            let instr = InstrRef(index);
            dispositions[index] = match &proto.instrs[index] {
                LowInstr::Close(_) | LowInstr::Tbc(_) if !cfg.reachable_blocks.contains(&block) => {
                    Some(CleanupDisposition::Unreachable)
                }
                LowInstr::Tbc(_) => Some(CleanupDisposition::ExplicitTbc),
                LowInstr::Close(_) if plan.tbc_flow.close_origins.contains_key(&instr) => {
                    let origins = &plan.tbc_flow.close_origins[&instr];
                    Some(
                        explicit_tbc_loop_owner(proto, cfg, plan, instr, origins, debug_bindings)
                            .map_or(
                                CleanupDisposition::ExplicitClose,
                                CleanupDisposition::LoopTbcBoundary,
                            ),
                    )
                }
                LowInstr::Close(_) => Some(CleanupDisposition::LexicalScope(
                    lexical_owners[index].ok_or_else(|| {
                        StructureError::invalid(format!(
                            "reachable cleanup {instr} has no lexical scope owner"
                        ))
                    })?,
                )),
                _ => None,
            };
        }
    }
    // 每条 Close 保留独立事件；只有目标的连续显式入口可以移动到所有真实入边。
    // 函数入口没有可代表首次调用的 CFG 入边，loop cleanup 则保留既有 owner。
    let mut syntax_edges = vec![false; cfg.edges.len()];
    for (_, loop_) in plan.loops() {
        if matches!(
            loop_.kind,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) {
            let control = &loop_.control_edges;
            for edge in control
                .preheader_body
                .iter()
                .chain(&control.preheader_exit)
                .chain(&control.body)
                .chain(&control.exit)
                .chain(&control.backedges)
            {
                syntax_edges[edge.index()] = true;
            }
        }
    }
    for &block in &cfg.block_order {
        if block == cfg.entry_block || !cfg.reachable_blocks.contains(&block) {
            continue;
        }
        let range = cfg.blocks[block.index()].instrs;
        let prefix = (range.start.index()..range.end())
            .take_while(|&index| {
                matches!(&proto.instrs[index], LowInstr::Close(close)
                if close.kind == crate::transformer::CloseKind::Explicit)
                    && dispositions[index] == Some(CleanupDisposition::ExplicitClose)
                    && plan
                        .loop_exit_tail_for_cleanup_instr(InstrRef(index))
                        .is_none()
            })
            .collect::<Vec<_>>();
        if prefix.is_empty() {
            continue;
        }
        let incoming = cfg.preds[block.index()]
            .iter()
            .copied()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            .collect::<Vec<_>>();
        if incoming.is_empty() {
            return Err(StructureError::invalid(
                "reachable cleanup block has no incoming edge",
            ));
        }
        // for 的隐式分派边由源码语法及 VM value phases 消费，没有逐边 cleanup 发射点。
        // 必须让整个前缀保留原位；只移动 break 入边会让自然/提前退出重复或漏执行。
        if incoming.iter().any(|edge| syntax_edges[edge.index()]) {
            continue;
        }
        for edge in incoming {
            let mut active = plan.tbc_flow.may_out[cfg.edges[edge.index()].from.index()].clone();
            for &index in &prefix {
                let instr = InstrRef(index);
                let actual = &plan.tbc_flow.close_origins[&instr];
                let origins = active.intersection(actual).copied().collect::<Vec<_>>();
                active.retain(|origin| !actual.contains(origin));
                if !origins.is_empty() {
                    plan.edge_plans[edge.index()]
                        .cleanup
                        .push(super::plan::EdgeCleanupAction { instr, origins });
                }
            }
        }
        for index in prefix {
            dispositions[index] = Some(CleanupDisposition::IncomingEdges);
        }
    }
    plan.cleanup_dispositions = dispositions;
    Ok(())
}

/// 入口事件已在入边执行，label 消费原始 Close 锚点及其 origin，不能从 must 集合反推。
pub(super) fn finalize_label_placements(
    cfg: &Cfg,
    plan: &mut StructurePlan,
) -> Result<(), StructureError> {
    let mut finalized = Vec::with_capacity(plan.labels.len());
    for label in &plan.labels {
        let (last, entry_cleanup) = label_entry_cleanup(cfg, plan, label.block)?;
        let barriers = plan
            .tbc_flow
            .active_at_entry(label.block)
            .ok_or_else(|| StructureError::invalid("label block has no TBC entry facts"))?
            .difference(&entry_cleanup)
            .copied()
            .collect::<Vec<_>>();
        let placement = match (label.placement, last) {
            (LabelPlacement::BeforeBlock, Some(last)) => LabelPlacement::AfterCleanup(last),
            (placement, _) => placement,
        };
        finalized.push((
            barriers,
            placement,
            entry_cleanup.into_iter().collect::<Vec<_>>(),
        ));
    }
    for (label, (barriers, placement, entry_cleanup)) in plan.labels.iter_mut().zip(finalized) {
        label.entry_cleanup = entry_cleanup;
        label.tbc_barriers = barriers;
        label.placement = placement;
    }
    Ok(())
}

fn label_entry_cleanup(
    cfg: &Cfg,
    plan: &StructurePlan,
    block: BlockRef,
) -> Result<(Option<InstrRef>, BTreeSet<InstrRef>), StructureError> {
    let range = cfg
        .blocks
        .get(block.index())
        .ok_or_else(|| StructureError::invalid("label block is outside the CFG arena"))?
        .instrs;
    let mut last = None;
    let mut origins = BTreeSet::new();
    for index in range.start.index()..range.end() {
        let instr = InstrRef(index);
        if plan.cleanup_disposition(instr) != Some(CleanupDisposition::IncomingEdges) {
            break;
        }
        origins.extend(
            plan.tbc_flow
                .close_origins(instr)
                .ok_or_else(|| StructureError::invalid("entry cleanup has no TBC origins"))?,
        );
        last = Some(instr);
    }
    Ok((last, origins))
}

pub(super) fn validate_cleanup_dispositions(
    proto: &LoweredProto,
    cfg: &Cfg,
    debug_bindings: &DebugBindingFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let explicit_tbc_close_origins = &plan.tbc_flow.close_origins;
    let dispositions = &plan.cleanup_dispositions;
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
                    || explicit_tbc_loop_owner(proto, cfg, plan, instr_ref, origins, debug_bindings)
                        != Some(region)
                {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} does not belong to loop region {}",
                        region.index()
                    )));
                }
            }
            (
                LowInstr::Close(_),
                Some(CleanupDisposition::ExplicitClose | CleanupDisposition::IncomingEdges),
            ) => {
                let instr = InstrRef(instr_index);
                let origins = explicit_tbc_close_origins.get(&instr);
                if !cfg.reachable_blocks.contains(&block)
                    || origins.is_none_or(|origins| {
                        explicit_tbc_loop_owner(proto, cfg, plan, instr, origins, debug_bindings)
                            .is_some()
                    })
                {
                    return Err(StructureError::invalid(format!(
                        "cleanup @{instr_index} has stale TBC origins"
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
    validate_entry_cleanups(proto, cfg, plan)
}

fn validate_entry_cleanups(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let mut prefixes = vec![Vec::new(); cfg.blocks.len()];
    for &block in &cfg.block_order {
        let range = cfg.blocks[block.index()].instrs;
        let mut prefix = true;
        for index in range.start.index()..range.end() {
            let instr = InstrRef(index);
            if plan.cleanup_disposition(instr) != Some(CleanupDisposition::IncomingEdges) {
                prefix = false;
                continue;
            }
            if !prefix
                || block == cfg.entry_block
                || !matches!(&proto.instrs[index], LowInstr::Close(close)
                    if close.kind == crate::transformer::CloseKind::Explicit)
                || plan.loop_exit_tail_for_cleanup_instr(instr).is_some()
                || cfg.preds[block.index()]
                    .iter()
                    .all(|edge| !cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            {
                return Err(StructureError::invalid(format!(
                    "cleanup {instr} has no complete explicit-entry ownership"
                )));
            }
            prefixes[block.index()].push(instr);
        }
    }
    for (index, edge) in cfg.edges.iter().enumerate() {
        let mut actions = plan.edge_plans[index].cleanup.iter();
        if cfg.reachable_blocks.contains(&edge.from) {
            let mut active = plan.tbc_flow.may_out[edge.from.index()].clone();
            for &instr in &prefixes[edge.to.index()] {
                let actual = &plan.tbc_flow.close_origins[&instr];
                let origins = active.intersection(actual).copied().collect::<Vec<_>>();
                active.retain(|origin| !actual.contains(origin));
                if !origins.is_empty()
                    && actions
                        .next()
                        .is_none_or(|action| action.instr != instr || action.origins != origins)
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} does not execute its exact entry cleanup {instr}"
                    )));
                }
            }
        }
        if actions.next().is_some() {
            return Err(StructureError::invalid(format!(
                "edge #{index} has an unowned or duplicate entry cleanup"
            )));
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
            may_out: vec![BTreeSet::new(); cfg.blocks.len()],
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
        may_out: active_by_reg_out
            .into_iter()
            .map(|by_reg| by_reg.into_values().flatten().collect())
            .collect(),
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
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let flow = &plan.tbc_flow;
    for (id, label) in plan.labels() {
        let (last, entry_cleanup) = label_entry_cleanup(cfg, plan, label.block)?;
        let expected = flow
            .active_at_entry(label.block)
            .ok_or_else(|| StructureError::invalid("label block has no TBC entry facts"))?
            .difference(&entry_cleanup)
            .copied()
            .collect::<BTreeSet<_>>();
        if matches!(label.placement, LabelPlacement::AfterCleanup(actual) if Some(actual) != last)
            || matches!(label.placement, LabelPlacement::BeforeBlock) && last.is_some()
            || !label
                .entry_cleanup
                .iter()
                .copied()
                .eq(entry_cleanup.iter().copied())
        {
            return Err(StructureError::invalid(format!(
                "label #{} has stale entry cleanup",
                id.index()
            )));
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
    debug_bindings: &DebugBindingFacts,
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
            let context = LoopTbcOwnershipContext {
                proto,
                cfg,
                plan,
                candidate,
                loop_region: region_id,
                preheader: *preheader,
                control: *control,
                body: *body,
                covered_origins: covered_tbc_instrs,
            };
            if loop_tbc_base_is_owned(proto, cfg, candidate, close.from)
                && covered_tbc_instrs.iter().all(|tbc| {
                    cfg.instr_to_block.get(tbc.index()).is_some_and(|block| {
                        loop_iteration_scope_contains(plan, candidate, *control, *body, *block)
                    })
                })
                && loop_tbc_boundary_location_is_owned(&context, close_block, close_instr)
                && loop_tbc_preserves_debug_scopes(&context, close_instr, debug_bindings)
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
    covered_origins: &'a BTreeSet<InstrRef>,
}

fn loop_tbc_preserves_debug_scopes(
    context: &LoopTbcOwnershipContext<'_>,
    close_instr: InstrRef,
    debug_bindings: &DebugBindingFacts,
) -> bool {
    let proto = context.proto;
    let source_end = context
        .covered_origins
        .iter()
        .flat_map(|origin| {
            let LowInstr::Tbc(tbc) = &proto.instrs[origin.index()] else {
                unreachable!("TBC flow origins retain their registration instruction");
            };
            proto.lowering_map.pc_map()[origin.index()]
                .iter()
                .filter_map(move |pc| {
                    proto
                        .debug_locals
                        .source_at(tbc.reg, *pc)
                        .map(|(_, scope)| scope.end_pc)
                })
        })
        .min();
    let Some(source_end) = source_end else {
        return true;
    };
    let LowInstr::Close(close) = &proto.instrs[close_instr.index()] else {
        unreachable!("loop cleanup query only accepts Close");
    };
    // 只查原 frame 的槽位，活动区间由 Transformer 的 source_at 索引回答。
    // Lua54 内层 guard 在 CLOSE 前结束，而同轮外层 copy 在 CLOSE 后才结束；
    // 若交给整个 loop 的隐式 closing，__close 中 copy 会提前不可见。
    // 入口 binding 不会随本轮 scope 消失；Def/Phi 的声明 owner 则直接消费 SSA。
    !proto.lowering_map.pc_map()[close_instr.index()]
        .iter()
        .any(|pc| {
            (0..close.from.index()).any(|reg| {
                let Some((scope, local)) = proto.debug_locals.source_at(Reg(reg), *pc) else {
                    return false;
                };
                local.end_pc > source_end
                    && debug_bindings.for_scope(scope).is_none_or(|fact| {
                        // 未接受或晚起的 Entry scope 不能当作函数入口 binding；缺失证明时保留 Close。
                        fact.declaration_block.map_or(fact.start_pc != 0, |block| {
                            loop_iteration_scope_contains(
                                context.plan,
                                context.candidate,
                                context.control,
                                context.body,
                                block,
                            )
                        })
                    })
            })
        })
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
        covered_origins: _,
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
        covered_origins,
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
                // VM-for 的正常 dispatch 出口已执行 body cleanup；它可以与仍携带资源的
                // break 汇合。只消费这条边确实不再携带的 origins，不能将 control 冒充 body。
                || (block_is_in_region(plan, control, predecessor)
                    && covered_origins.is_disjoint(&plan.tbc_flow.may_out[predecessor.index()]))
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
