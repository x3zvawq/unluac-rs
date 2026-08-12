use std::collections::BTreeSet;

use super::{
    BlockEmissionPlan, BlockTerminatorKind, BranchArm, CleanupDisposition, ConditionArcPolarity,
    ConditionPlan, ConditionPlanId, ConditionTarget, ControlFlowFeature, EdgeActionPlacement,
    EdgeTransfer, ForwardRouteKind, LabelPlacement, LoopPlanId, PhiIncomingDisposition,
    PlanRequirement, RegionId, RegionNavigation, RegionPlan, ScopePlanId, StructureError,
    UnstructuredLayoutItem, ValueDecisionArcPlan, ValueDecisionPlan, ValueDecisionPlanId,
    ValueDecisionTarget,
};
use crate::structure::helpers::shared_pure_terminal_kind;
use crate::structure::{
    BlockKind, BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts, SsaValue, StructurePlan,
};
use crate::transformer::{BranchSubject, InstrRef, LowInstr, LoweredProto};

pub(super) fn validate(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.regions.is_empty() || plan.root.index() >= plan.regions.len() {
        return Err(StructureError::invalid("plan root is missing"));
    }
    if !matches!(
        plan.regions[plan.root.index()],
        RegionPlan::Sequence { parent: None, .. }
    ) {
        return Err(StructureError::invalid(
            "plan root must be a parentless sequence",
        ));
    }
    if plan.region_by_block.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block-to-region index length mismatch",
        ));
    }

    validate_containment(plan)?;
    plan.navigation.validate(cfg, plan)?;
    let intervals = &plan.navigation;
    let edge_regions = &plan.navigation;
    let block_stats = RegionBlockStats::new(plan, intervals)?;
    validate_block_terminators(proto, cfg, plan)?;
    validate_block_coverage(cfg, plan)?;
    validate_region_entries(cfg, plan, intervals)?;
    validate_single_pass_plans(cfg, plan, intervals)?;
    let condition_edges = validate_condition_plans(cfg, plan)?;
    validate_branch_plans(cfg, plan, intervals, &block_stats, &condition_edges)?;
    let loop_edges = validate_loop_plans(proto, cfg, plan, intervals, &block_stats)?;
    validate_labels(cfg, plan)?;
    validate_edges(
        cfg,
        plan,
        intervals,
        edge_regions,
        &condition_edges,
        &loop_edges,
    )?;
    validate_requirements(cfg, plan, intervals)?;
    validate_value_decision_plans(cfg, plan)?;
    Ok(())
}

fn validate_single_pass_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    if plan.single_pass_by_region.len() != plan.regions.len() {
        return Err(StructureError::invalid(
            "single-pass reverse index length mismatch",
        ));
    }
    let mut seen_regions = vec![false; plan.regions.len()];
    for (index, fence) in plan.single_passes.iter().enumerate() {
        if fence.region.index() >= plan.regions.len()
            || std::mem::replace(&mut seen_regions[fence.region.index()], true)
            || plan.single_pass_by_region[fence.region.index()]
                != Some(super::SinglePassPlanId(index))
            || !matches!(
                plan.region(fence.region),
                Some(RegionPlan::Sequence {
                    parent: Some(_),
                    ..
                })
            )
        {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} has a stale region identity"
            )));
        }
        let entry = plan.region_for_block(fence.entry).ok_or_else(|| {
            StructureError::invalid(format!("single-pass payload #{index} entry is unowned"))
        })?;
        let tail = plan.region_for_block(fence.tail).ok_or_else(|| {
            StructureError::invalid(format!("single-pass payload #{index} tail is unowned"))
        })?;
        if !intervals.contains(fence.region, entry)
            || !intervals.contains(fence.region, tail)
            || fence.escape_edges.is_empty()
        {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} is not closed over its entry and tail"
            )));
        }
        let tail_edge = cfg
            .succs
            .get(fence.tail.index())
            .and_then(|edges| match edges.as_slice() {
                [edge] => Some(*edge),
                _ => None,
            })
            .and_then(|edge| cfg.edges.get(edge.index()))
            .ok_or_else(|| {
                StructureError::invalid(format!("single-pass payload #{index} tail is not linear"))
            })?;
        if tail_edge.to != fence.continuation {
            return Err(StructureError::invalid(format!(
                "single-pass payload #{index} tail does not reach its continuation"
            )));
        }
        let mut previous = None;
        for edge_ref in &fence.escape_edges {
            if previous.is_some_and(|previous| previous >= *edge_ref) {
                return Err(StructureError::invalid(format!(
                    "single-pass payload #{index} escape edges are not strictly ordered"
                )));
            }
            previous = Some(*edge_ref);
            let edge = cfg.edges.get(edge_ref.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "single-pass payload #{index} references a missing escape edge"
                ))
            })?;
            let source = plan.region_for_block(edge.from).ok_or_else(|| {
                StructureError::invalid(format!(
                    "single-pass payload #{index} escape source is unowned"
                ))
            })?;
            if edge.from == fence.tail
                || edge.to != fence.continuation
                || !intervals.contains(fence.region, source)
                || plan.edge_plan(*edge_ref).is_none_or(|edge_plan| {
                    edge_plan.owner != fence.region
                        || edge_plan.transfer != EdgeTransfer::Break(fence.region)
                })
            {
                return Err(StructureError::invalid(format!(
                    "single-pass payload #{index} escape edge {edge_ref} is stale: region={:?} entry={} tail={} continuation={} edge={} -> {} plan={:?}",
                    fence.region,
                    fence.entry,
                    fence.tail,
                    fence.continuation,
                    edge.from,
                    edge.to,
                    plan.edge_plan(*edge_ref),
                )));
            }
        }
    }
    for (region, owner) in plan.single_pass_by_region.iter().copied().enumerate() {
        if owner.is_some() != seen_regions[region] {
            return Err(StructureError::invalid(
                "single-pass reverse index has a stale entry",
            ));
        }
    }
    Ok(())
}

/// 证明稠密 terminator arena 与 low-IR/CFG 是同一份物理控制流事实。
///
/// 这里先验证 block range 构成 low-IR 的线性分区，再按 source block 各 claim 一次
/// CFG edge；因此即使输入已经损坏，工作量仍受 `blocks + edges + instructions` 限制。
fn validate_block_terminators(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let block_count = cfg.blocks.len();
    if plan.block_terminators.len() != block_count {
        return Err(StructureError::invalid(
            "block terminator arena length mismatch",
        ));
    }
    if cfg.succs.len() != block_count {
        return Err(StructureError::invalid(
            "CFG block/successor index length mismatch while validating terminators",
        ));
    }
    if cfg.instr_to_block.len() != proto.instrs.len() {
        return Err(StructureError::invalid(
            "CFG instruction-to-block index length mismatch while validating terminators",
        ));
    }

    let mut next_block = vec![None; block_count];
    let mut ordered = vec![false; block_count];
    let mut expected_start = 0usize;
    let mut previous = None;
    for block in cfg.block_order.iter().copied() {
        let basic_block = cfg.blocks.get(block.index()).ok_or_else(|| {
            StructureError::invalid(format!("CFG block order references missing block {block}"))
        })?;
        if basic_block.kind != BlockKind::Normal {
            return Err(StructureError::invalid(format!(
                "CFG block order contains non-normal block {block}"
            )));
        }
        let slot = ordered.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid(format!("CFG block order references missing block {block}"))
        })?;
        if std::mem::replace(slot, true) {
            return Err(StructureError::invalid(format!(
                "CFG block order contains duplicate block {block}"
            )));
        }
        if basic_block.instrs.start.index() != expected_start {
            return Err(StructureError::invalid(format!(
                "CFG block {block} does not start at the end of the preceding block"
            )));
        }
        expected_start = checked_range_end(basic_block.instrs.start, basic_block.instrs.len)?;
        if expected_start > proto.instrs.len() {
            return Err(StructureError::invalid(format!(
                "CFG block {block} instruction range exceeds the low-IR arena"
            )));
        }
        if let Some(previous) = previous {
            next_block[previous] = Some(block);
        }
        previous = Some(block.index());
    }
    if expected_start != proto.instrs.len() {
        return Err(StructureError::invalid(
            "CFG normal block ranges do not cover the low-IR arena",
        ));
    }
    for (index, basic_block) in cfg.blocks.iter().enumerate() {
        let block = BlockRef(index);
        match basic_block.kind {
            BlockKind::Normal if !ordered[index] => {
                return Err(StructureError::invalid(format!(
                    "normal CFG block {block} is missing from block order"
                )));
            }
            BlockKind::SyntheticExit => {
                if ordered[index]
                    || block != cfg.exit_block
                    || !basic_block.instrs.is_empty()
                    || basic_block.instrs.start.index() != proto.instrs.len()
                {
                    return Err(StructureError::invalid(format!(
                        "synthetic exit block {block} has stale identity or instruction range"
                    )));
                }
            }
            BlockKind::Normal => {}
        }
    }
    for (index, block) in cfg.instr_to_block.iter().copied().enumerate() {
        let basic_block = cfg.blocks.get(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "instruction @{index} maps to missing CFG block {block}"
            ))
        })?;
        let end = checked_range_end(basic_block.instrs.start, basic_block.instrs.len)?;
        if basic_block.kind != BlockKind::Normal
            || index < basic_block.instrs.start.index()
            || index >= end
        {
            return Err(StructureError::invalid(format!(
                "instruction @{index} has a stale CFG block mapping"
            )));
        }
    }

    let mut indexed_edges = vec![false; cfg.edges.len()];
    for (index, succs) in cfg.succs.iter().enumerate() {
        let block = BlockRef(index);
        for edge in succs.iter().copied() {
            let candidate = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "block {block} successor index references missing edge {edge}"
                ))
            })?;
            if candidate.from != block {
                return Err(StructureError::invalid(format!(
                    "edge {edge} is indexed under the wrong source block"
                )));
            }
            let slot = indexed_edges.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("CFG references missing edge {edge}"))
            })?;
            if std::mem::replace(slot, true) {
                return Err(StructureError::invalid(format!(
                    "edge {edge} appears multiple times in the CFG successor index"
                )));
            }
        }
    }
    if let Some(index) = indexed_edges.iter().position(|indexed| !indexed) {
        return Err(StructureError::invalid(format!(
            "edge #{index} is missing from the CFG successor index"
        )));
    }

    let mut claimed_edges = vec![false; cfg.edges.len()];
    for (index, terminator) in plan.block_terminators.iter().enumerate() {
        let block = BlockRef(index);
        let basic_block = cfg.blocks.get(index).ok_or_else(|| {
            StructureError::invalid(format!("terminator arena references missing block {block}"))
        })?;
        if terminator.block != block || terminator.instrs != basic_block.instrs {
            return Err(StructureError::invalid(format!(
                "block {block} has a stale terminator identity or instruction range"
            )));
        }

        match (basic_block.kind, terminator.kind) {
            (BlockKind::SyntheticExit, BlockTerminatorKind::SyntheticExit) => {
                if !terminator.instrs.is_empty() || !cfg.succs[index].is_empty() {
                    return Err(StructureError::invalid(format!(
                        "synthetic exit block {block} has instructions or successors"
                    )));
                }
            }
            (BlockKind::SyntheticExit, _)
            | (BlockKind::Normal, BlockTerminatorKind::SyntheticExit) => {
                return Err(StructureError::invalid(format!(
                    "block {block} has a terminator kind that disagrees with its CFG block kind"
                )));
            }
            (BlockKind::Normal, BlockTerminatorKind::Linear { edge }) => {
                if terminator
                    .instrs
                    .last()
                    .and_then(|instr| proto.instrs.get(instr.index()))
                    .is_some_and(LowInstr::is_control_terminator)
                {
                    return Err(StructureError::invalid(format!(
                        "linear block {block} ends in a control terminator"
                    )));
                }
                match (edge, next_block[index]) {
                    (None, None) => {}
                    (Some(edge), Some(target)) => claim_terminator_edge(
                        cfg,
                        &mut claimed_edges,
                        block,
                        edge,
                        EdgeKind::Fallthrough,
                        target,
                    )?,
                    _ => {
                        return Err(StructureError::invalid(format!(
                            "linear block {block} does not match its physical fallthrough"
                        )));
                    }
                }
            }
            (BlockKind::Normal, BlockTerminatorKind::Jump { instr, edge }) => {
                let LowInstr::Jump(raw) = terminator_instr(proto, terminator.instrs, block, instr)?
                else {
                    return Err(StructureError::invalid(format!(
                        "jump terminator in block {block} disagrees with low-IR opcode"
                    )));
                };
                claim_target_edge(
                    cfg,
                    &mut claimed_edges,
                    block,
                    edge,
                    EdgeKind::Jump,
                    raw.target,
                )?;
            }
            (
                BlockKind::Normal,
                BlockTerminatorKind::Branch {
                    instr,
                    truthy,
                    falsy,
                },
            ) => {
                let LowInstr::Branch(raw) =
                    terminator_instr(proto, terminator.instrs, block, instr)?
                else {
                    return Err(StructureError::invalid(format!(
                        "branch terminator in block {block} disagrees with low-IR opcode"
                    )));
                };
                claim_target_edge(
                    cfg,
                    &mut claimed_edges,
                    block,
                    truthy,
                    EdgeKind::BranchTrue,
                    raw.then_target,
                )?;
                claim_target_edge(
                    cfg,
                    &mut claimed_edges,
                    block,
                    falsy,
                    EdgeKind::BranchFalse,
                    raw.else_target,
                )?;
            }
            (BlockKind::Normal, BlockTerminatorKind::Return { instr, edge }) => {
                if !matches!(
                    terminator_instr(proto, terminator.instrs, block, instr)?,
                    LowInstr::Return(_)
                ) {
                    return Err(StructureError::invalid(format!(
                        "return terminator in block {block} disagrees with low-IR opcode"
                    )));
                }
                claim_terminator_edge(
                    cfg,
                    &mut claimed_edges,
                    block,
                    edge,
                    EdgeKind::Return,
                    cfg.exit_block,
                )?;
            }
            (BlockKind::Normal, BlockTerminatorKind::TailCall { instr, edge }) => {
                if !matches!(
                    terminator_instr(proto, terminator.instrs, block, instr)?,
                    LowInstr::TailCall(_)
                ) {
                    return Err(StructureError::invalid(format!(
                        "tail-call terminator in block {block} disagrees with low-IR opcode"
                    )));
                }
                claim_terminator_edge(
                    cfg,
                    &mut claimed_edges,
                    block,
                    edge,
                    EdgeKind::TailCall,
                    cfg.exit_block,
                )?;
            }
            (BlockKind::Normal, BlockTerminatorKind::NumericForInit { instr, body, exit }) => {
                let LowInstr::NumericForInit(raw) =
                    terminator_instr(proto, terminator.instrs, block, instr)?
                else {
                    return Err(StructureError::invalid(format!(
                        "numeric-for init terminator in block {block} disagrees with low-IR opcode"
                    )));
                };
                claim_loop_edges(
                    cfg,
                    &mut claimed_edges,
                    block,
                    body,
                    exit,
                    raw.body_target,
                    raw.exit_target,
                )?;
            }
            (BlockKind::Normal, BlockTerminatorKind::NumericForLoop { instr, body, exit }) => {
                let LowInstr::NumericForLoop(raw) =
                    terminator_instr(proto, terminator.instrs, block, instr)?
                else {
                    return Err(StructureError::invalid(format!(
                        "numeric-for loop terminator in block {block} disagrees with low-IR opcode"
                    )));
                };
                claim_loop_edges(
                    cfg,
                    &mut claimed_edges,
                    block,
                    body,
                    exit,
                    raw.body_target,
                    raw.exit_target,
                )?;
            }
            (BlockKind::Normal, BlockTerminatorKind::GenericForLoop { instr, body, exit }) => {
                let LowInstr::GenericForLoop(raw) =
                    terminator_instr(proto, terminator.instrs, block, instr)?
                else {
                    return Err(StructureError::invalid(format!(
                        "generic-for loop terminator in block {block} disagrees with low-IR opcode"
                    )));
                };
                claim_loop_edges(
                    cfg,
                    &mut claimed_edges,
                    block,
                    body,
                    exit,
                    raw.body_target,
                    raw.exit_target,
                )?;
            }
        }
    }

    if let Some(index) = claimed_edges.iter().position(|claimed| !claimed) {
        return Err(StructureError::invalid(format!(
            "edge #{index} is not covered by its source block terminator"
        )));
    }
    Ok(())
}

fn checked_range_end(start: InstrRef, len: usize) -> Result<usize, StructureError> {
    start
        .index()
        .checked_add(len)
        .ok_or_else(|| StructureError::invalid("CFG instruction range overflows usize"))
}

fn terminator_instr(
    proto: &LoweredProto,
    instrs: crate::structure::InstrRange,
    block: BlockRef,
    instr: InstrRef,
) -> Result<&LowInstr, StructureError> {
    if instrs.last() != Some(instr) {
        return Err(StructureError::invalid(format!(
            "block {block} terminator instruction is not the end of its instruction range"
        )));
    }
    proto.instrs.get(instr.index()).ok_or_else(|| {
        StructureError::invalid(format!(
            "block {block} terminator {instr} is outside the low-IR arena"
        ))
    })
}

fn claim_loop_edges(
    cfg: &Cfg,
    claimed_edges: &mut [bool],
    block: BlockRef,
    body: EdgeRef,
    exit: EdgeRef,
    body_target: InstrRef,
    exit_target: InstrRef,
) -> Result<(), StructureError> {
    claim_target_edge(
        cfg,
        claimed_edges,
        block,
        body,
        EdgeKind::LoopBody,
        body_target,
    )?;
    claim_target_edge(
        cfg,
        claimed_edges,
        block,
        exit,
        EdgeKind::LoopExit,
        exit_target,
    )
}

fn claim_target_edge(
    cfg: &Cfg,
    claimed_edges: &mut [bool],
    block: BlockRef,
    edge: EdgeRef,
    kind: EdgeKind,
    target: InstrRef,
) -> Result<(), StructureError> {
    let target = cfg
        .instr_to_block
        .get(target.index())
        .copied()
        .ok_or_else(|| {
            StructureError::invalid(format!(
                "control terminator in block {block} targets missing instruction {target}"
            ))
        })?;
    claim_terminator_edge(cfg, claimed_edges, block, edge, kind, target)
}

fn claim_terminator_edge(
    cfg: &Cfg,
    claimed_edges: &mut [bool],
    block: BlockRef,
    edge: EdgeRef,
    kind: EdgeKind,
    target: BlockRef,
) -> Result<(), StructureError> {
    if cfg.blocks.get(target.index()).is_none() {
        return Err(StructureError::invalid(format!(
            "terminator in block {block} targets missing block {target}"
        )));
    }
    let candidate = cfg.edges.get(edge.index()).ok_or_else(|| {
        StructureError::invalid(format!(
            "terminator in block {block} references missing edge {edge}"
        ))
    })?;
    if candidate.from != block || candidate.kind != kind || candidate.to != target {
        return Err(StructureError::invalid(format!(
            "terminator in block {block} disagrees with edge {edge} source, kind, or target"
        )));
    }
    let slot = claimed_edges.get_mut(edge.index()).ok_or_else(|| {
        StructureError::invalid(format!(
            "terminator in block {block} references missing edge {edge}"
        ))
    })?;
    if std::mem::replace(slot, true) {
        return Err(StructureError::invalid(format!(
            "edge {edge} is claimed more than once by block terminators"
        )));
    }
    Ok(())
}

fn validate_labels(cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
    if plan.label_by_block.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block-to-label index length mismatch",
        ));
    }

    let mut actual_targets = vec![false; cfg.blocks.len()];
    for (index, label) in plan.labels.iter().enumerate() {
        let id = super::LabelPlanId(index);
        let Some(target) = actual_targets.get_mut(label.block.index()) else {
            return Err(StructureError::invalid(format!(
                "label #{index} references a missing block"
            )));
        };
        if !cfg.reachable_blocks.contains(&label.block)
            || plan.label_for_block(label.block) != Some(id)
            || std::mem::replace(target, true)
        {
            return Err(StructureError::invalid(format!(
                "label #{index} has a stale block reverse index"
            )));
        }
        if label.tbc_barriers.windows(2).any(|pair| pair[0] >= pair[1])
            || label
                .tbc_barriers
                .iter()
                .any(|instr| instr.index() >= cfg.instr_to_block.len())
        {
            return Err(StructureError::invalid(format!(
                "label #{index} has a non-canonical TBC barrier set"
            )));
        }
    }
    for (index, label) in plan.label_by_block.iter().copied().enumerate() {
        let Some(label) = label else {
            continue;
        };
        if plan.label(label).map(|label| label.block) != Some(crate::structure::BlockRef(index)) {
            return Err(StructureError::invalid(format!(
                "block #{index} has a stale label reverse index"
            )));
        }
    }

    let label_region_by_block = label_regions_by_entry(cfg, plan)?;
    let mut expected_placements = vec![None; cfg.blocks.len()];
    for edge_plan in &plan.edge_plans {
        if !matches!(edge_plan.transfer, EdgeTransfer::Goto(_, _)) {
            continue;
        }
        let edge = cfg.edges.get(edge_plan.edge.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "goto edge {} is outside the CFG arena",
                edge_plan.edge
            ))
        })?;
        record_expected_label_placement(
            &mut expected_placements,
            edge.to,
            expected_label_placement_for_edge(
                cfg,
                &label_region_by_block,
                edge_plan.edge,
                edge.to,
            )?,
        )?;
    }
    let multi_entry_prefix = plan.navigation.multi_entry_island_prefix(&plan.regions);
    for (index, edge) in cfg.edges.iter().enumerate() {
        if plan
            .navigation
            .edge_enters_prefixed_region(EdgeRef(index), &multi_entry_prefix)
        {
            let edge_ref = EdgeRef(index);
            record_expected_label_placement(
                &mut expected_placements,
                edge.to,
                expected_label_placement_for_edge(cfg, &label_region_by_block, edge_ref, edge.to)?,
            )?;
        }
    }
    for (index, expected) in expected_placements.iter().copied().enumerate() {
        let block = BlockRef(index);
        let actual = plan
            .label_for_block(block)
            .and_then(|label| plan.label(label))
            .map(|label| match label.placement {
                LabelPlacement::AfterCleanup(_) => LabelPlacement::BeforeBlock,
                placement => placement,
            });
        if actual != expected {
            return Err(StructureError::invalid(format!(
                "label target {block} has placement {actual:?}; expected {expected:?}"
            )));
        }
    }
    Ok(())
}

fn label_regions_by_entry(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<Vec<Option<RegionId>>, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    for (index, node) in plan.regions.iter().enumerate() {
        let region = RegionId(index);
        let entry = match node {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => *entry,
            RegionPlan::Sequence { .. } => {
                let Some((_, fence)) = plan.single_pass_for_region(region) else {
                    continue;
                };
                fence.entry
            }
            RegionPlan::Block { .. } | RegionPlan::Unstructured { .. } => continue,
        };
        let slot = by_block.get_mut(entry.index()).ok_or_else(|| {
            StructureError::invalid("structured label entry is outside the CFG arena")
        })?;
        match *slot {
            None => *slot = Some(region),
            Some(outer) if plan.navigation.contains(outer, region) => {}
            Some(inner) if plan.navigation.contains(region, inner) => *slot = Some(region),
            Some(other) => {
                return Err(StructureError::invalid(format!(
                    "block {entry} is the entry of incomparable structured regions #{} and #{}",
                    other.index(),
                    region.index()
                )));
            }
        }
    }
    Ok(by_block)
}

fn record_expected_label_placement(
    placements: &mut [Option<LabelPlacement>],
    block: BlockRef,
    placement: LabelPlacement,
) -> Result<(), StructureError> {
    let slot = placements.get_mut(block.index()).ok_or_else(|| {
        StructureError::invalid(format!("label target {block} is outside the CFG arena"))
    })?;
    if let Some(existing) = slot.replace(placement)
        && existing != placement
    {
        return Err(StructureError::invalid(format!(
            "label target {block} requires conflicting placements {existing:?} and {placement:?}"
        )));
    }
    Ok(())
}

fn expected_label_placement_for_edge(
    cfg: &Cfg,
    label_region_by_block: &[Option<RegionId>],
    edge: EdgeRef,
    target: BlockRef,
) -> Result<LabelPlacement, StructureError> {
    if cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(target) {
        return Err(StructureError::invalid(format!(
            "label edge {edge} does not enter target {target}"
        )));
    }
    Ok(label_region_by_block
        .get(target.index())
        .copied()
        .flatten()
        .map_or(LabelPlacement::BeforeBlock, LabelPlacement::BeforeRegion))
}

pub(super) fn validate_final(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    validate(proto, cfg, plan)?;
    crate::structure::scope::validate_label_tbc_barriers(proto, cfg, plan)?;
    validate_condition_predicates(proto, plan)?;
    validate_condition_prefix_placements(proto, cfg, plan)?;
    validate_cleanup(proto, cfg, plan)?;
    validate_phis(cfg, dataflow, plan)?;
    validate_block_emissions(cfg, plan)?;
    super::loop_protocol::validate(proto, cfg, graph_facts, dataflow, plan)?;
    validate_condition_values(proto, cfg, dataflow, plan)?;
    validate_value_decision_values(proto, cfg, dataflow, plan)?;
    Ok(())
}

fn validate_block_emissions(cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
    if plan.block_emissions.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block emission arena length mismatch",
        ));
    }
    for index in 0..cfg.blocks.len() {
        let block = BlockRef(index);
        let expected = super::expected_block_emission(cfg, plan, block)?;
        let actual = plan.block_emissions[index];
        if actual != expected {
            return Err(StructureError::invalid(format!(
                "block {block} emission is stale: actual={actual:?}, expected={expected:?}"
            )));
        }
        if matches!(actual, BlockEmissionPlan::ForwardedControl { .. })
            && plan.label_for_block(block).is_some()
        {
            return Err(StructureError::invalid(format!(
                "forwarded block {block} owns a planned label"
            )));
        }
    }
    Ok(())
}

fn validate_condition_predicates(
    proto: &LoweredProto,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    for (condition_index, condition) in plan.conditions.iter().enumerate() {
        for (node_index, node) in condition.nodes.iter().enumerate() {
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} predicate is not a branch"
                )));
            };
            if node.predicate_negated != branch.cond.negated {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} has stale predicate polarity"
                )));
            }
        }
    }
    Ok(())
}

fn validate_condition_values(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    let mut owner_by_condition = vec![None; plan.conditions.len()];
    for (region, region_plan) in plan.regions() {
        let condition = match region_plan {
            RegionPlan::Branch { plan: branch, .. } => Some(
                plan.branch(*branch)
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "condition value owner has a missing branch payload",
                        )
                    })?
                    .condition,
            ),
            RegionPlan::Loop { plan: loop_, .. } => {
                plan.loop_(*loop_)
                    .ok_or_else(|| {
                        StructureError::invalid("condition value owner has a missing loop payload")
                    })?
                    .condition
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::ValueDecision { .. }
            | RegionPlan::Unstructured { .. } => None,
        };
        let Some(condition) = condition else {
            continue;
        };
        let slot = owner_by_condition
            .get_mut(condition.index())
            .ok_or_else(|| {
                StructureError::invalid("region references a missing condition value payload")
            })?;
        if slot
            .replace(region)
            .is_some_and(|existing| existing != region)
        {
            return Err(StructureError::invalid(
                "condition value payload has multiple region owners",
            ));
        }
    }

    for (condition_index, condition) in plan.conditions.iter().enumerate() {
        let condition_id = super::ConditionPlanId(condition_index);
        for node in &condition.nodes {
            let Some(value) = node.materialized_value else {
                continue;
            };
            let owner = owner_by_condition[condition_index].ok_or_else(|| {
                StructureError::invalid("condition value payload has no owning region")
            })?;
            if plan.condition_value_owner(value.phi) != Some((condition_id, node.id)) {
                return Err(StructureError::invalid(
                    "condition value has a stale reverse owner",
                ));
            }
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(
                    "condition value predicate is not a branch",
                ));
            };
            if !matches!(branch.cond.subject, BranchSubject::Compare { .. }) {
                return Err(StructureError::invalid(
                    "condition value predicate does not produce a boolean",
                ));
            }
            let consumer = condition.nodes.get(value.consumer.index()).ok_or_else(|| {
                StructureError::invalid("condition value references a missing consumer")
            })?;
            let phi = dataflow.phi_candidate(value.phi).ok_or_else(|| {
                StructureError::invalid("condition value references a missing phi")
            })?;
            let uses = dataflow.phi_uses.get(value.phi.index()).map(Vec::as_slice);
            if phi.block != consumer.block
                || phi.incoming.len() != 2
                || uses
                    != Some(&[crate::structure::UseSite {
                        instr: value.use_instr,
                        reg: phi.reg,
                    }])
                || cfg.instr_to_block.get(value.use_instr.index()).copied() != Some(consumer.block)
            {
                return Err(StructureError::invalid(
                    "condition value phi has stale use ownership",
                ));
            }
            if phi.incoming.iter().enumerate().any(|(index, incoming)| {
                !matches!(
                    plan.phi_plan(phi.id)
                        .and_then(|plan| plan.incomings.get(index))
                        .map(|incoming| incoming.disposition),
                    Some(PhiIncomingDisposition::RegionResult(region)) if region == owner
                ) || incoming.edge.is_none()
            }) {
                return Err(StructureError::invalid(
                    "condition value phi is not owned by its region",
                ));
            }

            let bool_for_arc = |truthy: bool| -> Option<bool> {
                let polarity = match truthy ^ node.predicate_negated {
                    true => ConditionArcPolarity::BranchTrue,
                    false => ConditionArcPolarity::BranchFalse,
                };
                let arc = node.arc(polarity);
                let edge = arc.route.last().copied()?;
                let incoming = phi
                    .incoming
                    .iter()
                    .find(|incoming| incoming.edge == Some(edge))?;
                let crate::structure::SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                let instr = dataflow.def_instr(def);
                let LowInstr::LoadBool(load) = proto.instrs.get(instr.index())? else {
                    return None;
                };
                arc.connector_blocks
                    .contains(&dataflow.def_block(def))
                    .then_some(load.value)
            };
            let (Some(raw_truthy), Some(raw_falsy)) = (bool_for_arc(true), bool_for_arc(false))
            else {
                return Err(StructureError::invalid(
                    "condition value routes do not materialize booleans",
                ));
            };
            if raw_truthy == raw_falsy || value.negated == raw_truthy {
                return Err(StructureError::invalid(
                    "condition value boolean polarity is stale",
                ));
            }
            if super::condition_forwarded_callee(
                proto,
                cfg,
                dataflow,
                node,
                value.phi,
                value.use_instr,
                node.id == condition.entry,
            ) != Some(value.forwarded_callee)
            {
                return Err(StructureError::invalid(
                    "condition value forwarded callee is stale",
                ));
            }
        }
    }
    Ok(())
}

fn validate_value_decision_plans(cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
    let decision_count = plan.value_decisions.len();
    let mut reachable_blocks = vec![false; cfg.blocks.len()];
    for block in &cfg.reachable_blocks {
        if let Some(reachable) = reachable_blocks.get_mut(block.index()) {
            *reachable = true;
        }
    }
    if plan.value_decision_region_by_plan.len() != decision_count {
        return Err(StructureError::invalid(
            "value decision region reverse index length mismatch",
        ));
    }

    let mut region_by_decision = vec![None; decision_count];
    let mut decision_by_region = vec![None; plan.regions.len()];
    for (region_index, region_plan) in plan.regions.iter().enumerate() {
        let RegionPlan::ValueDecision {
            plan: decision_id,
            entry,
            continuation,
            ..
        } = region_plan
        else {
            continue;
        };
        let region = RegionId(region_index);
        let decision = plan.value_decision(*decision_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision region #{region_index} references a missing payload"
            ))
        })?;
        let slot = region_by_decision
            .get_mut(decision_id.index())
            .ok_or_else(|| StructureError::invalid("value decision payload id is not dense"))?;
        if slot.replace(region).is_some() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has multiple region owners",
                decision_id.index()
            )));
        }
        decision_by_region[region_index] = Some(*decision_id);
        if plan.value_decision_region(*decision_id) != Some(region)
            || decision.header() != Some(*entry)
            || decision.merge != *continuation
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has a stale region, entry, or continuation",
                decision_id.index()
            )));
        }
    }
    for (index, region) in region_by_decision.iter().copied().enumerate() {
        let region = region.ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{index} has no owning region"
            ))
        })?;
        if plan.value_decision_region_by_plan[index] != region {
            return Err(StructureError::invalid(format!(
                "value decision payload #{index} has a stale region reverse index"
            )));
        }
    }

    let mut expected_decision_by_phi = vec![None; plan.value_decision_by_phi.len()];
    for index in 0..decision_count {
        let decision_id = ValueDecisionPlanId(index);
        let decision = &plan.value_decisions[index];
        for phi in
            std::iter::once(decision.result_phi).chain(decision.absorbed_phis.iter().copied())
        {
            let slot = expected_decision_by_phi
                .get_mut(phi.index())
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision phi reverse index exceeds the phi arena",
                    )
                })?;
            if slot.replace(decision_id).is_some() {
                return Err(StructureError::invalid(
                    "one phi is absorbed by multiple value decisions",
                ));
            }
        }
        if plan.value_decision_owner(decision.result_phi) != Some(decision_id) {
            return Err(StructureError::invalid(format!(
                "value decision payload #{index} has no unique phi reverse index"
            )));
        }
    }
    if plan.value_decision_by_phi != expected_decision_by_phi {
        return Err(StructureError::invalid(
            "value decision phi reverse index is stale",
        ));
    }

    let mut decision_for_block = vec![None; cfg.blocks.len()];
    let mut node_for_block = vec![None; cfg.blocks.len()];
    let mut leaf_for_block = vec![None; cfg.blocks.len()];
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        let region = region_by_decision[decision_index].ok_or_else(|| {
            StructureError::invalid("value decision payload lost its region owner")
        })?;
        if decision.blocks.is_empty()
            || decision.merge.index() >= cfg.blocks.len()
            || !reachable_blocks[decision.merge.index()]
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has empty coverage or a missing merge"
            )));
        }
        for block in &decision.blocks {
            let slot = decision_for_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "value decision payload #{decision_index} references missing block {block}"
                ))
            })?;
            let prior_owner = *slot;
            let label = plan.label_for_block(*block);
            if !reachable_blocks
                .get(block.index())
                .copied()
                .unwrap_or(false)
                || plan.region_for_block(*block) != Some(region)
                || prior_owner.is_some()
                || label.is_some() && decision.header() != Some(*block)
            {
                let goto_edges = label.map_or_else(Vec::new, |label| {
                    plan.edge_plans
                        .iter()
                        .filter(|edge| {
                            matches!(
                                edge.transfer,
                                EdgeTransfer::Goto(target, _) if target == label
                            )
                        })
                        .map(|edge| {
                            let cfg_edge = cfg.edges[edge.edge.index()];
                            format!(
                                "{} {} -> {} owner={:?} transfer={:?}",
                                edge.edge, cfg_edge.from, cfg_edge.to, edge.owner, edge.transfer
                            )
                        })
                        .collect::<Vec<_>>()
                });
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has stale, duplicate, or labeled block {block}: reachable={} expected-region={region:?} actual-region={:?} prior-owner={prior_owner:?} label={label:?} goto-edges={goto_edges:?}",
                    reachable_blocks
                        .get(block.index())
                        .copied()
                        .unwrap_or(false),
                    plan.region_for_block(*block),
                )));
            }
            *slot = Some(decision_id);
        }
        for (node_index, node) in decision.nodes.iter().enumerate() {
            let Some(slot) = node_for_block.get_mut(node.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} node {node_index} references a missing block"
                )));
            };
            if node.id.index() != node_index
                || decision_for_block[node.block.index()] != Some(decision_id)
                || slot.replace((decision_id, node.id)).is_some()
                || cfg.blocks[node.block.index()].instrs.last() != Some(node.predicate)
                || cfg.branch_edges(node.block).is_none()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has a stale or non-dense node {node_index}"
                )));
            }
        }
        for (leaf_index, leaf) in decision.leaves.iter().enumerate() {
            let Some(slot) = leaf_for_block.get_mut(leaf.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} leaf {leaf_index} references a missing block"
                )));
            };
            if leaf.id.index() != leaf_index
                || decision_for_block[leaf.block.index()] != Some(decision_id)
                || slot.replace((decision_id, leaf.id)).is_some()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{decision_index} has a stale or non-dense leaf {leaf_index}"
                )));
            }
        }
    }

    for (block_index, owner) in plan.region_by_block.iter().copied().enumerate() {
        let Some(owner) = owner else {
            continue;
        };
        if let Some(decision_id) = decision_by_region[owner.index()]
            && decision_for_block[block_index] != Some(decision_id)
        {
            return Err(StructureError::invalid(format!(
                "value decision region {owner:?} has block #{block_index} outside its frozen payload"
            )));
        }
    }
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        if decision_for_block[decision.merge.index()] == Some(ValueDecisionPlanId(decision_index)) {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} absorbs its merge block"
            )));
        }
    }

    let mut expected_route_owner = vec![None; cfg.edges.len()];
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        for block in &decision.blocks {
            for edge in cfg.succs.get(block.index()).into_iter().flatten() {
                let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                    StructureError::invalid("value decision successor index left the CFG arena")
                })?;
                if !reachable_blocks
                    .get(cfg_edge.to.index())
                    .copied()
                    .unwrap_or(false)
                {
                    continue;
                }
                let slot = &mut expected_route_owner[edge.index()];
                if slot.replace(decision_id).is_some() {
                    return Err(StructureError::invalid(
                        "one absorbed CFG edge belongs to multiple value decisions",
                    ));
                }
            }
        }
    }
    let mut requirement_on_edge = vec![false; cfg.edges.len()];
    for (_, requirement) in plan.requirements.iter() {
        let Some(edge) = requirement.edge() else {
            continue;
        };
        let Some(slot) = requirement_on_edge.get_mut(edge.index()) else {
            return Err(StructureError::invalid(
                "value decision saw a requirement outside the CFG arena",
            ));
        };
        *slot = true;
    }
    let unique_reachable_outgoing = cfg
        .succs
        .iter()
        .map(|outgoing| {
            let mut reachable = outgoing
                .iter()
                .copied()
                .filter(|edge| reachable_blocks[cfg.edges[edge.index()].to.index()]);
            match (reachable.next(), reachable.next()) {
                (Some(edge), None) => Some(edge),
                _ => None,
            }
        })
        .collect::<Vec<_>>();

    let mut covered_route_owner = vec![None; cfg.edges.len()];
    let mut route_visit_stamp = vec![0usize; cfg.blocks.len()];
    let mut route_state = ValueDecisionRouteState {
        covered_route_owner: &mut covered_route_owner,
        route_visit_stamp: &mut route_visit_stamp,
        next_route_stamp: 0,
    };
    for (decision_index, decision) in plan.value_decisions.iter().enumerate() {
        let decision_id = ValueDecisionPlanId(decision_index);
        let region = region_by_decision[decision_index].ok_or_else(|| {
            StructureError::invalid("value decision payload lost its region owner")
        })?;
        if decision.nodes.is_empty() || decision.entry.index() >= decision.nodes.len() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has no valid entry"
            )));
        }
        if !decision
            .leaves
            .iter()
            .any(|leaf| leaf.terminal_edge == decision.shared_exit_action)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has no valid shared exit action"
            )));
        }

        let mut indegree = vec![0usize; decision.nodes.len()];
        for (node_index, node) in decision.nodes.iter().enumerate() {
            let context = ValueDecisionRouteContext {
                cfg,
                plan,
                decision_id,
                region,
                decision,
                decision_for_block: &decision_for_block,
                node_for_block: &node_for_block,
                expected_route_owner: &expected_route_owner,
                requirement_on_edge: &requirement_on_edge,
                unique_reachable_outgoing: &unique_reachable_outgoing,
            };
            for (semantic_truthy, arc) in [(true, &node.truthy), (false, &node.falsy)] {
                context.validate_arc(node_index, node, semantic_truthy, arc, &mut route_state)?;
                match arc.target {
                    ValueDecisionTarget::Node(target) => {
                        let Some(degree) = indegree.get_mut(target.index()) else {
                            return Err(StructureError::invalid(format!(
                                "value decision payload #{decision_index} references a missing node"
                            )));
                        };
                        *degree += 1;
                    }
                    ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf)
                        if leaf.index() >= decision.leaves.len() =>
                    {
                        return Err(StructureError::invalid(format!(
                            "value decision payload #{decision_index} references a missing leaf"
                        )));
                    }
                    ValueDecisionTarget::Leaf(_) | ValueDecisionTarget::CurrentValue(_) => {}
                }
            }
        }

        let mut reachable_nodes = vec![false; decision.nodes.len()];
        let mut reachable_leaves = vec![false; decision.leaves.len()];
        let mut pending = vec![decision.entry];
        while let Some(node_id) = pending.pop() {
            let Some(node) = decision.nodes.get(node_id.index()) else {
                return Err(StructureError::invalid(
                    "value decision reachability left the node arena",
                ));
            };
            if std::mem::replace(&mut reachable_nodes[node_id.index()], true) {
                continue;
            }
            for target in [node.truthy.target, node.falsy.target] {
                match target {
                    ValueDecisionTarget::Node(target) => pending.push(target),
                    ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => {
                        let Some(reachable) = reachable_leaves.get_mut(leaf.index()) else {
                            return Err(StructureError::invalid(
                                "value decision reachability left the leaf arena",
                            ));
                        };
                        *reachable = true;
                    }
                }
            }
        }
        if reachable_nodes.iter().any(|reachable| !reachable)
            || reachable_leaves.iter().any(|reachable| !reachable)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} has unreachable nodes or leaves"
            )));
        }

        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(index, degree)| (*degree == 0).then_some(index))
            .collect::<Vec<_>>();
        let mut visited = 0usize;
        while let Some(node_index) = ready.pop() {
            visited += 1;
            let node = &decision.nodes[node_index];
            for target in [node.truthy.target, node.falsy.target] {
                let ValueDecisionTarget::Node(target) = target else {
                    continue;
                };
                indegree[target.index()] -= 1;
                if indegree[target.index()] == 0 {
                    ready.push(target.index());
                }
            }
        }
        if visited != decision.nodes.len() {
            return Err(StructureError::invalid(format!(
                "value decision payload #{decision_index} contains a cycle"
            )));
        }
    }
    if route_state.covered_route_owner != expected_route_owner {
        return Err(StructureError::invalid(
            "value decision routes do not exactly cover their absorbed CFG edges",
        ));
    }
    Ok(())
}

struct ValueDecisionRouteContext<'a> {
    cfg: &'a Cfg,
    plan: &'a StructurePlan,
    decision_id: ValueDecisionPlanId,
    region: RegionId,
    decision: &'a ValueDecisionPlan,
    decision_for_block: &'a [Option<ValueDecisionPlanId>],
    node_for_block: &'a [Option<(ValueDecisionPlanId, super::ValueDecisionNodeId)>],
    expected_route_owner: &'a [Option<ValueDecisionPlanId>],
    requirement_on_edge: &'a [bool],
    unique_reachable_outgoing: &'a [Option<crate::structure::EdgeRef>],
}

struct ValueDecisionRouteState<'a> {
    covered_route_owner: &'a mut [Option<ValueDecisionPlanId>],
    route_visit_stamp: &'a mut [usize],
    next_route_stamp: usize,
}

impl ValueDecisionRouteContext<'_> {
    fn validate_arc(
        &self,
        node_index: usize,
        node: &super::ValueDecisionNodePlan,
        semantic_truthy: bool,
        arc: &ValueDecisionArcPlan,
        state: &mut ValueDecisionRouteState<'_>,
    ) -> Result<(), StructureError> {
        let expected_polarity = match semantic_truthy ^ node.predicate_negated {
            true => ConditionArcPolarity::BranchTrue,
            false => ConditionArcPolarity::BranchFalse,
        };
        let (branch_true, branch_false) = self.cfg.branch_edges(node.block).ok_or_else(|| {
            StructureError::invalid("value decision node lost its physical branch edges")
        })?;
        let expected_first = match expected_polarity {
            ConditionArcPolarity::BranchTrue => branch_true,
            ConditionArcPolarity::BranchFalse => branch_false,
        };
        let first = arc.route.first().copied().ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{} node {node_index} has an empty route",
                self.decision_id.index()
            ))
        })?;
        if arc.polarity != expected_polarity || first != expected_first {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} node {node_index} has stale semantic polarity",
                self.decision_id.index()
            )));
        }

        if state.next_route_stamp == usize::MAX {
            state.route_visit_stamp.fill(0);
            state.next_route_stamp = 1;
        } else {
            state.next_route_stamp += 1;
        }
        let stamp = state.next_route_stamp;
        state.route_visit_stamp[node.block.index()] = stamp;
        let logical_leaf = match arc.target {
            ValueDecisionTarget::Node(_) => None,
            ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => self
                .decision
                .leaves
                .get(leaf.index())
                .map(|leaf| leaf.block),
        };
        let mut passes_logical_leaf = logical_leaf == Some(node.block);
        let mut previous_target = None;
        for (position, edge_ref) in arc.route.iter().copied().enumerate() {
            let edge = self.cfg.edges.get(edge_ref.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "value decision payload #{} route references a missing CFG edge",
                    self.decision_id.index()
                ))
            })?;
            if (position == 0 && edge.from != node.block)
                || previous_target.is_some_and(|target| target != edge.from)
                || self
                    .decision_for_block
                    .get(edge.from.index())
                    .copied()
                    .flatten()
                    != Some(self.decision_id)
                || self
                    .expected_route_owner
                    .get(edge_ref.index())
                    .copied()
                    .flatten()
                    != Some(self.decision_id)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} has a non-contiguous or foreign route",
                    self.decision_id.index()
                )));
            }
            if position == 0
                && !matches!(
                    (arc.polarity, edge.kind),
                    (ConditionArcPolarity::BranchTrue, EdgeKind::BranchTrue)
                        | (ConditionArcPolarity::BranchFalse, EdgeKind::BranchFalse)
                )
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} route starts on the wrong CFG arm",
                    self.decision_id.index()
                )));
            }
            if position > 0
                && self
                    .unique_reachable_outgoing
                    .get(edge.from.index())
                    .copied()
                    .flatten()
                    != Some(edge_ref)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} route crosses a non-linear connector",
                    self.decision_id.index()
                )));
            }
            let is_last = position + 1 == arc.route.len();
            if !is_last
                && (edge.to == self.decision.merge
                    || self
                        .node_for_block
                        .get(edge.to.index())
                        .copied()
                        .flatten()
                        .is_some()
                    || self
                        .decision_for_block
                        .get(edge.to.index())
                        .copied()
                        .flatten()
                        != Some(self.decision_id))
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} route crosses an undeclared node or boundary",
                    self.decision_id.index()
                )));
            }
            let Some(visit) = state.route_visit_stamp.get_mut(edge.to.index()) else {
                return Err(StructureError::invalid(
                    "value decision route reaches a missing block",
                ));
            };
            if *visit == stamp {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} contains a cyclic physical route",
                    self.decision_id.index()
                )));
            }
            *visit = stamp;
            passes_logical_leaf |= logical_leaf == Some(edge.to);

            let edge_plan = self.plan.edge_plan(edge_ref).ok_or_else(|| {
                StructureError::invalid("value decision route has no frozen edge plan")
            })?;
            let shared_action = self
                .plan
                .edge_plan(self.decision.shared_exit_action)
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision shared exit action has no frozen edge plan",
                    )
                })?;
            let terminal_action_matches = if is_last && logical_leaf.is_some() {
                edge_plan.phi_copies == shared_action.phi_copies && edge_plan.iteration.is_empty()
            } else {
                edge_plan.phi_copies.is_empty() && edge_plan.iteration.is_empty()
            };
            if edge_plan.owner != self.region
                || edge_plan.transfer != EdgeTransfer::Fallthrough
                || edge_plan.action_placement != EdgeActionPlacement::BeforeTransfer
                || edge_plan.forward_route.is_some()
                || !terminal_action_matches
                || self.requirement_on_edge[edge_ref.index()]
                || !self.plan.requirements.for_edge(edge_ref).is_empty()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} has incompatible absorbed edge {edge_ref}: owner={:?} transfer={:?} copies={} iteration={} terminal-action={terminal_action_matches}",
                    self.decision_id.index(),
                    edge_plan.owner,
                    edge_plan.transfer,
                    edge_plan.phi_copies.len(),
                    edge_plan.iteration.len(),
                )));
            }
            match state.covered_route_owner[edge_ref.index()] {
                Some(existing) if existing != self.decision_id => {
                    return Err(StructureError::invalid(
                        "one physical route edge belongs to multiple value decisions",
                    ));
                }
                Some(_) => {}
                None => state.covered_route_owner[edge_ref.index()] = Some(self.decision_id),
            }
            previous_target = Some(edge.to);
        }

        let terminal = previous_target
            .ok_or_else(|| StructureError::invalid("value decision route has no terminal block"))?;
        match arc.target {
            ValueDecisionTarget::Node(target) => {
                if self
                    .decision
                    .nodes
                    .get(target.index())
                    .map(|node| node.block)
                    != Some(terminal)
                {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} route misses its target node",
                        self.decision_id.index()
                    )));
                }
            }
            ValueDecisionTarget::Leaf(leaf) | ValueDecisionTarget::CurrentValue(leaf) => {
                let leaf = self.decision.leaves.get(leaf.index()).ok_or_else(|| {
                    StructureError::invalid("value decision route references a missing leaf")
                })?;
                if terminal != self.decision.merge
                    || !passes_logical_leaf
                    || arc.route.last().copied() != Some(leaf.terminal_edge)
                {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} route misses its logical leaf or merge",
                        self.decision_id.index()
                    )));
                }
            }
        }
        Ok(())
    }
}

fn validate_value_decision_values(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.value_decision_by_phi.len() != dataflow.phi_candidates.len() {
        return Err(StructureError::invalid(
            "value decision phi reverse index length mismatch",
        ));
    }
    let mut unresolved_result_phi = vec![false; dataflow.phi_candidates.len()];
    for (_, requirement) in plan.requirements.iter() {
        let PlanRequirement::UnresolvedValue { phi_id, .. } = requirement else {
            continue;
        };
        let Some(slot) = unresolved_result_phi.get_mut(phi_id.index()) else {
            return Err(StructureError::invalid(
                "unresolved value requirement references a missing phi",
            ));
        };
        *slot = true;
    }
    let mut incoming_by_edge = vec![None; cfg.edges.len()];
    let mut terminal_edge_owner = vec![None; cfg.edges.len()];
    for (decision_id, decision) in plan.value_decisions() {
        let region = plan
            .value_decision_region(decision_id)
            .ok_or_else(|| StructureError::invalid("value decision has no final region owner"))?;
        let result_phi = dataflow.phi_candidate(decision.result_phi).ok_or_else(|| {
            StructureError::invalid(format!(
                "value decision payload #{} references a missing result phi",
                decision_id.index()
            ))
        })?;
        if result_phi.id != decision.result_phi
            || result_phi.block != decision.merge
            || result_phi.reg != decision.result_reg
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} has a stale result identity",
                decision_id.index()
            )));
        }
        let phi_plan = plan.phi_plan(decision.result_phi).ok_or_else(|| {
            StructureError::invalid("value decision result phi has no final value plan")
        })?;
        if phi_plan.incomings.len() != result_phi.incoming.len()
            || !plan.phis_for_region(region).contains(&decision.result_phi)
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} result phi has stale shape or no region owner",
                decision_id.index()
            )));
        }
        for (incoming, incoming_plan) in result_phi.incoming.iter().zip(&phi_plan.incomings) {
            let valid = match incoming_plan.disposition {
                PhiIncomingDisposition::RegionResult(owner) => owner == region,
                PhiIncomingDisposition::LoopCarried(owner)
                    if incoming.value == SsaValue::Phi(result_phi.id) =>
                {
                    matches!(
                        plan.region(owner),
                        Some(RegionPlan::Loop { plan: loop_id, .. })
                            if plan.loop_(*loop_id).is_some_and(|loop_| loop_.header == decision.merge)
                    )
                }
                _ => false,
            };
            if !valid {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} result phi has a foreign incoming owner",
                    decision_id.index()
                )));
            }
        }
        if unresolved_result_phi[decision.result_phi.index()] {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} retains an unresolved result requirement",
                decision_id.index()
            )));
        }

        for (node_index, node) in decision.nodes.iter().enumerate() {
            let Some(LowInstr::Branch(branch)) = proto.instrs.get(node.predicate.index()) else {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} predicate is not a branch",
                    decision_id.index()
                )));
            };
            if cfg.instr_to_block.get(node.predicate.index()).copied() != Some(node.block)
                || branch.cond.negated != node.predicate_negated
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} node {node_index} has a stale predicate binding",
                    decision_id.index()
                )));
            }
            for arc in [&node.truthy, &node.falsy] {
                let ValueDecisionTarget::CurrentValue(leaf) = arc.target else {
                    continue;
                };
                let leaf = decision.leaves.get(leaf.index()).ok_or_else(|| {
                    StructureError::invalid(
                        "value decision current-value target references a missing leaf",
                    )
                })?;
                if !super::value_leaf_is_current(
                    proto,
                    dataflow,
                    node.predicate,
                    branch,
                    decision.result_reg,
                    leaf.value,
                    leaf.latest_local_def,
                ) {
                    return Err(StructureError::invalid(format!(
                        "value decision payload #{} node {node_index} current-value target contradicts its SSA identity",
                        decision_id.index()
                    )));
                }
            }
        }

        for (incoming_index, (incoming, incoming_plan)) in result_phi
            .incoming
            .iter()
            .zip(&phi_plan.incomings)
            .enumerate()
        {
            if incoming_plan.disposition != PhiIncomingDisposition::RegionResult(region) {
                continue;
            }
            let edge = incoming.edge.ok_or_else(|| {
                StructureError::invalid("value decision result phi has a synthetic incoming")
            })?;
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("value decision result incoming left the CFG arena")
            })?;
            let slot = &mut incoming_by_edge[edge.index()];
            if cfg_edge.to != decision.merge
                || incoming.pred != Some(cfg_edge.from)
                || slot.replace((decision_id, incoming_index)).is_some()
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} has a stale or duplicate result incoming",
                    decision_id.index()
                )));
            }
        }
        for (leaf_index, leaf) in decision.leaves.iter().enumerate() {
            if dataflow.block_exit_value(leaf.block, decision.result_reg) != leaf.value {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has a stale logical SSA value",
                    decision_id.index()
                )));
            }
            let expected_local_def = match leaf.value {
                SsaValue::Def(def) => dataflow
                    .defs
                    .get(def.index())
                    .filter(|record| {
                        record.id == def
                            && record.block == leaf.block
                            && record.reg == decision.result_reg
                    })
                    .map(|_| def),
                SsaValue::Entry(_) | SsaValue::Phi(_) => None,
            };
            if leaf.latest_local_def != expected_local_def {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has a stale local definition",
                    decision_id.index()
                )));
            }

            let edge = cfg.edges.get(leaf.terminal_edge.index()).ok_or_else(|| {
                StructureError::invalid("value decision leaf terminal edge is outside the CFG")
            })?;
            let incoming_index = incoming_by_edge
                .get(leaf.terminal_edge.index())
                .copied()
                .flatten()
                .filter(|(owner, _)| *owner == decision_id)
                .map(|(_, incoming)| incoming)
                .ok_or_else(|| {
                    StructureError::invalid(
                        "value decision leaf terminal edge has no result incoming",
                    )
                })?;
            let incoming = &result_phi.incoming[incoming_index];
            if edge.from != leaf.physical_pred
                || edge.to != decision.merge
                || incoming.pred != Some(leaf.physical_pred)
                || incoming.value != leaf.physical_value
                || !dataflow.value_contains(leaf.physical_value, leaf.value)
            {
                return Err(StructureError::invalid(format!(
                    "value decision payload #{} leaf {leaf_index} has stale physical provenance",
                    decision_id.index()
                )));
            }
            let slot = &mut terminal_edge_owner[leaf.terminal_edge.index()];
            if slot.is_some_and(|owner| owner != decision_id) {
                return Err(StructureError::invalid(
                    "one terminal edge belongs to multiple value decisions",
                ));
            }
            *slot = Some(decision_id);
        }
        if result_phi
            .incoming
            .iter()
            .zip(&phi_plan.incomings)
            .any(|(incoming, incoming_plan)| {
                incoming_plan.disposition == PhiIncomingDisposition::RegionResult(region)
                    && incoming
                        .edge
                        .is_none_or(|edge| terminal_edge_owner[edge.index()] != Some(decision_id))
            })
        {
            return Err(StructureError::invalid(format!(
                "value decision payload #{} leaves a result incoming uncovered",
                decision_id.index()
            )));
        }
    }
    Ok(())
}

fn validate_condition_prefix_placements(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    for (index, payload) in plan.loops.iter().enumerate() {
        if payload.kind != crate::structure::LoopKindHint::RepeatLike
            || payload.condition_prefix_placement
                != Some(crate::structure::LoopConditionPrefixPlacement::BeforeBody)
            || payload.control_edges.continues.is_empty()
        {
            continue;
        }
        let condition_entry = payload
            .condition
            .and_then(|id| plan.condition(id))
            .and_then(ConditionPlan::header)
            .or(payload.condition_header)
            .or_else(|| {
                (payload.kind == crate::structure::LoopKindHint::RepeatLike)
                    .then_some(payload.continue_target)
                    .flatten()
            })
            .unwrap_or(payload.header);
        if condition_entry == payload.header {
            continue;
        }
        let range = cfg.blocks[condition_entry.index()].instrs;
        let end = range.last().map_or(range.end(), |last| {
            if proto.instrs[last.index()].is_control_terminator() {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if !(range.start.index()..end).all(|instr| {
            matches!(
                proto.instrs[instr],
                LowInstr::LoadNil(_)
                    | LowInstr::LoadBool(_)
                    | LowInstr::LoadConst(_)
                    | LowInstr::LoadInteger(_)
                    | LowInstr::LoadNumber(_)
            )
        }) {
            return Err(StructureError::invalid(format!(
                "loop payload #{index} moves an effectful condition prefix before the body"
            )));
        }
    }
    Ok(())
}

fn validate_containment(plan: &StructurePlan) -> Result<(), StructureError> {
    let mut references = vec![0usize; plan.regions.len()];
    let mut children = vec![Vec::new(); plan.regions.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let owner = RegionId(index);
        if let RegionPlan::Unstructured { layout, .. } = region {
            for child in layout.iter().filter_map(|item| match item {
                UnstructuredLayoutItem::Region(child) => Some(*child),
                UnstructuredLayoutItem::Block(_) => None,
            }) {
                if matches!(
                    plan.regions.get(child.index()),
                    Some(RegionPlan::Unstructured { .. })
                ) {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} directly contains island child #{}",
                        child.index()
                    )));
                }
            }
        }
        let owned = match region {
            RegionPlan::Block { .. } => Vec::new(),
            RegionPlan::Sequence { children, .. } => children.clone(),
            RegionPlan::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            } => [Some(*condition), Some(*then_arm), *else_arm]
                .into_iter()
                .flatten()
                .collect(),
            RegionPlan::ValueDecision { .. } => Vec::new(),
            RegionPlan::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            } => [*preheader, Some(*control), Some(*body), *normal_tail]
                .into_iter()
                .flatten()
                .collect(),
            RegionPlan::Unstructured { layout, .. } => layout
                .iter()
                .filter_map(|item| match item {
                    UnstructuredLayoutItem::Region(region) => Some(*region),
                    UnstructuredLayoutItem::Block(_) => None,
                })
                .collect(),
        };
        for child in owned {
            let Some(child_plan) = plan.regions.get(child.index()) else {
                return Err(StructureError::invalid(format!(
                    "region {owner:?} references missing child {child:?}"
                )));
            };
            if child_plan.parent() != Some(owner) {
                return Err(StructureError::invalid(format!(
                    "region {child:?} parent disagrees with owner {owner:?}"
                )));
            }
            references[child.index()] += 1;
            children[index].push(child);
        }
    }
    for (index, count) in references.into_iter().enumerate() {
        let expected = usize::from(index != plan.root.index());
        if count != expected {
            return Err(StructureError::invalid(format!(
                "region #{index} has {count} containment references; expected {expected}"
            )));
        }
    }
    let mut pending = vec![(plan.root, false)];
    while let Some((region, inside_island)) = pending.pop() {
        let is_island = matches!(
            plan.regions.get(region.index()),
            Some(RegionPlan::Unstructured { .. })
        );
        if inside_island && is_island {
            return Err(StructureError::invalid(format!(
                "unstructured region #{} is nested inside another island",
                region.index()
            )));
        }
        pending.extend(
            children[region.index()]
                .iter()
                .copied()
                .map(|child| (child, inside_island || is_island)),
        );
    }
    Ok(())
}

struct RegionBlockStats {
    subtree_counts: Vec<usize>,
}

impl RegionBlockStats {
    fn new(plan: &StructurePlan, intervals: &RegionNavigation) -> Result<Self, StructureError> {
        let mut subtree_counts = vec![0usize; plan.regions.len()];
        for owner in plan.region_by_block.iter().copied().flatten() {
            *subtree_counts.get_mut(owner.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "block owner references missing region {:?} while building validation stats",
                    owner
                ))
            })? += 1;
        }
        for region in &intervals.postorder {
            if let Some(parent) = intervals.parent[region.index()] {
                subtree_counts[parent.index()] += subtree_counts[region.index()];
            }
        }
        Ok(Self { subtree_counts })
    }

    fn subtree_count(&self, region: RegionId) -> usize {
        self.subtree_counts[region.index()]
    }
}

fn region_contains_block(
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    region: RegionId,
    block: BlockRef,
) -> bool {
    plan.region_for_block(block)
        .is_some_and(|owner| intervals.contains(region, owner))
}

fn region_matches_exact_blocks<I>(
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    stats: &RegionBlockStats,
    region: RegionId,
    expected_len: usize,
    expected_blocks: I,
) -> bool
where
    I: IntoIterator<Item = BlockRef>,
{
    stats.subtree_count(region) == expected_len
        && expected_blocks
            .into_iter()
            .all(|block| region_contains_block(plan, intervals, region, block))
}

fn validate_block_coverage(cfg: &Cfg, plan: &StructurePlan) -> Result<(), StructureError> {
    let mut claims = vec![None; cfg.blocks.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let owner = RegionId(index);
        let blocks = match region {
            RegionPlan::Block { block, .. } => vec![*block],
            RegionPlan::Unstructured { layout, .. } => layout
                .iter()
                .filter_map(|item| match item {
                    UnstructuredLayoutItem::Block(block) => Some(*block),
                    UnstructuredLayoutItem::Region(_) => None,
                })
                .collect(),
            RegionPlan::ValueDecision { plan: decision, .. } => plan
                .value_decision(*decision)
                .map(|decision| decision.blocks().collect())
                .unwrap_or_default(),
            RegionPlan::Sequence { .. } | RegionPlan::Branch { .. } | RegionPlan::Loop { .. } => {
                Vec::new()
            }
        };
        for block in blocks {
            let Some(slot) = claims.get_mut(block.index()) else {
                return Err(StructureError::invalid(format!(
                    "region {owner:?} claims missing block {block}"
                )));
            };
            if slot.replace(owner).is_some() {
                return Err(StructureError::invalid(format!(
                    "block {block} is claimed by multiple regions"
                )));
            }
        }
    }
    for block in &cfg.block_order {
        let expected = cfg.reachable_blocks.contains(block);
        if claims[block.index()].is_some() != expected {
            return Err(StructureError::invalid(format!(
                "block {block} coverage disagrees with reachability"
            )));
        }
        if plan.region_by_block[block.index()] != claims[block.index()] {
            return Err(StructureError::invalid(format!(
                "block {block} owner index disagrees with arena claim"
            )));
        }
    }
    Ok(())
}

fn validate_region_entries(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    let expected_island_ports = intervals.collect_island_ports(cfg, &plan.regions)?;
    for (index, region) in plan.regions.iter().enumerate() {
        let region_id = RegionId(index);
        let boundary = intervals.boundary(region_id).ok_or_else(|| {
            StructureError::invalid(format!("region #{index} has no boundary summary"))
        })?;
        match region {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => {
                let through_entry = cfg.preds[entry.index()]
                    .iter()
                    .filter(|edge| {
                        let source = cfg.edges[edge.index()].from;
                        cfg.reachable_blocks.contains(&source)
                            && plan
                                .region_for_block(source)
                                .is_some_and(|owner| !intervals.contains(region_id, owner))
                    })
                    .count();
                if boundary.entry_count != through_entry {
                    return Err(StructureError::invalid(format!(
                        "structured region #{index} has a non-entry incoming edge"
                    )));
                }
            }
            RegionPlan::Unstructured {
                entry,
                entries,
                exits,
                ..
            } => {
                if !region_contains_block(plan, intervals, region_id, *entry) {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} entry block is outside its containment"
                    )));
                }
                let expected_entries = &expected_island_ports.entries[index];
                let expected_exits = &expected_island_ports.exits[index];
                if entries != expected_entries || exits != expected_exits {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} has stale or unordered boundary ports: entries={entries:?}, expected={expected_entries:?}, exits={exits:?}, expected={expected_exits:?}"
                    )));
                }
                if boundary.entry_count != entries.len() || boundary.exit_count != exits.len() {
                    return Err(StructureError::invalid(format!(
                        "unstructured region #{index} boundary summary disagrees with its ports"
                    )));
                }
            }
            RegionPlan::Block { .. } | RegionPlan::Sequence { .. } => {}
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ConditionEdgeBinding {
    condition: ConditionPlanId,
    node: BlockRef,
    target: ConditionTarget,
}

struct ConditionEdgeIndex {
    first: Vec<Option<ConditionEdgeBinding>>,
    terminal: Vec<Option<ConditionEdgeBinding>>,
    terminal_endpoint: Vec<Option<BlockRef>>,
}

impl ConditionEdgeIndex {
    fn new(edge_count: usize) -> Self {
        Self {
            first: vec![None; edge_count],
            terminal: vec![None; edge_count],
            terminal_endpoint: vec![None; edge_count],
        }
    }

    fn record_first(
        &mut self,
        edge: EdgeRef,
        binding: ConditionEdgeBinding,
    ) -> Result<(), StructureError> {
        record_condition_edge(&mut self.first, edge, binding, "first")
    }

    fn record_terminal(
        &mut self,
        edge: EdgeRef,
        binding: ConditionEdgeBinding,
        endpoint: BlockRef,
    ) -> Result<(), StructureError> {
        record_condition_edge(&mut self.terminal, edge, binding, "terminal")?;
        let slot = self
            .terminal_endpoint
            .get_mut(edge.index())
            .ok_or_else(|| StructureError::invalid("condition terminal edge is outside the CFG"))?;
        if slot.replace(endpoint).is_some_and(|old| old != endpoint) {
            return Err(StructureError::invalid(format!(
                "condition terminal edge {edge} has conflicting physical endpoints"
            )));
        }
        Ok(())
    }

    fn first_target(&self, condition: ConditionPlanId, edge: EdgeRef) -> Option<ConditionTarget> {
        self.first
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)
            .map(|binding| binding.target)
    }

    fn terminal_target(
        &self,
        condition: ConditionPlanId,
        edge: EdgeRef,
    ) -> Option<ConditionTarget> {
        self.terminal
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)
            .map(|binding| binding.target)
    }

    fn terminal_endpoint(&self, condition: ConditionPlanId, edge: EdgeRef) -> Option<BlockRef> {
        self.terminal
            .get(edge.index())
            .copied()
            .flatten()
            .filter(|binding| binding.condition == condition)?;
        self.terminal_endpoint.get(edge.index()).copied().flatten()
    }
}

fn record_condition_edge(
    index: &mut [Option<ConditionEdgeBinding>],
    edge: EdgeRef,
    binding: ConditionEdgeBinding,
    position: &str,
) -> Result<(), StructureError> {
    let Some(slot) = index.get_mut(edge.index()) else {
        return Err(StructureError::invalid(format!(
            "condition {} edge {edge} is outside the CFG arena",
            position
        )));
    };
    if let Some(existing) = *slot
        && existing != binding
    {
        return Err(StructureError::invalid(format!(
            "condition {position} edge {edge} has conflicting frozen owners: {existing:?} vs {binding:?}"
        )));
    }
    *slot = Some(binding);
    Ok(())
}

fn validate_condition_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<ConditionEdgeIndex, StructureError> {
    let mut edge_index = ConditionEdgeIndex::new(cfg.edges.len());
    for (phi_index, owner) in plan.condition_value_by_phi.iter().copied().enumerate() {
        let Some((condition_id, node_id)) = owner else {
            continue;
        };
        let value = plan
            .condition(condition_id)
            .and_then(|condition| condition.nodes.get(node_id.index()))
            .and_then(|node| node.materialized_value)
            .ok_or_else(|| {
                StructureError::invalid("condition value reverse index references a missing node")
            })?;
        if value.phi.index() != phi_index {
            return Err(StructureError::invalid(
                "condition value reverse index has a stale phi",
            ));
        }
    }
    let mut referenced = vec![false; plan.conditions.len()];
    for branch in &plan.branches {
        let Some(slot) = referenced.get_mut(branch.condition.index()) else {
            return Err(StructureError::invalid(
                "branch references a missing condition payload",
            ));
        };
        *slot = true;
    }
    for loop_ in &plan.loops {
        if let Some(condition) = loop_.condition {
            let Some(slot) = referenced.get_mut(condition.index()) else {
                return Err(StructureError::invalid(
                    "loop references a missing condition payload",
                ));
            };
            *slot = true;
        }
    }

    let mut seen_block_epoch = vec![0usize; cfg.blocks.len()];
    for (index, condition) in plan.conditions.iter().enumerate() {
        if !referenced[index]
            || condition.nodes.is_empty()
            || condition.entry.index() >= condition.nodes.len()
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} is unreferenced or has no valid entry"
            )));
        }

        let mut blocks = Vec::new();
        let epoch = index.checked_add(1).ok_or_else(|| {
            StructureError::invalid("condition count exceeds validation epoch capacity")
        })?;
        let mut reachable = vec![false; condition.nodes.len()];
        let mut indegree = vec![0usize; condition.nodes.len()];
        let mut terminal_edges = [Vec::new(), Vec::new()];
        for (node_index, node) in condition.nodes.iter().enumerate() {
            if node.id.index() != node_index || node.block.index() >= cfg.blocks.len() {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} has non-dense nodes or duplicate blocks"
                )));
            }
            let Some(seen_epoch) = seen_block_epoch.get_mut(node.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} references a missing block"
                )));
            };
            if std::mem::replace(seen_epoch, epoch) == epoch {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} has duplicate node blocks"
                )));
            }
            blocks.push(node.block);
            let range = cfg.blocks[node.block.index()].instrs;
            let predicate = range.last().ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} has an empty predicate block"
                ))
            })?;
            if predicate != node.predicate {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} has a stale predicate binding"
                )));
            }
            let (branch_true, branch_false) = cfg.branch_edges(node.block).ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} node {node_index} is not a CFG branch"
                ))
            })?;
            for (polarity, expected_first) in [
                (ConditionArcPolarity::BranchTrue, branch_true),
                (ConditionArcPolarity::BranchFalse, branch_false),
            ] {
                let arc = node.arc(polarity);
                if arc.source != node.id {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} arc owner is stale"
                    )));
                }
                let Some(first_edge) = arc.route.first().copied() else {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} has an empty route"
                    )));
                };
                if first_edge != expected_first || arc.polarity != polarity {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} has a stale physical route"
                    )));
                }
                edge_index.record_first(
                    first_edge,
                    ConditionEdgeBinding {
                        condition: ConditionPlanId(index),
                        node: node.block,
                        target: arc.target,
                    },
                )?;
                let mut connector_blocks = Vec::new();
                for pair in arc.route.windows(2) {
                    let current = cfg.edges.get(pair[0].index()).ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} route references a missing CFG edge"
                        ))
                    })?;
                    let next = cfg.edges.get(pair[1].index()).ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} route references a missing CFG edge"
                        ))
                    })?;
                    if current.to != next.from {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} node {node_index} route is not contiguous"
                        )));
                    }
                    connector_blocks.push(current.to);
                }
                if connector_blocks != arc.connector_blocks {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} route connector blocks are stale"
                    )));
                }
                if !arc.route.contains(&arc.transfer) {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} transfer is outside its route"
                    )));
                }
                let transfer_position = arc
                    .route
                    .iter()
                    .position(|edge| *edge == arc.transfer)
                    .ok_or_else(|| {
                        StructureError::invalid(format!(
                            "condition payload #{index} node {node_index} transfer is outside its route"
                        ))
                    })?;
                for block in arc.connector_blocks.iter().take(transfer_position) {
                    let Some(seen_epoch) = seen_block_epoch.get_mut(block.index()) else {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} connector references a missing block"
                        )));
                    };
                    if std::mem::replace(seen_epoch, epoch) == epoch {
                        return Err(StructureError::invalid(format!(
                            "condition payload #{index} reuses a condition block across nodes"
                        )));
                    }
                    blocks.push(*block);
                }
                validate_condition_internal_route(cfg, plan, index, node_index, arc)?;
                let last_edge = *arc.route.last().ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} node {node_index} route is empty"
                    ))
                })?;
                match arc.target {
                    ConditionTarget::Node(target) => {
                        let target_node = condition.nodes.get(target.index()).ok_or_else(|| {
                            StructureError::invalid(format!(
                                "condition payload #{index} references a missing node"
                            ))
                        })?;
                        if cfg.edges[last_edge.index()].to != target_node.block {
                            return Err(StructureError::invalid(format!(
                                "condition payload #{index} node edge contradicts the CFG"
                            )));
                        }
                        indegree[target.index()] += 1;
                    }
                    ConditionTarget::Truthy => {
                        terminal_edges[0].push(arc.transfer);
                        edge_index.record_terminal(
                            arc.transfer,
                            ConditionEdgeBinding {
                                condition: ConditionPlanId(index),
                                node: node.block,
                                target: ConditionTarget::Truthy,
                            },
                            cfg.edges[last_edge.index()].to,
                        )?;
                    }
                    ConditionTarget::Falsy => {
                        terminal_edges[1].push(arc.transfer);
                        edge_index.record_terminal(
                            arc.transfer,
                            ConditionEdgeBinding {
                                condition: ConditionPlanId(index),
                                node: node.block,
                                target: ConditionTarget::Falsy,
                            },
                            cfg.edges[last_edge.index()].to,
                        )?;
                    }
                }
            }
            if let Some(value) = node.materialized_value {
                let (ConditionTarget::Node(truthy), ConditionTarget::Node(falsy)) =
                    (node.semantic_target(true), node.semantic_target(false))
                else {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} value node {node_index} has a terminal route"
                    )));
                };
                if truthy != falsy
                    || truthy == node.id
                    || condition.nodes.get(truthy.index()).is_none()
                    || plan.condition_value_owner(value.phi)
                        != Some((super::ConditionPlanId(index), node.id))
                    || cfg.instr_to_block.get(value.use_instr.index()).copied()
                        != Some(condition.nodes[truthy.index()].block)
                {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} value node {node_index} has stale ownership or consumer"
                    )));
                }
            }
        }
        if blocks != condition.blocks {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} has stale frozen block coverage"
            )));
        }

        let expected_exits = [condition.truthy, condition.falsy];
        for terminal_index in 0..2 {
            let exits = &terminal_edges[terminal_index];
            let representative = expected_exits[terminal_index];
            if exits.is_empty() || !exits.contains(&representative) {
                return Err(StructureError::invalid(format!(
                    "condition payload #{index} is missing a frozen terminal edge"
                )));
            }
            let terminal_target = if terminal_index == 0 {
                ConditionTarget::Truthy
            } else {
                ConditionTarget::Falsy
            };
            let condition_id = ConditionPlanId(index);
            let representative_target = edge_index
                .terminal_endpoint(condition_id, representative)
                .filter(|_| {
                    edge_index.terminal_target(condition_id, representative)
                        == Some(terminal_target)
                })
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} terminal transfer has no physical endpoint"
                    ))
                })?;
            let representative_plan = plan.edge_plan(representative).ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{index} terminal edge has no plan"
                ))
            })?;
            for edge in exits {
                let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "condition payload #{index} terminal edge has no plan"
                    ))
                })?;
                if edge_index.terminal_endpoint(condition_id, *edge) != Some(representative_target)
                    || edge_plan.owner != representative_plan.owner
                    || edge_plan.transfer != representative_plan.transfer
                    || edge_plan.action_placement != representative_plan.action_placement
                    || edge_plan.phi_copies != representative_plan.phi_copies
                    || edge_plan.iteration != representative_plan.iteration
                    || plan.edge_action_is_forwarded_only(*edge)
                        != plan.edge_action_is_forwarded_only(representative)
                    || edge_plan.forward_route != representative_plan.forward_route
                        && (!forwarded_actions_are_empty(plan, edge_plan)
                            || !forwarded_actions_are_empty(plan, representative_plan))
                {
                    return Err(StructureError::invalid(format!(
                        "condition payload #{index} has inconsistent terminal edge actions: \
                         representative={representative:?}/{representative_plan:?}, \
                         edge={edge:?}/{edge_plan:?}"
                    )));
                }
            }
        }

        let mut stack = vec![condition.entry];
        while let Some(node) = stack.pop() {
            if std::mem::replace(&mut reachable[node.index()], true) {
                continue;
            }
            let node = &condition.nodes[node.index()];
            for target in [node.semantic_target(true), node.semantic_target(false)] {
                if let ConditionTarget::Node(target) = target {
                    stack.push(target);
                }
            }
        }
        if reachable.iter().any(|reachable| !reachable) {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} has unreachable DAG nodes"
            )));
        }

        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(index, degree)| (*degree == 0).then_some(index))
            .collect::<Vec<_>>();
        let mut visited = 0usize;
        while let Some(node_index) = ready.pop() {
            visited += 1;
            let node = &condition.nodes[node_index];
            for target in [node.semantic_target(true), node.semantic_target(false)] {
                let ConditionTarget::Node(target) = target else {
                    continue;
                };
                indegree[target.index()] -= 1;
                if indegree[target.index()] == 0 {
                    ready.push(target.index());
                }
            }
        }
        if visited != condition.nodes.len() {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} contains a cycle"
            )));
        }
        let header = condition.header().ok_or_else(|| {
            StructureError::invalid(format!("condition payload #{index} has no entry node"))
        })?;
        if condition
            .blocks()
            .any(|block| block != header && plan.label_for_block(block).is_some())
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{index} absorbs a labeled non-entry block"
            )));
        }
    }
    Ok(edge_index)
}

fn forwarded_actions_are_empty(plan: &StructurePlan, edge: &super::EdgePlan) -> bool {
    edge.forward_route
        .is_none_or(|route| plan.forward_route_action_edges(route).next().is_none())
}

fn validate_branch_plans(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    block_stats: &RegionBlockStats,
    condition_edges: &ConditionEdgeIndex,
) -> Result<(), StructureError> {
    let mut seen = vec![false; plan.branches.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let RegionPlan::Branch {
            plan: branch_id,
            entry,
            condition,
            continuation,
            ..
        } = region
        else {
            continue;
        };
        let payload = plan.branch(*branch_id).ok_or_else(|| {
            StructureError::invalid(format!("branch region #{index} has no payload"))
        })?;
        if seen[branch_id.index()] {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has conflicting region ownership",
                branch_id.index()
            )));
        }
        seen[branch_id.index()] = true;
        if payload.header != *entry || payload.continuation != *continuation {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has stale entry or continuation",
                branch_id.index()
            )));
        }
        let condition_id = payload.condition;

        let condition_plan = plan.condition(condition_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "branch payload #{} references a missing condition",
                branch_id.index()
            ))
        })?;
        if condition_plan.header() != Some(payload.header) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} condition has a stale header",
                branch_id.index()
            )));
        }
        let expected_condition_blocks = condition_plan.blocks().collect::<Vec<_>>();
        if !region_matches_exact_blocks(
            plan,
            intervals,
            block_stats,
            *condition,
            expected_condition_blocks.len(),
            expected_condition_blocks.iter().copied(),
        ) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} condition region has stale coverage",
                branch_id.index()
            )));
        }

        let (expected_then, expected_else) = if payload.condition_inverted {
            (condition_plan.falsy, condition_plan.truthy)
        } else {
            (condition_plan.truthy, condition_plan.falsy)
        };
        if (payload.then_edge, payload.else_edge) != (expected_then, expected_else) {
            return Err(StructureError::invalid(format!(
                "branch payload #{} has stale frozen edge polarity",
                branch_id.index()
            )));
        }
        for (edge, expected_arm) in [
            (
                payload.then_edge,
                Some(if payload.condition_inverted {
                    BranchArm::Falsy
                } else {
                    BranchArm::Truthy
                }),
            ),
            (
                payload.else_edge,
                Some(if payload.condition_inverted {
                    BranchArm::Truthy
                } else {
                    BranchArm::Falsy
                }),
            ),
        ] {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "branch payload #{} references a missing edge",
                    branch_id.index()
                ))
            })?;
            plan.edge_plan(edge).ok_or_else(|| {
                StructureError::invalid(format!(
                    "branch payload #{} edge has no plan",
                    branch_id.index()
                ))
            })?;
            if let Some(expected_arm) = expected_arm
                && condition_terminal_arm(condition_edges, payload.condition, edge)
                    != Some(expected_arm)
            {
                return Err(StructureError::invalid(format!(
                    "branch payload #{} edge {edge} contradicts its final condition arm",
                    branch_id.index()
                )));
            }
            if !region_contains_block(plan, intervals, *condition, cfg_edge.from) {
                return Err(StructureError::invalid(format!(
                    "branch payload #{} edge {edge} starts outside its condition region",
                    branch_id.index()
                )));
            }
        }
        if payload
            .value_plan
            .as_ref()
            .is_some_and(|value| Some(value.merge) != *continuation)
        {
            return Err(StructureError::invalid(format!(
                "branch payload #{} value merge has a stale continuation",
                branch_id.index()
            )));
        }
    }
    if seen.iter().any(|seen| !seen) {
        return Err(StructureError::invalid(
            "one or more branch payloads have no owning region",
        ));
    }
    Ok(())
}

struct LoopEdgeIndex {
    body: Vec<Option<LoopPlanId>>,
    exit: Vec<Option<LoopPlanId>>,
    backedge: Vec<Option<LoopPlanId>>,
    continue_: Vec<Option<LoopPlanId>>,
}

impl LoopEdgeIndex {
    fn new(plan: &StructurePlan, edge_count: usize) -> Result<Self, StructureError> {
        let mut index = Self {
            body: vec![None; edge_count],
            exit: vec![None; edge_count],
            backedge: vec![None; edge_count],
            continue_: vec![None; edge_count],
        };
        for (loop_index, payload) in plan.loops.iter().enumerate() {
            let loop_id = LoopPlanId(loop_index);
            for edge in payload
                .control_edges
                .preheader_body
                .iter()
                .chain(&payload.control_edges.body)
            {
                record_loop_edge(&mut index.body, *edge, loop_id, "body")?;
            }
            for edge in payload
                .control_edges
                .preheader_exit
                .iter()
                .chain(&payload.control_edges.exit)
            {
                record_loop_edge(&mut index.exit, *edge, loop_id, "exit")?;
            }
            for edge in &payload.control_edges.backedges {
                record_loop_edge(&mut index.backedge, *edge, loop_id, "backedge")?;
            }
            for edge in &payload.control_edges.continues {
                record_loop_edge(&mut index.continue_, *edge, loop_id, "continue")?;
            }
        }
        Ok(index)
    }

    fn has_body(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.body, loop_id, edge)
    }

    fn has_exit(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.exit, loop_id, edge)
    }

    fn has_backedge(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.backedge, loop_id, edge)
    }

    fn has_continue(&self, loop_id: LoopPlanId, edge: EdgeRef) -> bool {
        loop_edge_matches(&self.continue_, loop_id, edge)
    }
}

fn record_loop_edge(
    index: &mut [Option<LoopPlanId>],
    edge: EdgeRef,
    loop_id: LoopPlanId,
    role: &str,
) -> Result<(), StructureError> {
    let Some(slot) = index.get_mut(edge.index()) else {
        return Err(StructureError::invalid(format!(
            "loop payload #{} {role} edge is outside the CFG arena",
            loop_id.index()
        )));
    };
    if slot.is_some_and(|owner| owner != loop_id) {
        return Err(StructureError::invalid(format!(
            "edge {edge} has multiple loop {role} owners"
        )));
    }
    *slot = Some(loop_id);
    Ok(())
}

fn loop_edge_matches(index: &[Option<LoopPlanId>], loop_id: LoopPlanId, edge: EdgeRef) -> bool {
    index.get(edge.index()).copied().flatten() == Some(loop_id)
}

fn validate_loop_plans(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    block_stats: &RegionBlockStats,
) -> Result<LoopEdgeIndex, StructureError> {
    if plan.loop_region_by_plan.len() != plan.loops.len() {
        return Err(StructureError::invalid("loop region index length mismatch"));
    }
    if plan.loop_exit_tail_by_block.len() != cfg.blocks.len()
        || plan.loop_exit_tail_by_edge.len() != cfg.edges.len()
        || plan.loop_exit_tail_by_cleanup_instr.len() != cfg.instr_to_block.len()
    {
        return Err(StructureError::invalid(
            "loop exit tail reverse index length mismatch",
        ));
    }
    let loop_edges = LoopEdgeIndex::new(plan, cfg.edges.len())?;
    let mut break_edges_by_region = vec![Vec::new(); plan.regions.len()];
    for (edge_index, edge_plan) in plan.edge_plans.iter().enumerate() {
        if edge_plan.edge.index() != edge_index {
            return Err(StructureError::invalid(format!(
                "edge plan #{edge_index} has a stale identity while indexing loop exits"
            )));
        }
        if let EdgeTransfer::Break(region) = edge_plan.transfer {
            let Some(edges) = break_edges_by_region.get_mut(region.index()) else {
                return Err(StructureError::invalid(format!(
                    "edge plan #{edge_index} references a missing break region"
                )));
            };
            edges.push(edge_plan.edge);
        }
    }
    // 独立从最终 containment 与 transfer 重建 normal-tail guard 集合，不能信任
    // freeze 阶段保存的候选边。只有最内层当前 loop 的真实 Break 才会写 guard；
    // forwarding route 取最终 target，pad outgoing 自身不拥有动作。
    let mut nearest_loop = vec![None; plan.regions.len()];
    for region in intervals.preorder.iter().copied() {
        let inherited =
            intervals.parent[region.index()].and_then(|parent| nearest_loop[parent.index()]);
        nearest_loop[region.index()] =
            if matches!(plan.region(region), Some(RegionPlan::Loop { .. })) {
                Some(region)
            } else {
                inherited
            };
    }
    let mut expected_normal_tail_guards = vec![Vec::new(); plan.loops.len()];
    for edge_plan in &plan.edge_plans {
        let EdgeTransfer::Break(loop_region) = edge_plan.transfer else {
            continue;
        };
        let Some(RegionPlan::Loop { plan: loop_id, .. }) = plan.region(loop_region) else {
            continue;
        };
        let Some(tail) = plan
            .loop_(*loop_id)
            .and_then(|payload| payload.normal_tail.as_ref())
        else {
            continue;
        };
        let cfg_edge = cfg.edges.get(edge_plan.edge.index()).ok_or_else(|| {
            StructureError::invalid("normal-tail guard entry references a missing CFG edge")
        })?;
        let source = plan
            .region_for_block(cfg_edge.from)
            .ok_or_else(|| StructureError::invalid("normal-tail guard entry source is unowned"))?;
        if nearest_loop[source.index()] != Some(loop_region) {
            continue;
        }
        let target = edge_plan
            .forward_route
            .map(|route| {
                plan.forward_route(route)
                    .map(|route| route.target)
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "normal-tail guard entry references a missing forwarding route",
                        )
                    })
            })
            .transpose()?
            .unwrap_or(cfg_edge.to);
        if target == tail.continuation {
            expected_normal_tail_guards[loop_id.index()].push(edge_plan.edge);
        }
    }
    for entries in &mut expected_normal_tail_guards {
        entries.sort_by_key(|edge| edge.index());
        entries.dedup();
    }
    let mut seen = vec![false; plan.loops.len()];
    let mut syntax_edge_epoch = vec![0usize; cfg.edges.len()];
    let mut normal_exit_epoch = vec![0usize; cfg.edges.len()];
    let mut expected_tail_by_block = vec![None; cfg.blocks.len()];
    let mut expected_tail_by_edge = vec![None; cfg.edges.len()];
    let mut expected_tail_by_cleanup_instr = vec![None; cfg.instr_to_block.len()];
    for (index, region) in plan.regions.iter().enumerate() {
        let RegionPlan::Loop {
            plan: loop_id,
            entry,
            preheader,
            control,
            body,
            normal_tail,
            ..
        } = region
        else {
            continue;
        };
        let region_id = RegionId(index);
        let payload = plan.loop_(*loop_id).ok_or_else(|| {
            StructureError::invalid(format!("loop region #{index} has no payload"))
        })?;
        if seen[loop_id.index()] || plan.loop_region(*loop_id) != Some(region_id) {
            return Err(StructureError::invalid(format!(
                "loop payload #{} has conflicting region ownership",
                loop_id.index()
            )));
        }
        seen[loop_id.index()] = true;

        for child in preheader
            .iter()
            .copied()
            .chain([*control, *body])
            .chain(normal_tail.iter().copied())
        {
            if !matches!(plan.region(child), Some(RegionPlan::Sequence { parent: Some(parent), .. }) if *parent == region_id)
            {
                return Err(StructureError::invalid(format!(
                    "loop region #{index} partition is not an owned sequence"
                )));
            }
        }
        let partitions = preheader
            .iter()
            .copied()
            .chain([*control, *body])
            .chain(normal_tail.iter().copied())
            .collect::<BTreeSet<_>>();
        if partitions.len()
            != 2 + usize::from(preheader.is_some()) + usize::from(normal_tail.is_some())
        {
            return Err(StructureError::invalid(format!(
                "loop region #{index} reuses a partition region"
            )));
        }
        let expected_preheader_len = usize::from(payload.preheader_block.is_some());
        if preheader.is_some_and(|partition| {
            !region_matches_exact_blocks(
                plan,
                intervals,
                block_stats,
                partition,
                expected_preheader_len,
                payload.preheader_block,
            )
        }) || (preheader.is_none() && expected_preheader_len != 0)
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} preheader partition is stale",
                loop_id.index()
            )));
        }
        let preheader_count = preheader
            .map(|partition| block_stats.subtree_count(partition))
            .unwrap_or(0);
        let control_count = block_stats.subtree_count(*control);
        let normal_tail_count = normal_tail
            .map(|partition| block_stats.subtree_count(partition))
            .unwrap_or(0);
        let owned_count = block_stats.subtree_count(region_id);
        let body_count = block_stats.subtree_count(*body);
        let expected_body_count = owned_count
            .saturating_sub(control_count)
            .saturating_sub(preheader_count)
            .saturating_sub(normal_tail_count);
        if body_count != expected_body_count {
            return Err(StructureError::invalid(format!(
                "loop payload #{} body is not the remainder of its owned blocks",
                loop_id.index()
            )));
        }
        match (&payload.normal_tail, normal_tail) {
            (None, None) => {}
            (Some(tail), Some(tail_region)) => {
                if !matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::WhileLike
                        | crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) || payload.continuation != Some(tail.continuation)
                    || normal_tail_count == 0
                    || !region_contains_block(plan, intervals, *tail_region, tail.entry)
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has an invalid normal-tail partition",
                        loop_id.index()
                    )));
                }
                let entry_owner = plan.region_for_block(tail.entry).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} normal-tail entry is unowned",
                        loop_id.index()
                    ))
                })?;
                if !intervals.contains(*tail_region, entry_owner) {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} normal-tail entry is outside its partition",
                        loop_id.index()
                    )));
                }
                let boundary = intervals.boundary(*tail_region).ok_or_else(|| {
                    StructureError::invalid("normal-tail region has no boundary summary")
                })?;
                if tail.normal_exits.is_empty()
                    || tail
                        .normal_exits
                        .windows(2)
                        .any(|pair| pair[0].index() >= pair[1].index())
                    || boundary.entry_count != tail.normal_exits.len()
                    || boundary.exit_count != tail.completion_exits.len()
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has stale normal-tail boundary ports",
                        loop_id.index()
                    )));
                }
                for edge in &tail.normal_exits {
                    let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                        StructureError::invalid("normal-tail exit has no edge plan")
                    })?;
                    let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                        StructureError::invalid("normal-tail exit references a missing edge")
                    })?;
                    let syntax_exit_kind =
                        if payload.kind == crate::structure::LoopKindHint::WhileLike {
                            !matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        } else {
                            cfg_edge.kind == EdgeKind::LoopExit
                        };
                    let syntax_exit_transfer = match edge_plan.transfer {
                        EdgeTransfer::BranchArm(super::BranchArm::LoopExit) => true,
                        EdgeTransfer::Break(target) => target == region_id,
                        _ => false,
                    };
                    if !syntax_exit_kind
                        || cfg_edge.to != tail.entry
                        || region_contains_block(plan, intervals, *tail_region, cfg_edge.from)
                        || !syntax_exit_transfer
                    {
                        return Err(StructureError::invalid(format!(
                            "loop payload #{} normal-tail exit is stale",
                            loop_id.index()
                        )));
                    }
                }
                if tail.completion_exits.is_empty()
                    || tail
                        .completion_exits
                        .windows(2)
                        .any(|pair| pair[0].index() >= pair[1].index())
                {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} has invalid normal-tail completion exits",
                        loop_id.index()
                    )));
                }
                for edge in &tail.completion_exits {
                    let edge_plan = plan.edge_plan(*edge).ok_or_else(|| {
                        StructureError::invalid("normal-tail completion has no edge plan")
                    })?;
                    let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                        StructureError::invalid("normal-tail completion references a missing edge")
                    })?;
                    if edge_plan.edge != *edge
                        || cfg_edge.to != tail.continuation
                        || !region_contains_block(plan, intervals, *tail_region, cfg_edge.from)
                    {
                        return Err(StructureError::invalid(format!(
                            "loop payload #{} normal-tail completion is stale",
                            loop_id.index()
                        )));
                    }
                }
                if tail.early_exits != expected_normal_tail_guards[loop_id.index()] {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} normal-tail guard entries are stale: frozen={:?}, expected={:?}",
                        loop_id.index(),
                        tail.early_exits,
                        expected_normal_tail_guards[loop_id.index()],
                    )));
                }
            }
            _ => {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} normal-tail slot disagrees with its payload",
                    loop_id.index()
                )));
            }
        }
        if payload.normal_tail.is_some() && payload.exit_tail.is_some() {
            return Err(StructureError::invalid(format!(
                "loop payload #{} owns two normal-exit tail forms",
                loop_id.index()
            )));
        }
        if let Some(tail) = &payload.exit_tail {
            let Some(block_slot) = expected_tail_by_block.get_mut(tail.block.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} exit tail block is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if block_slot.replace(*loop_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} shares an exit-tail block",
                    loop_id.index()
                )));
            }
            let Some(edge_slot) = expected_tail_by_edge.get_mut(tail.normal_exit.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} exit-tail edge is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if edge_slot.replace(*loop_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} shares an exit-tail edge",
                    loop_id.index()
                )));
            }
            for instr in &tail.cleanup {
                let Some(cleanup_slot) = expected_tail_by_cleanup_instr.get_mut(instr.index())
                else {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} exit-tail cleanup is outside the instruction arena",
                        loop_id.index()
                    )));
                };
                if cleanup_slot.replace(*loop_id).is_some() {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} shares an exit-tail cleanup instruction",
                        loop_id.index()
                    )));
                }
            }
            let cfg_edge = cfg.edges.get(tail.normal_exit.index()).ok_or_else(|| {
                StructureError::invalid("loop exit tail references a missing normal edge")
            })?;
            let edge_plan = plan
                .edge_plan(tail.normal_exit)
                .ok_or_else(|| StructureError::invalid("loop exit tail normal edge has no plan"))?;
            let block_range = cfg
                .blocks
                .get(tail.block.index())
                .ok_or_else(|| {
                    StructureError::invalid("loop exit tail references a missing block")
                })?
                .instrs;
            let expected_early = break_edges_by_region[region_id.index()]
                .iter()
                .copied()
                .filter(|edge| *edge != tail.normal_exit)
                .collect::<Vec<_>>();
            let reachable_predecessors = cfg.preds[tail.block.index()]
                .iter()
                .copied()
                .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                .collect::<Vec<_>>();
            let cleanup_block_range = cfg
                .blocks
                .get(tail.cleanup_block.index())
                .map(|block| block.instrs);
            let cleanup_instrs_are_dense =
                tail.cleanup.iter().enumerate().all(|(offset, instr)| {
                    Some(tail.cleanup_block) == cfg.instr_to_block.get(instr.index()).copied()
                        && tail.cleanup.first().map(|first| first.index() + offset)
                            == Some(instr.index())
                });
            let cleanup_location_is_valid = if tail.cleanup_block == tail.block {
                tail.cleanup_route.is_empty()
                    && tail.cleanup.iter().all(|instr| {
                        instr.index() >= tail.range.start.index()
                            && instr.index() < tail.range.end()
                    })
            } else {
                let [route] = tail.cleanup_route.as_slice() else {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} cleanup route is not direct",
                        loop_id.index()
                    )));
                };
                let route_cfg = cfg.edges.get(route.index());
                let route_plan = plan.edge_plan(*route);
                let mut cleanup_predecessors = cfg.preds[tail.cleanup_block.index()]
                    .iter()
                    .copied()
                    .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                    .collect::<Vec<_>>();
                cleanup_predecessors.sort_by_key(|edge| edge.index());
                cfg.succs[tail.block.index()].as_slice() == [*route]
                    && route_cfg.is_some_and(|edge| {
                        edge.from == tail.block && edge.to == tail.cleanup_block
                    })
                    && route_plan.is_some_and(|edge| {
                        edge.transfer == EdgeTransfer::Fallthrough && edge.forward_route.is_none()
                    })
                    && cleanup_predecessors.as_slice() == [*route]
                    && cleanup_block_range
                        .is_some_and(|range| tail.cleanup.first() == Some(&range.start))
                    && block_range.last().map(|last| last.index()) == Some(tail.range.end())
                    && plan.label_for_block(tail.cleanup_block).is_none()
            };
            if payload.continuation != Some(tail.continuation)
                || tail.block != tail.continuation
                || cfg_edge.to != tail.block
                || edge_plan.owner != region_id
                || edge_plan.transfer != EdgeTransfer::Break(region_id)
                || edge_plan.forward_route.is_some()
                || !payload.control_edges.exit.contains(&tail.normal_exit)
                || tail.range.start != block_range.start
                || tail.range.is_empty()
                || tail.range.end() >= block_range.end()
                || reachable_predecessors.as_slice() != [tail.normal_exit]
                || tail.early_exits != expected_early
                || tail.early_exits.iter().any(|edge| {
                    cfg.edges
                        .get(edge.index())
                        .is_some_and(|edge| edge.to == tail.block)
                })
                || plan.label_for_block(tail.block).is_some()
                || tail.cleanup.is_empty()
                || tail.cleanup.windows(2).any(|pair| pair[0] >= pair[1])
                || !cleanup_instrs_are_dense
                || !cleanup_location_is_valid
            {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} has a stale instruction exit tail",
                    loop_id.index()
                )));
            }
            let tail_owner = plan
                .region_for_block(tail.block)
                .ok_or_else(|| StructureError::invalid("loop exit tail block is unowned"))?;
            if intervals.contains(region_id, tail_owner) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} instruction exit tail is still contained by the loop",
                    loop_id.index()
                )));
            }
        }
        let header_owner = plan.region_for_block(payload.header).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop payload #{} header is unowned",
                loop_id.index()
            ))
        })?;
        let header_partition = if intervals.contains(*control, header_owner) {
            *control
        } else {
            *body
        };
        if !intervals.contains(header_partition, header_owner) {
            return Err(StructureError::invalid(format!(
                "loop payload #{} header is outside its frozen partition",
                loop_id.index()
            )));
        }
        if matches!(
            payload.kind,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) && let Some(latch) = payload.continue_target
        {
            let latch_owner = plan.region_for_block(latch).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} VM latch is unowned",
                    loop_id.index()
                ))
            })?;
            if !intervals.contains(*control, latch_owner) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} VM latch is outside control",
                    loop_id.index()
                )));
            }
        }
        let entry_owner = plan.region_for_block(*entry).ok_or_else(|| {
            StructureError::invalid(format!("loop region #{index} entry is unowned"))
        })?;
        let expected_entry = payload.preheader_block.unwrap_or(payload.header);
        if *entry != expected_entry || preheader.is_some() != payload.preheader_block.is_some() {
            return Err(StructureError::invalid(format!(
                "loop region #{index} entry/preheader contract is stale"
            )));
        }
        let expected_entry_partition = preheader.unwrap_or(header_partition);
        if !intervals.contains(expected_entry_partition, entry_owner) {
            return Err(StructureError::invalid(format!(
                "loop region #{index} entry is outside its entry partition"
            )));
        }
        let requires_condition = matches!(
            payload.kind,
            crate::structure::LoopKindHint::WhileLike | crate::structure::LoopKindHint::RepeatLike
        ) || (payload.kind == crate::structure::LoopKindHint::Unknown
            && control_count != 0);
        if requires_condition && payload.condition.is_none() {
            return Err(StructureError::invalid(format!(
                "loop payload #{} is missing its frozen condition plan",
                loop_id.index()
            )));
        }
        if let Some(condition_id) = payload.condition {
            let condition = plan.condition(condition_id).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} references a missing condition",
                    loop_id.index()
                ))
            })?;
            for block in condition.blocks() {
                let owner = plan.region_for_block(block).ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} condition block {block} is unowned",
                        loop_id.index()
                    ))
                })?;
                if !intervals.contains(*control, owner) {
                    return Err(StructureError::invalid(format!(
                        "loop payload #{} condition block {block} is outside control",
                        loop_id.index()
                    )));
                }
            }
            let expected_condition_blocks = condition.blocks().collect::<Vec<_>>();
            if !region_matches_exact_blocks(
                plan,
                intervals,
                block_stats,
                *control,
                expected_condition_blocks.len(),
                expected_condition_blocks.iter().copied(),
            ) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} condition region has stale coverage",
                    loop_id.index()
                )));
            }
        }
        let condition_entry = payload
            .condition
            .and_then(|id| plan.condition(id))
            .and_then(ConditionPlan::header)
            .or(payload.condition_header)
            .or_else(|| {
                (payload.kind == crate::structure::LoopKindHint::RepeatLike)
                    .then_some(payload.continue_target)
                    .flatten()
            })
            .unwrap_or(payload.header);
        let expected_prefix_placement = (control_count != 0
            && matches!(
                payload.kind,
                crate::structure::LoopKindHint::WhileLike
                    | crate::structure::LoopKindHint::RepeatLike
                    | crate::structure::LoopKindHint::Unknown
            ))
        .then_some(
            if payload.kind == crate::structure::LoopKindHint::RepeatLike
                && condition_entry != payload.header
                && payload.control_edges.continues.is_empty()
            {
                crate::structure::LoopConditionPrefixPlacement::AfterBody
            } else {
                crate::structure::LoopConditionPrefixPlacement::BeforeBody
            },
        );
        if payload.condition_prefix_placement != expected_prefix_placement {
            return Err(StructureError::invalid(format!(
                "loop payload #{} condition prefix placement is stale",
                loop_id.index()
            )));
        }

        if payload
            .normalized_exit_aliases
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} normalized exits are not unique and sorted",
                loop_id.index()
            )));
        }
        for alias in &payload.normalized_exit_aliases {
            let alias_owner = plan.region_for_block(alias.block).ok_or_else(|| {
                StructureError::invalid("normalized loop exit alias block is unowned")
            })?;
            let continuation_owner =
                plan.region_for_block(alias.continuation).ok_or_else(|| {
                    StructureError::invalid("normalized loop exit continuation is unowned")
                })?;
            let alias_instr = cfg
                .blocks
                .get(alias.block.index())
                .map(|block| block.instrs.start)
                .ok_or_else(|| {
                    StructureError::invalid("normalized loop exit alias is outside the CFG")
                })?;
            let continuation_instr = cfg
                .blocks
                .get(alias.continuation.index())
                .map(|block| block.instrs.start)
                .ok_or_else(|| {
                    StructureError::invalid("normalized loop exit continuation is outside the CFG")
                })?;
            let alias_in_control = intervals.contains(*control, alias_owner);
            let continuation_in_loop = intervals.contains(region_id, continuation_owner);
            let has_exit_edge = payload.control_edges.exit.iter().any(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|edge| edge.to == alias.block)
            });
            let equivalent = super::super::helpers::equivalent_single_return_targets(
                proto,
                cfg,
                alias_instr,
                continuation_instr,
            );
            if !alias_in_control || continuation_in_loop || !has_exit_edge || !equivalent {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} has an invalid normalized exit alias {} -> {}: in-control={alias_in_control} continuation-in-loop={continuation_in_loop} exit-edge={has_exit_edge} equivalent={equivalent}",
                    loop_id.index(),
                    alias.block,
                    alias.continuation,
                )));
            }
        }

        let syntax_epoch = loop_id.index().checked_add(1).ok_or_else(|| {
            StructureError::invalid("loop count exceeds validation epoch capacity")
        })?;
        if let Some(tail) = &payload.normal_tail {
            for edge in &tail.normal_exits {
                let slot = normal_exit_epoch.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid("normal-tail exit is outside the CFG arena")
                })?;
                if std::mem::replace(slot, syntax_epoch) == syntax_epoch {
                    return Err(StructureError::invalid(
                        "normal-tail exit is listed more than once",
                    ));
                }
            }
        }
        for (edge, role) in payload
            .control_edges
            .preheader_body
            .map(|edge| (edge, "preheader body"))
            .into_iter()
            .chain(
                payload
                    .control_edges
                    .preheader_exit
                    .map(|edge| (edge, "preheader exit")),
            )
            .chain(
                payload
                    .control_edges
                    .body
                    .iter()
                    .copied()
                    .map(|edge| (edge, "control body")),
            )
            .chain(
                payload
                    .control_edges
                    .exit
                    .iter()
                    .copied()
                    .map(|edge| (edge, "control exit")),
            )
        {
            let Some(edge_epoch) = syntax_edge_epoch.get_mut(edge.index()) else {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {role} edge is outside the CFG arena",
                    loop_id.index()
                )));
            };
            if std::mem::replace(edge_epoch, syntax_epoch) == syntax_epoch {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} assigns edge {edge} multiple syntax roles",
                    loop_id.index()
                )));
            }
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} {role} edge is missing",
                    loop_id.index()
                ))
            })?;
            let source = plan.region_for_block(cfg_edge.from).ok_or_else(|| {
                StructureError::invalid(format!(
                    "loop payload #{} {role} source is unowned",
                    loop_id.index()
                ))
            })?;
            let source_partition = if role.starts_with("preheader") {
                preheader.ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop payload #{} has a preheader edge without a preheader region",
                        loop_id.index()
                    ))
                })?
            } else {
                *control
            };
            if !intervals.contains(source_partition, source) {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {:?} header {} {role} edge {edge} source {} owner {:?} ({:?}) is outside partition {:?}",
                    loop_id.index(),
                    payload.kind,
                    payload.header,
                    cfg_edge.from,
                    source,
                    plan.region(source),
                    source_partition,
                )));
            }
            let target_inside = plan
                .region_for_block(cfg_edge.to)
                .is_some_and(|target| intervals.contains(region_id, target));
            let immediate_break_body = role == "control body"
                && payload.kind == crate::structure::LoopKindHint::GenericForLike
                && matches!(
                    cfg.terminator(&proto.instrs, payload.header),
                    Some(LowInstr::GenericForLoop(instr))
                        if super::super::helpers::same_or_transparent_jump_target(
                            proto,
                            cfg,
                            instr.exit_target,
                            instr.body_target,
                        )
                );
            let expects_inside = role.ends_with("body") && !immediate_break_body
                || normal_exit_epoch[edge.index()] == syntax_epoch;
            let normalized_exit = role == "control exit"
                && payload
                    .normalized_exit_aliases
                    .iter()
                    .any(|alias| alias.block == cfg_edge.to);
            if (target_inside && !normalized_exit) != expects_inside {
                return Err(StructureError::invalid(format!(
                    "loop payload #{} {role} edge crosses the wrong boundary",
                    loop_id.index()
                )));
            }
        }
    }
    validate_propagated_breaks(cfg, plan, intervals, &nearest_loop)?;
    if seen.into_iter().any(|seen| !seen) {
        return Err(StructureError::invalid(
            "selected loop payload has no owning region",
        ));
    }
    if expected_tail_by_block != plan.loop_exit_tail_by_block {
        return Err(StructureError::invalid(
            "loop exit tail block reverse index is stale",
        ));
    }
    if expected_tail_by_edge != plan.loop_exit_tail_by_edge {
        return Err(StructureError::invalid(
            "loop exit tail edge reverse index is stale",
        ));
    }
    if expected_tail_by_cleanup_instr != plan.loop_exit_tail_by_cleanup_instr {
        return Err(StructureError::invalid(
            "loop exit tail cleanup reverse index is stale",
        ));
    }
    Ok(loop_edges)
}

fn validate_propagated_breaks(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    nearest_loop: &[Option<RegionId>],
) -> Result<(), StructureError> {
    let mut target_by_region = vec![None; plan.regions.len()];
    let mut continuation_by_region = vec![None; plan.regions.len()];
    for (loop_index, payload) in plan.loops.iter().enumerate() {
        let Some(target) = payload.propagated_break else {
            continue;
        };
        let source = plan
            .loop_region(super::LoopPlanId(loop_index))
            .ok_or_else(|| StructureError::invalid("propagated break source has no loop region"))?;
        let Some(RegionPlan::Loop {
            plan: target_plan, ..
        }) = plan.region(target)
        else {
            return Err(StructureError::invalid(
                "propagated break targets a non-loop region",
            ));
        };
        if target == source || !intervals.contains(target, source) {
            return Err(StructureError::invalid(
                "propagated break target does not contain its source loop",
            ));
        }
        if matches!(
            payload.kind,
            crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::GenericForLike
        ) {
            for edge in payload
                .control_edges
                .preheader_exit
                .into_iter()
                .chain(payload.control_edges.exit.iter().copied())
            {
                let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
                    StructureError::invalid("VM-for propagated break syntax exit has no edge plan")
                })?;
                if edge_plan.transfer != EdgeTransfer::BranchArm(BranchArm::LoopExit) {
                    return Err(StructureError::invalid(format!(
                        "VM-for propagated break edge {edge} has edge/completion double ownership: {:?}",
                        edge_plan.transfer
                    )));
                }
            }
        }
        target_by_region[source.index()] = Some(target);
        continuation_by_region[source.index()] = plan
            .loop_(*target_plan)
            .and_then(|loop_| loop_.continuation);
    }

    // 只记录每个 region 最近的传播 loop。若一条 edge 没有离开它，就必然也没有
    // 离开更外层的传播 loop；若离开了，transfer 对最近 owner 的证明可沿相同 target
    // 链向祖先复用。这样无需为每个 loop 重扫整张 CFG。
    let mut nearest_propagated = vec![None; plan.regions.len()];
    for region in intervals.preorder.iter().copied() {
        let inherited =
            intervals.parent[region.index()].and_then(|parent| nearest_propagated[parent.index()]);
        nearest_propagated[region.index()] = if target_by_region[region.index()].is_some() {
            Some(region)
        } else {
            inherited
        };
    }

    // 跨过多个源码 loop 的 break 需要每个中间 loop 在完成后继续传播；否则一个
    // Lua `break` 只能退出最内层。该链只沿 loop-parent 检查一次。
    for source in intervals.preorder.iter().copied() {
        let Some(target) = target_by_region[source.index()] else {
            continue;
        };
        let parent_loop = intervals.parent[source.index()]
            .and_then(|parent| nearest_loop[parent.index()])
            .ok_or_else(|| {
                StructureError::invalid("propagated break source has no containing loop")
            })?;
        if parent_loop != target && target_by_region[parent_loop.index()] != Some(target) {
            return Err(StructureError::invalid(
                "propagated break chain changes target before reaching its owner",
            ));
        }
    }

    let mut completing_exit = vec![false; plan.regions.len()];
    for (index, (edge, edge_plan)) in cfg.edges.iter().zip(&plan.edge_plans).enumerate() {
        if matches!(
            edge_plan.transfer,
            EdgeTransfer::Return | EdgeTransfer::TailCall | EdgeTransfer::Unreachable
        ) {
            continue;
        }
        let source_owner = plan.region_for_block(edge.from).ok_or_else(|| {
            StructureError::invalid(format!("propagated break edge #{index} source is unowned"))
        })?;
        let Some(source_loop) = nearest_propagated[source_owner.index()] else {
            continue;
        };
        if plan
            .region_for_block(edge.to)
            .is_some_and(|target_owner| intervals.contains(source_loop, target_owner))
        {
            continue;
        }
        let target = target_by_region[source_loop.index()]
            .ok_or_else(|| StructureError::invalid("propagated break index is sparse"))?;
        let valid = matches!(edge_plan.transfer, EdgeTransfer::Break(owner) if owner == target)
            || edge_plan.transfer == EdgeTransfer::BranchArm(BranchArm::LoopExit)
                && Some(edge.to) == continuation_by_region[source_loop.index()];
        if !valid {
            return Err(StructureError::invalid(format!(
                "loop #{} propagated break has a non-propagating exit edge #{index}",
                source_loop.index()
            )));
        }
        completing_exit[source_loop.index()] = true;
    }

    // 内层完成会执行计划中的下一层 break；逆 preorder 把该完成事实沿同 target
    // 的连续传播链汇总，仍然只访问每个 region 一次。
    for source in intervals.preorder.iter().copied().rev() {
        let Some(target) = target_by_region[source.index()] else {
            continue;
        };
        if !completing_exit[source.index()] {
            return Err(StructureError::invalid(
                "propagated break loop has no completing exit",
            ));
        }
        let parent_loop =
            intervals.parent[source.index()].and_then(|parent| nearest_loop[parent.index()]);
        if let Some(parent) = parent_loop
            && target_by_region[parent.index()] == Some(target)
        {
            completing_exit[parent.index()] = true;
        }
    }
    Ok(())
}

struct EdgeValidationIndex {
    continue_barriers: Vec<bool>,
    break_barriers: Vec<bool>,
}

impl EdgeValidationIndex {
    fn new(cfg: &Cfg, plan: &StructurePlan) -> Self {
        let mut continue_barriers = vec![false; cfg.blocks.len()];
        let mut break_barriers = vec![false; cfg.blocks.len()];
        for scope in &plan.scopes {
            mark_block(&mut continue_barriers, scope.entry);
            mark_block(&mut break_barriers, scope.entry);
            if let Some(exit) = scope.exit {
                mark_block(&mut continue_barriers, exit);
                mark_block(&mut break_barriers, exit);
            }
            for close in &scope.close_points {
                if let Some(block) = cfg.instr_to_block.get(close.index()).copied() {
                    mark_block(&mut continue_barriers, block);
                }
            }
        }
        for (_, label) in plan.labels() {
            mark_block(&mut continue_barriers, label.block);
            mark_block(&mut break_barriers, label.block);
        }

        Self {
            continue_barriers,
            break_barriers,
        }
    }
}

fn mark_block(index: &mut [bool], block: BlockRef) {
    if let Some(slot) = index.get_mut(block.index()) {
        *slot = true;
    }
}

fn validate_edges(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    edge_regions: &RegionNavigation,
    condition_edges: &ConditionEdgeIndex,
    loop_edges: &LoopEdgeIndex,
) -> Result<(), StructureError> {
    if plan.edge_plans.len() != cfg.edges.len() {
        return Err(StructureError::invalid("edge plan length mismatch"));
    }
    let layout_edges = super::arena::layout_edge_facts(cfg, &plan.regions, &plan.navigation)?;
    let validation_index = EdgeValidationIndex::new(cfg, plan);
    validate_forward_routes(cfg, plan, intervals, condition_edges, &validation_index)?;
    for (index, edge_plan) in plan.edge_plans.iter().enumerate() {
        if edge_plan.edge.index() != index || edge_plan.owner.index() >= plan.regions.len() {
            return Err(StructureError::invalid(format!(
                "edge plan #{index} has invalid identity or owner"
            )));
        }
        let edge = cfg.edges[index];
        match edge_plan.action_placement {
            EdgeActionPlacement::BeforeTransfer => {}
            EdgeActionPlacement::BeforeTrailingCleanup { cleanup } => {
                let block_range = cfg
                    .blocks
                    .get(edge.from.index())
                    .ok_or_else(|| {
                        StructureError::invalid(format!(
                            "edge #{index} action placement source block is missing"
                        ))
                    })?
                    .instrs;
                if !matches!(edge_plan.transfer, EdgeTransfer::LoopBack(_))
                    || edge_plan.forward_route.is_some()
                    || cfg.succs.get(edge.from.index()).map(Vec::as_slice)
                        != Some(&[edge_plan.edge])
                    || cleanup.is_empty()
                    || cleanup.start.index() <= block_range.start.index()
                    || block_range.last().map(|last| last.index()) != Some(cleanup.end())
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} has a stale trailing-cleanup action placement"
                    )));
                }
            }
        }
        if !cfg.reachable_blocks.contains(&edge.from)
            && !matches!(edge_plan.transfer, EdgeTransfer::Unreachable)
        {
            return Err(StructureError::invalid(format!(
                "unreachable edge #{index} has executable transfer"
            )));
        }
        if !matches!(
            edge_plan.transfer,
            EdgeTransfer::Break(_) | EdgeTransfer::Continue(_)
        ) && edge_plan.forward_route.is_some()
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} has a forwarding route without loop control transfer"
            )));
        }
        if edge_plan.transfer == EdgeTransfer::Fallthrough {
            let source = plan.region_for_block(edge.from).ok_or_else(|| {
                StructureError::invalid(format!("edge #{index} source has no region"))
            })?;
            let target = plan.region_for_block(edge.to).ok_or_else(|| {
                StructureError::invalid(format!("edge #{index} target has no region"))
            })?;
            edge_regions
                .edge_relation(edge_plan.edge)
                .and_then(|relation| relation.lca)
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "edge #{index} has no containment owner while validating fallthrough"
                    ))
                })?;
            if let Some(source_child) = edge_regions
                .edge_relation(edge_plan.edge)
                .and_then(|relation| relation.source_child)
                && matches!(
                    plan.region(source_child),
                    Some(RegionPlan::Unstructured { .. })
                )
                && !intervals.contains(source_child, target)
                && !plan
                    .navigation
                    .region_can_complete_from(source_child, source, edge.from)
            {
                return Err(StructureError::invalid(format!(
                    "edge #{index} falls through from a non-final island layout item"
                )));
            }
        }
        let island_for_syntax_edge = match (edge_plan.transfer, plan.region(edge_plan.owner)) {
            (
                EdgeTransfer::BranchArm(BranchArm::LoopBody),
                Some(RegionPlan::Loop { plan: loop_id, .. }),
            ) => plan.loop_(*loop_id).is_some_and(|payload| {
                matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) && loop_edges.has_body(*loop_id, edge_plan.edge)
            }),
            (
                EdgeTransfer::BranchArm(BranchArm::LoopExit),
                Some(RegionPlan::Loop { plan: loop_id, .. }),
            ) => plan.loop_(*loop_id).is_some_and(|payload| {
                matches!(
                    payload.kind,
                    crate::structure::LoopKindHint::NumericForLike
                        | crate::structure::LoopKindHint::GenericForLike
                ) && loop_edges.has_exit(*loop_id, edge_plan.edge)
            }),
            _ => false,
        };
        if layout_edges[index].crosses_island_layout
            && !layout_edges[index].natural
            && !island_for_syntax_edge
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough | EdgeTransfer::BranchArm(_)
            )
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} crosses a non-completing island layout item without an explicit transfer"
            )));
        }
        match edge_plan.transfer {
            EdgeTransfer::Return
                if edge.kind != EdgeKind::Return
                    && shared_pure_terminal_kind(cfg, edge.to) != Some(EdgeKind::Return) =>
            {
                return Err(StructureError::invalid("return transfer kind mismatch"));
            }
            EdgeTransfer::TailCall
                if edge.kind != EdgeKind::TailCall
                    && shared_pure_terminal_kind(cfg, edge.to) != Some(EdgeKind::TailCall) =>
            {
                return Err(StructureError::invalid("tail-call transfer kind mismatch"));
            }
            EdgeTransfer::Goto(label, _)
                if plan.label(label).map(|label| label.block) != Some(edge.to) =>
            {
                return Err(StructureError::invalid(
                    "goto label differs from edge target",
                ));
            }
            EdgeTransfer::Break(region)
                if let Some((_, fence)) = plan.single_pass_for_region(region) =>
            {
                let source = plan.region_for_block(edge.from).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} source has no region"))
                })?;
                if edge_plan.owner != region
                    || !intervals.contains(region, source)
                    || edge.to != fence.continuation
                    || edge_plan.forward_route.is_some()
                    || fence.escape_edges.binary_search(&edge_plan.edge).is_err()
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} does not match single-pass region #{}",
                        region.index()
                    )));
                }
            }
            EdgeTransfer::LoopBack(region)
            | EdgeTransfer::Break(region)
            | EdgeTransfer::Continue(region) => {
                let Some(RegionPlan::Loop {
                    plan: loop_id,
                    body,
                    ..
                }) = plan.region(region)
                else {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} references a non-loop control owner"
                    )));
                };
                let loop_ = plan.loop_(*loop_id).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} loop payload is missing"))
                })?;
                let source = plan.region_for_block(edge.from).ok_or_else(|| {
                    StructureError::invalid(format!("edge #{index} source has no region"))
                })?;
                if !intervals.contains(region, source) {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} {} -> {} {:?} loop region #{} does not contain source owner #{} ({:?})",
                        edge.from,
                        edge.to,
                        edge_plan.transfer,
                        region.index(),
                        source.index(),
                        plan.region(source),
                    )));
                }
                if matches!(edge_plan.transfer, EdgeTransfer::Break(_))
                    && !intervals.contains(*body, source)
                    && !loop_edges.has_exit(*loop_id, edge_plan.edge)
                {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} break source is outside the loop body/control exit"
                    )));
                }
                let semantic_match = match edge_plan.transfer {
                    EdgeTransfer::LoopBack(_) => loop_edges.has_backedge(*loop_id, edge_plan.edge),
                    EdgeTransfer::Continue(_) => {
                        loop_edges.has_continue(*loop_id, edge_plan.edge)
                            && (loop_.continue_target == Some(edge.to)
                                && edge_plan.forward_route.is_none()
                                || validate_continue_forwarding_route(
                                    cfg, plan, edge_plan, region,
                                )?)
                    }
                    EdgeTransfer::Break(_) => {
                        loop_.continuation == Some(edge.to) && edge_plan.forward_route.is_none()
                            || validate_break_forwarding_route(
                                cfg,
                                plan,
                                intervals,
                                edge_plan,
                                region,
                                loop_.continuation,
                                &validation_index,
                            )?
                    }
                    _ => false,
                };
                // 内层源码 loop 的 VM exit 可以同时承担祖先 loop 的 break。例如
                // generic-for 正常耗尽后直接离开包裹它的 while：该 CFG edge 必须由
                // 内层 loop 消费协议/phi，却要在源码 loop 之后发射外层 break。
                // ownership 因而仍属于内层 syntax region，transfer target 才是祖先。
                let nested_syntax_exit = matches!(edge_plan.transfer, EdgeTransfer::Break(_))
                    && edge_plan.owner != region
                    && intervals.contains(region, edge_plan.owner)
                    && matches!(
                        plan.region(edge_plan.owner),
                        Some(RegionPlan::Loop {
                            plan: owner_loop, ..
                        }) if loop_edges.has_exit(*owner_loop, edge_plan.edge)
                    );
                if !semantic_match || edge_plan.owner != region && !nested_syntax_exit {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} {} -> {} {:?} does not match loop #{} payload: backedges={:?}, continues={:?}, forwarded={:?}, continue_target={:?}, continuation={:?}",
                        edge.from,
                        edge.to,
                        edge_plan.transfer,
                        loop_id.index(),
                        loop_.control_edges.backedges,
                        loop_.control_edges.continues,
                        edge_plan.forward_route,
                        loop_.continue_target,
                        loop_.continuation,
                    )));
                }
            }
            EdgeTransfer::BranchArm(arm) => {
                let valid = match plan.region(edge_plan.owner) {
                    Some(RegionPlan::Branch {
                        plan: branch_id, ..
                    }) => plan.branch(*branch_id).is_some_and(|branch| {
                        let condition_target = condition_edges
                            .first_target(branch.condition, edge_plan.edge)
                            .or_else(|| {
                                condition_edges.terminal_target(branch.condition, edge_plan.edge)
                            });
                        matches!(
                            (condition_target, arm),
                            (Some(ConditionTarget::Truthy), BranchArm::Truthy)
                                | (Some(ConditionTarget::Falsy), BranchArm::Falsy)
                                | (
                                    Some(ConditionTarget::Node(_)),
                                    BranchArm::Truthy | BranchArm::Falsy
                                )
                        )
                    }),
                    Some(RegionPlan::Loop { plan: loop_id, .. }) => {
                        plan.loop_(*loop_id).is_some_and(|loop_| {
                            let condition_target = loop_.condition.and_then(|condition| {
                                condition_edges
                                    .first_target(condition, edge_plan.edge)
                                    .or_else(|| {
                                        condition_edges.terminal_target(condition, edge_plan.edge)
                                    })
                            });
                            match arm {
                                BranchArm::LoopBody => {
                                    loop_edges.has_body(*loop_id, edge_plan.edge)
                                        || loop_.control_edges.preheader_body
                                            == Some(edge_plan.edge)
                                }
                                BranchArm::LoopExit => {
                                    loop_edges.has_exit(*loop_id, edge_plan.edge)
                                        || loop_.control_edges.preheader_exit
                                            == Some(edge_plan.edge)
                                }
                                BranchArm::Truthy => {
                                    matches!(
                                        condition_target,
                                        Some(ConditionTarget::Truthy | ConditionTarget::Node(_))
                                    ) || condition_target.is_none()
                                        && loop_.header == edge.from
                                        && edge.kind == EdgeKind::BranchTrue
                                }
                                BranchArm::Falsy => {
                                    matches!(
                                        condition_target,
                                        Some(ConditionTarget::Falsy | ConditionTarget::Node(_))
                                    ) || condition_target.is_none()
                                        && loop_.header == edge.from
                                        && edge.kind == EdgeKind::BranchFalse
                                }
                            }
                        })
                    }
                    _ => false,
                };
                if !valid {
                    return Err(StructureError::invalid(format!(
                        "edge #{index} branch arm {arm:?} lacks a matching structured header: \
                         owner={:?}, cfg={} -> {} {:?}",
                        edge_plan.owner, edge.from, edge.to, edge.kind,
                    )));
                }
            }
            EdgeTransfer::Unreachable
            | EdgeTransfer::Fallthrough
            | EdgeTransfer::Return
            | EdgeTransfer::TailCall
            | EdgeTransfer::Goto(_, _) => {}
        }
    }
    Ok(())
}

fn condition_terminal_arm(
    condition_edges: &ConditionEdgeIndex,
    condition: ConditionPlanId,
    edge: EdgeRef,
) -> Option<BranchArm> {
    match condition_edges.terminal_target(condition, edge)? {
        ConditionTarget::Truthy => Some(BranchArm::Truthy),
        ConditionTarget::Falsy => Some(BranchArm::Falsy),
        ConditionTarget::Node(_) => None,
    }
}

fn validate_condition_internal_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    condition_index: usize,
    node_index: usize,
    arc: &super::ConditionArcPlan,
) -> Result<(), StructureError> {
    let transfer_position = arc
        .route
        .iter()
        .position(|edge| *edge == arc.transfer)
        .ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} transfer is outside its route"
            ))
        })?;
    let internal_len = match arc.target {
        ConditionTarget::Node(_) => {
            if transfer_position + 1 != arc.route.len() {
                return Err(StructureError::invalid(format!(
                    "condition payload #{condition_index} node {node_index} has an executable transfer before another condition node"
                )));
            }
            arc.route.len()
        }
        ConditionTarget::Truthy | ConditionTarget::Falsy => transfer_position,
    };
    for (position, edge) in arc.route.iter().copied().take(internal_len).enumerate() {
        let edge_plan = plan.edge_plan(edge).ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} route edge has no final plan"
            ))
        })?;
        if !edge_plan.phi_copies.is_empty()
            || edge_plan.actions_before_trailing_cleanup().is_some()
            || !matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough
                    | EdgeTransfer::BranchArm(BranchArm::Truthy | BranchArm::Falsy)
            )
        {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} route edge {edge} at step {position} has unconsumed actions: {edge_plan:?}"
            )));
        }
        let Some(cfg_edge) = cfg.edges.get(edge.index()) else {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} route references a missing CFG edge"
            )));
        };
        if cfg_edge.from == cfg_edge.to {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} node {node_index} route loops in place"
            )));
        }
    }
    if matches!(arc.target, ConditionTarget::Truthy | ConditionTarget::Falsy)
        && transfer_position + 1 < arc.route.len()
    {
        let edge_plan = plan.edge_plan(arc.transfer).ok_or_else(|| {
            StructureError::invalid(format!(
                "condition payload #{condition_index} transfer edge has no final plan"
            ))
        })?;
        let route = edge_plan
            .forward_route
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "condition payload #{condition_index} transfer does not own its physical route suffix"
                ))
            })
            .map(|route| plan.forward_route_edges(route).collect::<Vec<_>>())?;
        // `forward_route` 绑定在语义 transfer edge 上，但 route 本身从该 edge 的
        // target 开始，因此只覆盖 condition arc 中 transfer 之后的物理后缀。
        if route.as_slice() != &arc.route[transfer_position + 1..] {
            return Err(StructureError::invalid(format!(
                "condition payload #{condition_index} transfer route suffix is stale"
            )));
        }
    }
    Ok(())
}

fn validate_forward_routes(
    cfg: &Cfg,
    plan: &StructurePlan,
    intervals: &RegionNavigation,
    _condition_edges: &ConditionEdgeIndex,
    index: &EdgeValidationIndex,
) -> Result<(), StructureError> {
    let edge_count = cfg.edges.len();
    if plan.forward_next.len() != edge_count
        || plan.forward_preorder.len() != edge_count
        || plan.forward_subtree_end.len() != edge_count
        || plan.forward_depth.len() != edge_count
        || plan.forward_owner_by_edge.len() != edge_count
        || plan.forward_kind_by_edge.len() != edge_count
    {
        return Err(StructureError::invalid(
            "forward route dense index length mismatch",
        ));
    }

    let mut entry_count = vec![0usize; plan.forward_routes.len()];
    let mut entry_by_route = vec![None; plan.forward_routes.len()];
    for edge_plan in &plan.edge_plans {
        let Some(route_id) = edge_plan.forward_route else {
            continue;
        };
        let route = plan.forward_route(route_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "{} references missing forward route #{}",
                edge_plan.edge,
                route_id.index()
            ))
        })?;
        if edge_plan.owner != route.loop_region
            || !matches!(
                (edge_plan.transfer, route.kind),
                (EdgeTransfer::Break(owner), ForwardRouteKind::ExclusiveBreak)
                    | (EdgeTransfer::Continue(owner), ForwardRouteKind::ContinueToTarget)
                    | (EdgeTransfer::Continue(owner), ForwardRouteKind::ContinueLatch)
                    | (
                        EdgeTransfer::Continue(owner),
                        ForwardRouteKind::RepeatConditionArc(_)
                    ) if owner == route.loop_region
            )
        {
            return Err(StructureError::invalid(format!(
                "{} has a forwarding route inconsistent with its transfer",
                edge_plan.edge
            )));
        }
        if cfg.edges.get(edge_plan.edge.index()).map(|edge| edge.to) != Some(route.start) {
            return Err(StructureError::invalid(format!(
                "{} does not enter the start of forward route #{}",
                edge_plan.edge,
                route_id.index()
            )));
        }
        entry_count[route_id.index()] = entry_count[route_id.index()]
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forward route entry count overflow"))?;
        entry_by_route[route_id.index()] = Some(edge_plan.edge);
    }

    let mut first_route = vec![None; edge_count];
    let mut is_route_last = vec![false; edge_count];
    for (route_id, route) in plan.forward_routes() {
        if entry_count[route_id.index()] == 0 {
            return Err(StructureError::invalid(format!(
                "forward route #{} has no bound entry",
                route_id.index()
            )));
        }
        if route.kind == ForwardRouteKind::ExclusiveBreak && entry_count[route_id.index()] != 1 {
            return Err(StructureError::invalid(format!(
                "exclusive break route #{} has multiple entries",
                route_id.index()
            )));
        }
        if route.len == 0
            || route.first.index() >= edge_count
            || route.last.index() >= edge_count
            || cfg.edges[route.first.index()].from != route.start
            || cfg.edges[route.last.index()].to != route.target
            || !plan.forward_route_contains_edge(route_id, route.last)
            || plan.forward_depth[route.first.index()]
                .checked_sub(plan.forward_depth[route.last.index()])
                .and_then(|distance| distance.checked_add(1))
                != Some(route.len)
        {
            return Err(StructureError::invalid(format!(
                "forward route #{} has stale endpoints or length",
                route_id.index()
            )));
        }
        if first_route[route.first.index()]
            .replace(route_id)
            .is_some_and(|old| old != route_id)
        {
            return Err(StructureError::invalid(
                "forward routes with different identities share a first edge",
            ));
        }
        is_route_last[route.last.index()] = true;
        let Some(RegionPlan::Loop {
            plan: loop_id,
            control,
            body,
            ..
        }) = plan.region(route.loop_region)
        else {
            return Err(StructureError::invalid(format!(
                "forward route #{} has a non-loop owner",
                route_id.index()
            )));
        };
        let payload = plan.loop_(*loop_id).ok_or_else(|| {
            StructureError::invalid(format!(
                "forward route #{} loop payload is missing",
                route_id.index()
            ))
        })?;
        let metadata_matches = match route.kind {
            ForwardRouteKind::ExclusiveBreak => payload.continuation == Some(route.target),
            ForwardRouteKind::ContinueToTarget => payload.continue_target == Some(route.target),
            ForwardRouteKind::ContinueLatch => {
                payload.continue_target == Some(route.start) && payload.header == route.target
            }
            ForwardRouteKind::RepeatConditionArc(arc_ref) => {
                let arc = plan
                    .condition(arc_ref.condition)
                    .and_then(|condition| condition.nodes.get(arc_ref.node.index()))
                    .map(|node| node.arc(arc_ref.polarity));
                payload.kind == crate::structure::LoopKindHint::RepeatLike
                    && payload.condition == Some(arc_ref.condition)
                    && payload.header == route.target
                    && arc.is_some_and(|arc| {
                        let Some(first) = arc.route.first().copied() else {
                            return false;
                        };
                        arc.route.last() == Some(&route.last)
                            && cfg.edges.get(first.index()).map(|edge| edge.from)
                                == payload.continue_target
                            && plan.forward_route_contains_edge(route_id, first)
                            && plan.forward_depth[first.index()]
                                .checked_sub(plan.forward_depth[route.last.index()])
                                .and_then(|distance| distance.checked_add(1))
                                == Some(arc.route.len())
                    })
            }
        };
        if !metadata_matches {
            return Err(StructureError::invalid(format!(
                "forward route #{} {:?} #{} -> #{} contradicts loop payload {:?}: condition={:?} header=#{} continue={:?} continuation={:?}",
                route_id.index(),
                route.kind,
                route.start.index(),
                route.target.index(),
                payload.kind,
                payload.condition,
                payload.header.index(),
                payload.continue_target,
                payload.continuation,
            )));
        }
        let entry = entry_by_route[route_id.index()];
        if route.kind == ForwardRouteKind::ExclusiveBreak
            && entry.is_none_or(|entry| {
                plan.region_for_block(cfg.edges[entry.index()].from)
                    .is_none_or(|source| !intervals.contains(route.loop_region, source))
            })
        {
            return Err(StructureError::invalid(format!(
                "exclusive break route #{} starts outside its loop",
                route_id.index()
            )));
        }
        let _ = (control, body);
    }

    let mut route_predecessor = vec![None; edge_count];
    let mut route_predecessor_count = vec![0usize; edge_count];
    for (edge_index, next) in plan.forward_next.iter().copied().enumerate() {
        let edge = EdgeRef(edge_index);
        let assigned = plan.forward_preorder[edge_index] != usize::MAX;
        if assigned
            != (plan.forward_subtree_end[edge_index] != usize::MAX
                && plan.forward_depth[edge_index] != usize::MAX
                && plan.forward_owner_by_edge[edge_index].is_some()
                && plan.forward_kind_by_edge[edge_index].is_some())
        {
            return Err(StructureError::invalid(format!(
                "{edge} has inconsistent forward route indexes"
            )));
        }
        if !assigned {
            if next.is_some() {
                return Err(StructureError::invalid(format!(
                    "unowned {edge} has a forwarding successor"
                )));
            }
            continue;
        }
        if plan.forward_subtree_end[edge_index] <= plan.forward_preorder[edge_index] {
            return Err(StructureError::invalid(format!(
                "{edge} has an invalid forwarding interval"
            )));
        }
        if let Some(next) = next {
            let next_cfg = cfg.edges.get(next.index()).ok_or_else(|| {
                StructureError::invalid(format!("{edge} has a missing forwarding successor"))
            })?;
            if cfg.edges[edge_index].to != next_cfg.from
                || plan.forward_depth[edge_index]
                    != plan.forward_depth[next.index()].saturating_add(1)
                || !(plan.forward_preorder[next.index()] <= plan.forward_preorder[edge_index]
                    && plan.forward_preorder[edge_index] < plan.forward_subtree_end[next.index()])
            {
                return Err(StructureError::invalid(format!(
                    "{edge} has a stale forwarding successor"
                )));
            }
            route_predecessor_count[next.index()] += 1;
            route_predecessor[next.index()] = Some(edge);
        } else if plan.forward_depth[edge_index] != 0 {
            return Err(StructureError::invalid(format!(
                "forward route root {edge} has a non-zero depth"
            )));
        }

        let owner = plan.forward_owner_by_edge[edge_index]
            .ok_or_else(|| StructureError::invalid("forward route edge has no loop owner"))?;
        let kind = plan.forward_kind_by_edge[edge_index]
            .ok_or_else(|| StructureError::invalid("forward route edge has no semantic kind"))?;
        let Some(RegionPlan::Loop { control, body, .. }) = plan.region(owner) else {
            return Err(StructureError::invalid(
                "forward route edge owner is not a loop",
            ));
        };
        let cfg_edge = cfg.edges[edge_index];
        let edge_plan = plan
            .edge_plan(edge)
            .ok_or_else(|| StructureError::invalid("forward route edge has no edge plan"))?;
        let source_owner = plan.region_for_block(cfg_edge.from).ok_or_else(|| {
            StructureError::invalid("forward route source block has no containment owner")
        })?;
        let is_last = is_route_last[edge_index];
        match kind {
            ForwardRouteKind::ExclusiveBreak => {
                let expected_incoming = if let Some(route_id) = first_route[edge_index] {
                    entry_by_route[route_id.index()]
                } else if route_predecessor_count[edge_index] == 1 {
                    route_predecessor[edge_index]
                } else {
                    None
                };
                let ancestor_loopback = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(ancestor)
                        if is_last
                            && ancestor != owner
                            && edge_plan.owner == ancestor
                            && intervals.contains(ancestor, owner)
                            && intervals.contains(ancestor, source_owner)
                            && matches!(
                                plan.region(ancestor),
                                Some(RegionPlan::Loop { plan: loop_id, .. })
                                    if plan.loop_(*loop_id)
                                        .is_some_and(|loop_| loop_.header == cfg_edge.to)
                            )
                );
                if index.break_barriers[cfg_edge.from.index()]
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || expected_incoming.is_none()
                    || cfg.preds[cfg_edge.from.index()].as_slice() != expected_incoming.as_slice()
                    || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                    || cfg_edge.kind != EdgeKind::Jump
                    || !(edge_plan.transfer == EdgeTransfer::Fallthrough || ancestor_loopback)
                {
                    return Err(StructureError::invalid(format!(
                        "exclusive break forwarding edge {edge} is not a pure pad: block={} preds={:?} expected={expected_incoming:?} succs={:?} kind={:?} transfer={:?} forward-owner={:?} forward-kind={:?} break-barrier={} island={}",
                        cfg_edge.from,
                        cfg.preds[cfg_edge.from.index()],
                        cfg.succs[cfg_edge.from.index()],
                        cfg_edge.kind,
                        edge_plan.transfer,
                        plan.forward_owner_by_edge[edge.index()],
                        plan.forward_kind_by_edge[edge.index()],
                        index.break_barriers[cfg_edge.from.index()],
                        plan.navigation.has_unstructured_ancestor(source_owner),
                    )));
                }
            }
            ForwardRouteKind::ContinueToTarget | ForwardRouteKind::ContinueLatch => {
                let terminal_transfer = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(region) | EdgeTransfer::Continue(region) if region == owner
                );
                let nested_break = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::Break(nested)
                        if !is_last
                            && nested != owner
                            && edge_plan.owner == nested
                            && edge_plan.forward_route.is_none()
                            && edge_plan.iteration.is_empty()
                            && intervals.contains(owner, nested)
                            && intervals.contains(nested, source_owner)
                            && plan.region_for_block(cfg_edge.to).is_some_and(|target_owner| {
                                !intervals.contains(nested, target_owner)
                                    && intervals.contains(*body, target_owner)
                            })
                            && matches!(
                                plan.region(nested),
                                Some(RegionPlan::Loop { plan: loop_id, .. })
                                    if plan.loop_(*loop_id)
                                        .is_some_and(|loop_| loop_.continuation == Some(cfg_edge.to))
                            )
                );
                if index.continue_barriers[cfg_edge.from.index()]
                    || !intervals.contains(*body, source_owner)
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                    || cfg_edge.kind != EdgeKind::Jump
                    || cfg.blocks[cfg_edge.from.index()].instrs.len != 1
                    || if is_last {
                        !terminal_transfer
                    } else {
                        edge_plan.transfer != EdgeTransfer::Fallthrough && !nested_break
                    }
                {
                    return Err(StructureError::invalid(format!(
                        "continue forwarding edge {edge} is not a pure loop pad"
                    )));
                }
            }
            ForwardRouteKind::RepeatConditionArc(_) => {
                let ForwardRouteKind::RepeatConditionArc(arc_ref) = kind else {
                    return Err(StructureError::invalid(
                        "repeat forwarding edge lost its condition arc",
                    ));
                };
                let arc = plan
                    .condition(arc_ref.condition)
                    .and_then(|condition| condition.nodes.get(arc_ref.node.index()))
                    .map(|node| node.arc(arc_ref.polarity))
                    .ok_or_else(|| {
                        StructureError::invalid("repeat forwarding edge has a stale condition arc")
                    })?;
                let arc_first = *arc.route.first().ok_or_else(|| {
                    StructureError::invalid("repeat forwarding condition arc is empty")
                })?;
                let arc_last = *arc.route.last().ok_or_else(|| {
                    StructureError::invalid("repeat forwarding condition arc is empty")
                })?;
                let condition_edge = plan.forward_path_contains_edge(arc_first, arc_last, edge);
                let terminal_transfer = matches!(
                    edge_plan.transfer,
                    EdgeTransfer::LoopBack(region) | EdgeTransfer::Continue(region) if region == owner
                );
                if index.continue_barriers[cfg_edge.from.index()]
                    || plan.navigation.has_unstructured_ancestor(source_owner)
                    || if condition_edge {
                        !intervals.contains(*control, source_owner)
                            || if is_last {
                                !terminal_transfer
                            } else {
                                !matches!(
                                    edge_plan.transfer,
                                    EdgeTransfer::Fallthrough
                                        | EdgeTransfer::BranchArm(
                                            BranchArm::Truthy | BranchArm::Falsy
                                        )
                                )
                            }
                    } else {
                        !intervals.contains(*body, source_owner)
                            || cfg.succs[cfg_edge.from.index()].as_slice() != [edge]
                            || cfg_edge.kind != EdgeKind::Jump
                            || cfg.blocks[cfg_edge.from.index()].instrs.len != 1
                            || edge_plan.transfer != EdgeTransfer::Fallthrough
                    }
                {
                    return Err(StructureError::invalid(format!(
                        "repeat condition forwarding edge {edge} is inconsistent"
                    )));
                }
            }
        }
    }
    Ok(())
}

fn validate_continue_forwarding_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    entry: &super::EdgePlan,
    loop_region: RegionId,
) -> Result<bool, StructureError> {
    let Some(route_id) = entry.forward_route else {
        return Ok(false);
    };
    let route = plan.forward_route(route_id).ok_or_else(|| {
        StructureError::invalid(format!(
            "continue entry references missing route #{route_id:?}"
        ))
    })?;
    Ok(route.loop_region == loop_region
        && matches!(
            route.kind,
            ForwardRouteKind::ContinueToTarget
                | ForwardRouteKind::ContinueLatch
                | ForwardRouteKind::RepeatConditionArc(_)
        )
        && cfg.edges.get(entry.edge.index()).map(|edge| edge.to) == Some(route.start))
}

fn validate_break_forwarding_route(
    cfg: &Cfg,
    plan: &StructurePlan,
    _intervals: &RegionNavigation,
    entry: &super::EdgePlan,
    loop_region: RegionId,
    _continuation: Option<crate::structure::BlockRef>,
    _validation_index: &EdgeValidationIndex,
) -> Result<bool, StructureError> {
    let Some(route_id) = entry.forward_route else {
        return Ok(false);
    };
    let route = plan.forward_route(route_id).ok_or_else(|| {
        StructureError::invalid(format!(
            "break entry references missing route #{route_id:?}"
        ))
    })?;
    Ok(route.loop_region == loop_region
        && route.kind == ForwardRouteKind::ExclusiveBreak
        && cfg.edges.get(entry.edge.index()).map(|edge| edge.to) == Some(route.start))
}

fn validate_requirements(
    cfg: &Cfg,
    plan: &StructurePlan,
    _intervals: &RegionNavigation,
) -> Result<(), StructureError> {
    if plan.requirements.by_edge.len() != cfg.edges.len()
        || plan.requirements.unresolved_by_block.len() != cfg.blocks.len()
    {
        return Err(StructureError::invalid(
            "requirement reverse index length mismatch",
        ));
    }
    let mut required_features = BTreeSet::new();
    let mut expected_by_edge = vec![Vec::new(); cfg.edges.len()];
    let mut expected_unresolved_by_block = vec![false; cfg.blocks.len()];
    let mut multi_entry_requirement = vec![false; plan.regions.len()];
    for (id, requirement) in plan.requirements.iter() {
        match requirement {
            PlanRequirement::Goto { edge, label, .. } => {
                if !matches!(plan.edge_plan(*edge).map(|plan| plan.transfer), Some(EdgeTransfer::Goto(target, _)) if target == *label)
                {
                    return Err(StructureError::invalid(format!(
                        "goto requirement #{} disagrees with edge transfer",
                        id.index()
                    )));
                }
                required_features.insert(ControlFlowFeature::GotoLabel);
                expected_by_edge[edge.index()].push(id);
            }
            PlanRequirement::Continue { edge, loop_region } => {
                if !matches!(plan.edge_plan(*edge).map(|plan| plan.transfer), Some(EdgeTransfer::Continue(region)) if region == *loop_region)
                {
                    return Err(StructureError::invalid(format!(
                        "continue requirement #{} disagrees with edge transfer",
                        id.index()
                    )));
                }
                required_features.insert(ControlFlowFeature::ContinueStatement);
                expected_by_edge[edge.index()].push(id);
            }
            PlanRequirement::MultiEntryIsland {
                region,
                entry_count,
            } => {
                let valid = matches!(
                    plan.region(*region),
                    Some(RegionPlan::Unstructured { entries, .. })
                        if entries.len() == *entry_count && *entry_count > 1
                );
                let Some(seen) = multi_entry_requirement.get_mut(region.index()) else {
                    return Err(StructureError::invalid(
                        "multi-entry requirement references a missing region",
                    ));
                };
                if !valid || std::mem::replace(seen, true) {
                    return Err(StructureError::invalid("multi-entry requirement is stale"));
                }
                required_features.insert(ControlFlowFeature::GotoLabel);
            }
            PlanRequirement::UnresolvedValue { block, .. } => {
                let unresolved = expected_unresolved_by_block
                    .get_mut(block.index())
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "unresolved requirement references a missing CFG block",
                        )
                    })?;
                *unresolved = true;
            }
        }
    }
    for (index, region) in plan.regions.iter().enumerate() {
        let expected = matches!(
            region,
            RegionPlan::Unstructured { entries, .. } if entries.len() > 1
        );
        if multi_entry_requirement[index] != expected {
            return Err(StructureError::invalid(format!(
                "region #{index} multi-entry requirement coverage is stale"
            )));
        }
    }
    if required_features != plan.requirements.required_features {
        return Err(StructureError::invalid(
            "required control-flow feature index is stale",
        ));
    }
    if expected_by_edge != plan.requirements.by_edge {
        return Err(StructureError::invalid(
            "requirement edge reverse index is incomplete or stale",
        ));
    }
    if expected_unresolved_by_block != plan.requirements.unresolved_by_block {
        return Err(StructureError::invalid(
            "unresolved requirement block index is incomplete or stale",
        ));
    }
    let expected_unavailable = required_features
        .iter()
        .copied()
        .filter(|feature| match feature {
            ControlFlowFeature::GotoLabel => !plan.requirements.caps.goto_label,
            ControlFlowFeature::ContinueStatement => !plan.requirements.caps.continue_stmt,
        })
        .collect::<BTreeSet<_>>();
    if expected_unavailable != plan.requirements.unavailable_features {
        return Err(StructureError::invalid(
            "unavailable control-flow feature index is stale",
        ));
    }
    Ok(())
}

fn validate_cleanup(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.cleanup_dispositions.len() != proto.instrs.len() {
        return Err(StructureError::invalid(
            "cleanup disposition length mismatch",
        ));
    }
    let mut lexical_scope_by_cleanup = vec![None; proto.instrs.len()];
    for (scope_index, scope) in plan.scopes.iter().enumerate() {
        let scope_id = ScopePlanId(scope_index);
        for close in &scope.close_points {
            let Some(slot) = lexical_scope_by_cleanup.get_mut(close.index()) else {
                return Err(StructureError::invalid(format!(
                    "lexical scope #{scope_index} cleanup is outside the instruction arena"
                )));
            };
            if slot.replace(scope_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{} has multiple lexical scope owners",
                    close.index()
                )));
            }
        }
    }
    let mut tbc_scope_by_cleanup = vec![None; proto.instrs.len()];
    for (scope_index, scope) in plan.tbc_scopes.iter().enumerate() {
        let scope_id = super::TbcScopePlanId(scope_index);
        if scope.origins.is_empty() || !scope.origins.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(StructureError::invalid(format!(
                "TBC scope #{scope_index} is not canonical"
            )));
        }
        for (close, boundary) in std::iter::once((scope.boundary, true))
            .chain(scope.exits.iter().copied().map(|close| (close, false)))
        {
            let Some(slot) = tbc_scope_by_cleanup.get_mut(close.index()) else {
                return Err(StructureError::invalid(format!(
                    "TBC scope #{scope_index} cleanup is outside the instruction arena"
                )));
            };
            if slot.replace((scope_id, boundary)).is_some() {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{} has multiple TBC scope owners",
                    close.index()
                )));
            }
        }
    }
    for (index, instr) in proto.instrs.iter().enumerate() {
        let disposition = plan.cleanup_dispositions[index];
        let is_cleanup = matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_));
        if is_cleanup != disposition.is_some() {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} does not have one dense disposition"
            )));
        }
        if !is_cleanup {
            continue;
        }
        let reachable = cfg
            .instr_to_block
            .get(index)
            .is_some_and(|block| cfg.reachable_blocks.contains(block));
        if matches!(disposition, Some(CleanupDisposition::Unreachable)) == reachable {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} reachability disposition is stale"
            )));
        }
        if let Some(CleanupDisposition::LoopTbcBoundary(region)) = disposition
            && !matches!(plan.region(region), Some(RegionPlan::Loop { .. }))
        {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} references a non-loop region"
            )));
        }
        if let Some(CleanupDisposition::LexicalScope(scope)) = disposition
            && lexical_scope_by_cleanup[index] != Some(scope)
        {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} lexical scope owner is stale"
            )));
        }
        match disposition {
            Some(CleanupDisposition::ExplicitTbcBoundary(scope))
                if tbc_scope_by_cleanup[index] != Some((scope, true)) =>
            {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{index} TBC boundary owner is stale"
                )));
            }
            Some(CleanupDisposition::ExplicitTbcExit(scope))
                if tbc_scope_by_cleanup[index] != Some((scope, false)) =>
            {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{index} TBC exit owner is stale"
                )));
            }
            _ => {}
        }
    }
    for (loop_id, loop_) in plan.loops() {
        let Some(tail) = &loop_.exit_tail else {
            continue;
        };
        let actual_cleanup = (tail.range.start.index()..tail.range.end())
            .filter(|index| {
                matches!(
                    proto.instrs.get(*index),
                    Some(LowInstr::Close(_) | LowInstr::Tbc(_))
                )
            })
            .map(crate::transformer::InstrRef)
            .collect::<Vec<_>>();
        let has_control = (tail.range.start.index()..tail.range.end()).any(|index| {
            proto
                .instrs
                .get(index)
                .is_some_and(LowInstr::is_control_terminator)
        });
        let cleanup_shape_is_valid = if tail.cleanup_block == tail.block {
            actual_cleanup == tail.cleanup
        } else {
            actual_cleanup.is_empty()
                && tail.cleanup.iter().all(|instr| {
                    matches!(proto.instrs.get(instr.index()), Some(LowInstr::Close(_)))
                })
        };
        if !cleanup_shape_is_valid
            || tail.cleanup.is_empty()
            || has_control
            || tail.cleanup.iter().any(|instr| {
                matches!(
                    plan.cleanup_disposition(*instr),
                    None | Some(CleanupDisposition::Unreachable)
                )
            })
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} has a stale executable exit-tail range",
                loop_id.index()
            )));
        }
    }
    for (index, edge_plan) in plan.edge_plans.iter().enumerate() {
        let EdgeActionPlacement::BeforeTrailingCleanup { cleanup } = edge_plan.action_placement
        else {
            continue;
        };
        let edge = &cfg.edges[index];
        let block_range = cfg.blocks[edge.from.index()].instrs;
        let Some(terminator) = block_range.last() else {
            return Err(StructureError::invalid(format!(
                "edge #{index} cleanup placement source is empty"
            )));
        };
        let cleanup_is_exact = cleanup.end() == terminator.index()
            && (cleanup.start.index()..cleanup.end()).all(|instr| {
                matches!(
                    proto.instrs.get(instr),
                    Some(LowInstr::Close(_) | LowInstr::Tbc(_))
                )
            })
            && cleanup.start.index() > block_range.start.index()
            && !matches!(
                proto.instrs.get(cleanup.start.index() - 1),
                Some(LowInstr::Close(_) | LowInstr::Tbc(_))
            );
        if edge_plan.phi_copies.is_empty()
            || !matches!(
                proto.instrs.get(terminator.index()),
                Some(LowInstr::Jump(_))
            )
            || !cleanup_is_exact
            || (cleanup.start.index()..cleanup.end()).any(|instr| {
                matches!(
                    plan.cleanup_disposition(crate::transformer::InstrRef(instr)),
                    None | Some(CleanupDisposition::Unreachable)
                )
            })
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} trailing-cleanup action contract is stale"
            )));
        }
    }
    Ok(())
}

fn validate_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.phis.len() != dataflow.phi_candidates.len()
        || plan.phis_by_block.len() != cfg.blocks.len()
        || plan.phis_by_region.len() != plan.regions.len()
    {
        return Err(StructureError::invalid("phi plan/index length mismatch"));
    }
    let mut expected_by_block = vec![Vec::new(); cfg.blocks.len()];
    let mut expected_by_region = vec![BTreeSet::new(); plan.regions.len()];
    let mut expected_edge_copies = vec![Vec::new(); cfg.edges.len()];
    let mut unresolved_requirements = vec![0usize; dataflow.phi_candidates.len()];
    let canonical_targets = crate::structure::phi_facts::CanonicalEdgeCopyTargets::build(
        plan,
        dataflow.phi_candidates.len(),
    )?;
    for (_, requirement) in plan.requirements.iter() {
        if let PlanRequirement::UnresolvedValue { phi_id, block, reg } = requirement {
            let Some(count) = unresolved_requirements.get_mut(phi_id.index()) else {
                return Err(StructureError::invalid(format!(
                    "unresolved requirement references missing {phi_id}"
                )));
            };
            let candidate = &dataflow.phi_candidates[phi_id.index()];
            if candidate.id != *phi_id || candidate.block != *block || candidate.reg != *reg {
                return Err(StructureError::invalid(format!(
                    "unresolved requirement for {phi_id} has stale location"
                )));
            }
            *count += 1;
        }
    }
    for candidate in &dataflow.phi_candidates {
        let phi = plan.phi_plan(candidate.id).ok_or_else(|| {
            StructureError::invalid(format!("{} has no final value plan", candidate.id))
        })?;
        if phi.phi != candidate.id
            || phi.block != candidate.block
            || phi.reg != candidate.reg
            || phi.incomings.len() != candidate.incoming.len()
        {
            return Err(StructureError::invalid(format!(
                "{} identity/incoming shape is stale",
                candidate.id
            )));
        }
        expected_by_block[candidate.block.index()].push(candidate.id);
        let mut unresolved = false;
        for (incoming, expected) in phi.incomings.iter().zip(&candidate.incoming) {
            if incoming.edge != expected.edge || incoming.value != expected.value {
                return Err(StructureError::invalid(format!(
                    "{} incoming identity is stale",
                    candidate.id
                )));
            }
            if let Some(edge) = incoming.edge
                && cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(candidate.block)
            {
                return Err(StructureError::invalid(format!(
                    "{} incoming edge does not target its phi block",
                    candidate.id
                )));
            }
            let copy_target =
                canonical_targets.for_incoming(plan, candidate, expected, incoming.disposition);
            match incoming.disposition {
                PhiIncomingDisposition::RegionInput(region)
                | PhiIncomingDisposition::RegionResult(region)
                | PhiIncomingDisposition::LoopCarried(region)
                    if region.index() >= plan.regions.len() =>
                {
                    return Err(StructureError::invalid(format!(
                        "{} incoming references missing region",
                        candidate.id
                    )));
                }
                PhiIncomingDisposition::RegionInput(region)
                | PhiIncomingDisposition::RegionResult(region)
                | PhiIncomingDisposition::LoopCarried(region) => {
                    expected_by_region[region.index()].insert(candidate.id);
                    if crate::structure::phi_facts::incoming_requires_edge_copy(
                        plan,
                        candidate.id,
                        incoming.disposition,
                    ) && let Some(edge) = incoming.edge
                    {
                        expected_edge_copies[edge.index()].push(super::PhiEdgeCopy {
                            phi_id: copy_target,
                            value: incoming.value,
                        });
                    }
                }
                PhiIncomingDisposition::EdgeCopy => {
                    let edge = incoming.edge.ok_or_else(|| {
                        StructureError::invalid(format!(
                            "{} synthetic incoming cannot be an edge copy",
                            candidate.id
                        ))
                    })?;
                    expected_edge_copies[edge.index()].push(super::PhiEdgeCopy {
                        phi_id: copy_target,
                        value: incoming.value,
                    });
                }
                PhiIncomingDisposition::DiagnosticUnresolved => unresolved = true,
                PhiIncomingDisposition::Dead => {}
            }
        }
        let has_requirement = unresolved_requirements[candidate.id.index()] == 1;
        if unresolved != has_requirement || unresolved_requirements[candidate.id.index()] > 1 {
            return Err(StructureError::invalid(format!(
                "{} unresolved disposition/requirement mismatch",
                candidate.id
            )));
        }
    }
    if plan.phis_by_block != expected_by_block {
        return Err(StructureError::invalid("phi block reverse index is stale"));
    }
    for (index, expected) in expected_by_region.iter().enumerate() {
        if plan.phis_by_region[index]
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != *expected
        {
            return Err(StructureError::invalid(format!(
                "region #{index} phi reverse index is stale"
            )));
        }
    }
    if crate::structure::phi_facts::build_forwarded_action_heads(plan)? != plan.forward_action_head
    {
        return Err(StructureError::invalid(
            "forwarded phi action index is stale",
        ));
    }
    for (index, expected) in expected_edge_copies.iter().enumerate() {
        if plan.edge_plans[index].phi_copies != *expected {
            return Err(StructureError::invalid(format!(
                "edge #{index} dense phi actions are stale or conflicting"
            )));
        }
    }
    Ok(())
}
