//! 校验基本块终结指令及其边归属；依赖 lowered 指令和 CFG，不负责区域布局；例如核对 TEST/JMP 的两个后继。

use super::*;

/// 证明稠密 terminator arena 与 low-IR/CFG 是同一份物理控制流事实。
///
/// 这里先验证 block range 构成 low-IR 的线性分区，再按 source block 各 claim 一次
/// CFG edge；因此即使输入已经损坏，工作量仍受 `blocks + edges + instructions` 限制。
pub(super) fn validate_block_terminators(
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

pub(super) fn checked_range_end(start: InstrRef, len: usize) -> Result<usize, StructureError> {
    start
        .index()
        .checked_add(len)
        .ok_or_else(|| StructureError::invalid("CFG instruction range overflows usize"))
}

pub(super) fn terminator_instr(
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

pub(super) fn claim_loop_edges(
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

pub(super) fn claim_target_edge(
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

pub(super) fn claim_terminator_edge(
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
