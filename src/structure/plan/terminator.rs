//! 把 basic block 的物理结尾冻结成稠密计划。
//!
//! CFG 构建时已经解释过 low-IR 控制指令；这里把指令 identity 与精确 edge identity
//! 一次性配对，避免 HIR 再按 opcode target 或 successor 数量重建同一事实。

use crate::structure::{BlockKind, BlockRef, Cfg, EdgeKind, EdgeRef, InstrRange, StructureError};
use crate::transformer::{InstrRef, LowInstr, LoweredProto};

/// 一个 basic block 的冻结物理结尾。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockTerminatorPlan {
    pub block: BlockRef,
    pub instrs: InstrRange,
    pub kind: BlockTerminatorKind,
}

/// 控制指令与其唯一 CFG edge identity。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockTerminatorKind {
    SyntheticExit,
    Linear {
        edge: Option<EdgeRef>,
    },
    Jump {
        instr: InstrRef,
        edge: EdgeRef,
    },
    Branch {
        instr: InstrRef,
        truthy: EdgeRef,
        falsy: EdgeRef,
    },
    Return {
        instr: InstrRef,
        edge: EdgeRef,
    },
    TailCall {
        instr: InstrRef,
        edge: EdgeRef,
    },
    NumericForInit {
        instr: InstrRef,
        body: EdgeRef,
        exit: EdgeRef,
    },
    NumericForLoop {
        instr: InstrRef,
        body: EdgeRef,
        exit: EdgeRef,
    },
    GenericForLoop {
        instr: InstrRef,
        body: EdgeRef,
        exit: EdgeRef,
    },
}

impl BlockTerminatorKind {
    /// 返回被该计划吸收、不应作为普通指令 lowering 的物理 terminator。
    pub const fn instr(self) -> Option<InstrRef> {
        match self {
            Self::SyntheticExit | Self::Linear { .. } => None,
            Self::Jump { instr, .. }
            | Self::Branch { instr, .. }
            | Self::Return { instr, .. }
            | Self::TailCall { instr, .. }
            | Self::NumericForInit { instr, .. }
            | Self::NumericForLoop { instr, .. }
            | Self::GenericForLoop { instr, .. } => Some(instr),
        }
    }
}

pub(super) fn freeze(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> Result<Vec<BlockTerminatorPlan>, StructureError> {
    if cfg.blocks.len() != cfg.succs.len() {
        return Err(StructureError::invalid(
            "CFG block/successor index length mismatch while freezing terminators",
        ));
    }

    cfg.blocks
        .iter()
        .copied()
        .enumerate()
        .map(|(index, basic_block)| {
            let block = BlockRef(index);
            let kind = match basic_block.kind {
                BlockKind::SyntheticExit => {
                    if !basic_block.instrs.is_empty() || !cfg.succs[index].is_empty() {
                        return Err(StructureError::invalid(format!(
                            "synthetic exit block {block} has instructions or successors"
                        )));
                    }
                    BlockTerminatorKind::SyntheticExit
                }
                BlockKind::Normal => freeze_normal(proto, cfg, block, basic_block.instrs)?,
            };
            Ok(BlockTerminatorPlan {
                block,
                instrs: basic_block.instrs,
                kind,
            })
        })
        .collect()
}

fn freeze_normal(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
    instrs: InstrRange,
) -> Result<BlockTerminatorKind, StructureError> {
    let Some(instr) = instrs.last() else {
        return Ok(BlockTerminatorKind::Linear {
            edge: freeze_linear_edge(cfg, block)?,
        });
    };
    let low = proto.instrs.get(instr.index()).ok_or_else(|| {
        StructureError::invalid(format!(
            "block {block} terminator {instr} is outside the low-IR arena"
        ))
    })?;
    match low {
        LowInstr::Jump(jump) => Ok(BlockTerminatorKind::Jump {
            instr,
            edge: freeze_target_edge(cfg, block, EdgeKind::Jump, jump.target)?,
        }),
        LowInstr::Branch(branch) => Ok(BlockTerminatorKind::Branch {
            instr,
            truthy: freeze_target_edge(cfg, block, EdgeKind::BranchTrue, branch.then_target)?,
            falsy: freeze_target_edge(cfg, block, EdgeKind::BranchFalse, branch.else_target)?,
        }),
        LowInstr::Return(_) => Ok(BlockTerminatorKind::Return {
            instr,
            edge: freeze_exit_edge(cfg, block, EdgeKind::Return)?,
        }),
        LowInstr::TailCall(_) => Ok(BlockTerminatorKind::TailCall {
            instr,
            edge: freeze_exit_edge(cfg, block, EdgeKind::TailCall)?,
        }),
        LowInstr::NumericForInit(loop_) => Ok(BlockTerminatorKind::NumericForInit {
            instr,
            body: freeze_target_edge(cfg, block, EdgeKind::LoopBody, loop_.body_target)?,
            exit: freeze_target_edge(cfg, block, EdgeKind::LoopExit, loop_.exit_target)?,
        }),
        LowInstr::NumericForLoop(loop_) => Ok(BlockTerminatorKind::NumericForLoop {
            instr,
            body: freeze_target_edge(cfg, block, EdgeKind::LoopBody, loop_.body_target)?,
            exit: freeze_target_edge(cfg, block, EdgeKind::LoopExit, loop_.exit_target)?,
        }),
        LowInstr::GenericForLoop(loop_) => Ok(BlockTerminatorKind::GenericForLoop {
            instr,
            body: freeze_target_edge(cfg, block, EdgeKind::LoopBody, loop_.body_target)?,
            exit: freeze_target_edge(cfg, block, EdgeKind::LoopExit, loop_.exit_target)?,
        }),
        _ => Ok(BlockTerminatorKind::Linear {
            edge: freeze_linear_edge(cfg, block)?,
        }),
    }
}

fn freeze_linear_edge(cfg: &Cfg, block: BlockRef) -> Result<Option<EdgeRef>, StructureError> {
    match cfg.succs.get(block.index()).map(Vec::as_slice) {
        Some([]) => Ok(None),
        Some([edge])
            if cfg.edges.get(edge.index()).is_some_and(|candidate| {
                candidate.from == block && candidate.kind == EdgeKind::Fallthrough
            }) =>
        {
            Ok(Some(*edge))
        }
        Some(_) => Err(StructureError::invalid(format!(
            "linear block {block} does not have zero or one fallthrough edge"
        ))),
        None => Err(StructureError::invalid(format!(
            "linear block {block} has no successor index"
        ))),
    }
}

fn freeze_exit_edge(cfg: &Cfg, block: BlockRef, kind: EdgeKind) -> Result<EdgeRef, StructureError> {
    let edge = freeze_unique_kind_edge(cfg, block, kind)?;
    if cfg.edges[edge.index()].to != cfg.exit_block {
        return Err(StructureError::invalid(format!(
            "terminal block {block} does not target the synthetic exit"
        )));
    }
    Ok(edge)
}

fn freeze_target_edge(
    cfg: &Cfg,
    block: BlockRef,
    kind: EdgeKind,
    target: InstrRef,
) -> Result<EdgeRef, StructureError> {
    let target_block = cfg
        .instr_to_block
        .get(target.index())
        .copied()
        .ok_or_else(|| {
            StructureError::invalid(format!(
                "control terminator in block {block} targets missing instruction {target}"
            ))
        })?;
    let edge = freeze_unique_kind_edge(cfg, block, kind)?;
    if cfg.edges[edge.index()].to != target_block {
        return Err(StructureError::invalid(format!(
            "control terminator in block {block} disagrees with edge {edge} target"
        )));
    }
    Ok(edge)
}

fn freeze_unique_kind_edge(
    cfg: &Cfg,
    block: BlockRef,
    kind: EdgeKind,
) -> Result<EdgeRef, StructureError> {
    let succs = cfg
        .succs
        .get(block.index())
        .ok_or_else(|| StructureError::invalid(format!("block {block} has no successor index")))?;
    let mut found = None;
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
        if candidate.kind == kind && found.replace(edge).is_some() {
            return Err(StructureError::invalid(format!(
                "block {block} has multiple {kind:?} edges"
            )));
        }
    }
    let edge = found
        .ok_or_else(|| StructureError::invalid(format!("block {block} has no {kind:?} edge")))?;
    let expected_len = match kind {
        EdgeKind::BranchTrue | EdgeKind::BranchFalse | EdgeKind::LoopBody | EdgeKind::LoopExit => 2,
        EdgeKind::Fallthrough | EdgeKind::Jump | EdgeKind::Return | EdgeKind::TailCall => 1,
    };
    if succs.len() != expected_len {
        return Err(StructureError::invalid(format!(
            "block {block} has an unexpected successor count for {kind:?}"
        )));
    }
    Ok(edge)
}
