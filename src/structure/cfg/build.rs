//! 这个文件实现 shared CFG 构建。
//!
//! 这里坚持只按控制流切块，不夹带结构恢复语义，是为了让后续 GraphFacts /
//! Dataflow 都能在同一份"最原始但稳定"的图上复用分析结果。
//!
//! leader 与物理边共享 low-IR 控制出口投影，`CfgBuilder` 统一维护边及前驱/后继。
//! 例如真假分支指向同一指令时仍生成两条不同极性的边，不能按目标去重。

use std::collections::BTreeSet;

use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::structure::StructureError;
use crate::transformer::{InstrRef, LowInstr, LoweredProto};

use super::common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, EdgeKind, EdgeRef, InstrRange,
};

/// 对 proto 树递归构建 CFG。
pub(crate) fn build_cfg_proto(
    state: &mut DecompileState,
    _context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let lowered = state.require_lowered()?;
    state.cfg = Some(build_cfg_graph(&lowered.main)?);
    Ok(())
}

/// 对 proto 树构建 CFG。
///
/// Luau 的 serialized chunk 可以合法地包含数百层嵌套 proto。这里使用显式
/// postorder frame，而不是把 proto 深度压到 Rust 调用栈；每个 frame 只保留
/// 已完成的 child CFG，语义与原先的递归后序构建一致。
pub fn build_cfg_graph(proto: &LoweredProto) -> Result<CfgGraph, StructureError> {
    struct Frame<'a> {
        proto: &'a LoweredProto,
        next_child: usize,
        children: Vec<CfgGraph>,
    }

    let mut stack = vec![Frame {
        proto,
        next_child: 0,
        children: Vec::new(),
    }];
    loop {
        let child = {
            let frame = stack.last_mut().expect("CFG proto frame is non-empty");
            let child = frame.proto.children.get(frame.next_child);
            if child.is_some() {
                frame.next_child += 1;
            }
            child
        };
        if let Some(child) = child {
            stack.push(Frame {
                proto: child,
                next_child: 0,
                children: Vec::new(),
            });
            continue;
        }

        let frame = stack.pop().expect("CFG proto frame is non-empty");
        let result = CfgGraph {
            cfg: build_cfg(&frame.proto.instrs)?,
            children: frame.children,
        };
        if let Some(parent) = stack.last_mut() {
            parent.children.push(result);
        } else {
            return Ok(result);
        }
    }
}

fn build_cfg(instrs: &[LowInstr]) -> Result<Cfg, StructureError> {
    if instrs.is_empty() {
        let blocks = vec![
            BasicBlock {
                kind: BlockKind::Normal,
                instrs: InstrRange::new(InstrRef(0), 0),
            },
            BasicBlock {
                kind: BlockKind::SyntheticExit,
                instrs: InstrRange::new(InstrRef(0), 0),
            },
        ];

        return Ok(Cfg {
            blocks,
            edges: Vec::new(),
            entry_block: BlockRef(0),
            exit_block: BlockRef(1),
            block_order: vec![BlockRef(0)],
            instr_to_block: Vec::new(),
            preds: vec![Vec::new(), Vec::new()],
            succs: vec![Vec::new(), Vec::new()],
            reachable_blocks: [BlockRef(0)].into_iter().collect(),
        });
    }

    let leaders = collect_leaders(instrs)?;
    let block_starts = leaders.into_iter().collect::<Vec<_>>();
    let mut blocks = Vec::with_capacity(block_starts.len() + 1);
    let mut instr_to_block = vec![BlockRef(0); instrs.len()];
    let mut block_order = Vec::with_capacity(block_starts.len());

    for (index, start) in block_starts.iter().copied().enumerate() {
        let end = block_starts.get(index + 1).copied().unwrap_or(instrs.len());
        let block_ref = BlockRef(index);
        block_order.push(block_ref);
        blocks.push(BasicBlock {
            kind: BlockKind::Normal,
            instrs: InstrRange::new(InstrRef(start), end - start),
        });

        for slot in instr_to_block.iter_mut().take(end).skip(start) {
            *slot = block_ref;
        }
    }

    let exit_block = BlockRef(blocks.len());
    blocks.push(BasicBlock {
        kind: BlockKind::SyntheticExit,
        instrs: InstrRange::new(InstrRef(instrs.len()), 0),
    });

    let block_count = blocks.len();
    let mut builder = CfgBuilder {
        edges: Vec::new(),
        preds: vec![Vec::new(); block_count],
        succs: vec![Vec::new(); block_count],
    };

    for (index, block_ref) in block_order.iter().copied().enumerate() {
        let basic_block = blocks[block_ref.index()];
        let Some(last_instr) = basic_block.instrs.last() else {
            if let Some(next_block) = block_order.get(index + 1).copied() {
                builder.add_edge(block_ref, next_block, EdgeKind::Fallthrough);
            }
            continue;
        };

        let has_control_edges =
            visit_control_edges(&instrs[last_instr.index()], |target, kind| {
                match target {
                    Some(target) => {
                        builder.add_target_edge(&instr_to_block, block_ref, target, kind)?
                    }
                    None => builder.add_edge(block_ref, exit_block, kind),
                }
                Ok::<_, StructureError>(())
            })?;
        if !has_control_edges && let Some(next_block) = block_order.get(index + 1).copied() {
            builder.add_edge(block_ref, next_block, EdgeKind::Fallthrough);
        }
    }

    let entry_block = BlockRef(0);
    let reachable_blocks = compute_reachable_blocks(entry_block, &builder.edges, &builder.succs);

    let cfg = Cfg {
        blocks,
        edges: builder.edges,
        entry_block,
        exit_block,
        block_order,
        instr_to_block,
        preds: builder.preds,
        succs: builder.succs,
        reachable_blocks,
    };
    super::validate_cfg(&cfg)?;
    Ok(cfg)
}

/// 构图期间的可变上下文，把 `edges/preds/succs` 收拢到一处，
/// 消除原先每个 `add_*_edge` helper 都要带 6 个参数的模式。
struct CfgBuilder {
    edges: Vec<CfgEdge>,
    preds: Vec<Vec<EdgeRef>>,
    succs: Vec<Vec<EdgeRef>>,
}

impl CfgBuilder {
    fn add_edge(&mut self, from: BlockRef, to: BlockRef, kind: EdgeKind) {
        let edge_ref = EdgeRef(self.edges.len());
        self.edges.push(CfgEdge { from, to, kind });
        self.succs[from.index()].push(edge_ref);
        self.preds[to.index()].push(edge_ref);
    }

    /// 把指令级跳转目标翻译成 block 引用后添边。
    fn add_target_edge(
        &mut self,
        instr_to_block: &[BlockRef],
        from: BlockRef,
        target: InstrRef,
        kind: EdgeKind,
    ) -> Result<(), StructureError> {
        let to = instr_to_block.get(target.index()).copied().ok_or_else(|| {
            StructureError::invalid(format!(
                "low-IR control edge from {from} targets missing instruction {target}"
            ))
        })?;
        self.add_edge(from, to, kind);
        Ok(())
    }
}

fn collect_leaders(instrs: &[LowInstr]) -> Result<BTreeSet<usize>, StructureError> {
    let mut leaders = BTreeSet::from([0]);

    for (index, instr) in instrs.iter().enumerate() {
        visit_control_edges(instr, |target, _| {
            let Some(target) = target else {
                return Ok(());
            };
            if target.index() >= instrs.len() {
                return Err(StructureError::invalid(format!(
                    "low-IR control instruction @{index} targets missing instruction {target}"
                )));
            }
            leaders.insert(target.index());
            Ok(())
        })?;

        if instr.is_control_terminator() && index + 1 < instrs.len() {
            leaders.insert(index + 1);
        }
    }

    Ok(leaders)
}

/// 统一投影 low-IR 的控制出口；None 表示函数出口，返回 false 才使用普通 fallthrough。
/// leader 切分与物理边构造共享目标及极性，回调逐边执行，保留同目标双分支的身份和顺序。
fn visit_control_edges<E>(
    instr: &LowInstr,
    mut emit: impl FnMut(Option<InstrRef>, EdgeKind) -> Result<(), E>,
) -> Result<bool, E> {
    match instr {
        LowInstr::Jump(instr) => emit(Some(instr.target), EdgeKind::Jump)?,
        LowInstr::Branch(instr) => {
            emit(Some(instr.then_target), EdgeKind::BranchTrue)?;
            emit(Some(instr.else_target), EdgeKind::BranchFalse)?;
        }
        LowInstr::NumericForInit(instr) => {
            emit(Some(instr.body_target), EdgeKind::LoopBody)?;
            emit(Some(instr.exit_target), EdgeKind::LoopExit)?;
        }
        LowInstr::NumericForLoop(instr) => {
            emit(Some(instr.body_target), EdgeKind::LoopBody)?;
            emit(Some(instr.exit_target), EdgeKind::LoopExit)?;
        }
        LowInstr::GenericForLoop(instr) => {
            emit(Some(instr.body_target), EdgeKind::LoopBody)?;
            emit(Some(instr.exit_target), EdgeKind::LoopExit)?;
        }
        LowInstr::Return(_) => emit(None, EdgeKind::Return)?,
        LowInstr::TailCall(_) => emit(None, EdgeKind::TailCall)?,
        _ => return Ok(false),
    }
    Ok(true)
}

fn compute_reachable_blocks(
    entry_block: BlockRef,
    edges: &[CfgEdge],
    succs: &[Vec<EdgeRef>],
) -> BTreeSet<BlockRef> {
    let mut reachable = BTreeSet::new();
    let mut stack = vec![entry_block];

    while let Some(block) = stack.pop() {
        if !reachable.insert(block) {
            continue;
        }

        for edge_ref in &succs[block.index()] {
            let edge = edges[edge_ref.index()];
            if !reachable.contains(&edge.to) {
                stack.push(edge.to);
            }
        }
    }

    reachable
}
