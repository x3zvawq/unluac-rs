//! 这个文件实现 shared CFG 构建。
//!
//! 这里坚持只按控制流切块，不夹带结构恢复语义，是为了让后续 GraphFacts /
//! Dataflow 都能在同一份“最原始但稳定”的图上复用分析结果。

use std::collections::BTreeSet;

use crate::transformer::{
    BranchInstr, GenericForLoopInstr, InstrRef, JumpInstr, LowInstr, LoweredChunk, LoweredProto,
    NumericForInitInstr, NumericForLoopInstr,
};

use super::common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, EdgeKind, EdgeRef, InstrRange,
};

/// 对整个 lowered chunk 递归构建 CFG。
pub fn build_cfg_graph(chunk: &LoweredChunk) -> CfgGraph {
    build_cfg_proto(&chunk.main)
}

fn build_cfg_proto(proto: &LoweredProto) -> CfgGraph {
    CfgGraph {
        cfg: build_cfg(&proto.instrs),
        children: proto.children.iter().map(build_cfg_proto).collect(),
    }
}

fn build_cfg(instrs: &[LowInstr]) -> Cfg {
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

        return Cfg {
            blocks,
            edges: Vec::new(),
            entry_block: BlockRef(0),
            exit_block: BlockRef(1),
            block_order: vec![BlockRef(0)],
            instr_to_block: Vec::new(),
            preds: vec![Vec::new(), Vec::new()],
            succs: vec![Vec::new(), Vec::new()],
            reachable_blocks: [BlockRef(0)].into_iter().collect(),
        };
    }

    let leaders = collect_leaders(instrs);
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

    let mut edges = Vec::new();
    let mut preds = vec![Vec::new(); blocks.len()];
    let mut succs = vec![Vec::new(); blocks.len()];

    for (index, block_ref) in block_order.iter().copied().enumerate() {
        let basic_block = blocks[block_ref.index()];
        let Some(last_instr) = basic_block.instrs.last() else {
            if let Some(next_block) = block_order.get(index + 1).copied() {
                add_edge(
                    &mut edges,
                    &mut preds,
                    &mut succs,
                    block_ref,
                    next_block,
                    EdgeKind::Fallthrough,
                );
            }
            continue;
        };

        match &instrs[last_instr.index()] {
            LowInstr::Jump(instr) => add_jump_edge(
                &mut edges,
                &mut preds,
                &mut succs,
                &instr_to_block,
                block_ref,
                instr,
            ),
            LowInstr::Branch(instr) => add_branch_edges(
                &mut edges,
                &mut preds,
                &mut succs,
                &instr_to_block,
                block_ref,
                instr,
            ),
            LowInstr::NumericForInit(instr) => add_numeric_loop_edges(
                &mut edges,
                &mut preds,
                &mut succs,
                &instr_to_block,
                block_ref,
                instr,
            ),
            LowInstr::NumericForLoop(instr) => add_numeric_loop_edges(
                &mut edges,
                &mut preds,
                &mut succs,
                &instr_to_block,
                block_ref,
                instr,
            ),
            LowInstr::GenericForLoop(instr) => add_generic_loop_edges(
                &mut edges,
                &mut preds,
                &mut succs,
                &instr_to_block,
                block_ref,
                instr,
            ),
            LowInstr::Return(_instr) => add_exit_edge(
                &mut edges,
                &mut preds,
                &mut succs,
                block_ref,
                exit_block,
                EdgeKind::Return,
            ),
            LowInstr::TailCall(_instr) => add_exit_edge(
                &mut edges,
                &mut preds,
                &mut succs,
                block_ref,
                exit_block,
                EdgeKind::TailCall,
            ),
            _ => {
                if let Some(next_block) = block_order.get(index + 1).copied() {
                    add_edge(
                        &mut edges,
                        &mut preds,
                        &mut succs,
                        block_ref,
                        next_block,
                        EdgeKind::Fallthrough,
                    );
                }
            }
        }
    }

    let entry_block = BlockRef(0);
    let reachable_blocks = compute_reachable_blocks(entry_block, &edges, &succs);

    Cfg {
        blocks,
        edges,
        entry_block,
        exit_block,
        block_order,
        instr_to_block,
        preds,
        succs,
        reachable_blocks,
    }
}

fn collect_leaders(instrs: &[LowInstr]) -> BTreeSet<usize> {
    let mut leaders = BTreeSet::from([0]);

    for (index, instr) in instrs.iter().enumerate() {
        for target in jump_targets(instr) {
            assert!(
                target.index() < instrs.len(),
                "low-IR jump target @{} must stay inside proto",
                target.index()
            );
            leaders.insert(target.index());
        }

        if is_terminator(instr) && index + 1 < instrs.len() {
            leaders.insert(index + 1);
        }
    }

    leaders
}

fn jump_targets(instr: &LowInstr) -> Vec<InstrRef> {
    match instr {
        LowInstr::Jump(instr) => vec![instr.target],
        LowInstr::Branch(instr) => vec![instr.then_target, instr.else_target],
        LowInstr::NumericForInit(instr) => vec![instr.body_target, instr.exit_target],
        LowInstr::NumericForLoop(instr) => vec![instr.body_target, instr.exit_target],
        LowInstr::GenericForLoop(instr) => vec![instr.body_target, instr.exit_target],
        _ => Vec::new(),
    }
}

fn is_terminator(instr: &LowInstr) -> bool {
    matches!(
        instr,
        LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::TailCall(_)
            | LowInstr::Return(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_)
    )
}

fn add_jump_edge(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    instr_to_block: &[BlockRef],
    from: BlockRef,
    instr: &JumpInstr,
) {
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.target),
        EdgeKind::Jump,
    );
}

fn add_branch_edges(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    instr_to_block: &[BlockRef],
    from: BlockRef,
    instr: &BranchInstr,
) {
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.then_target),
        EdgeKind::BranchTrue,
    );
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.else_target),
        EdgeKind::BranchFalse,
    );
}

fn add_numeric_loop_edges<T>(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    instr_to_block: &[BlockRef],
    from: BlockRef,
    instr: &T,
) where
    T: NumericLoopTargets,
{
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.body_target()),
        EdgeKind::LoopBody,
    );
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.exit_target()),
        EdgeKind::LoopExit,
    );
}

fn add_generic_loop_edges(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    instr_to_block: &[BlockRef],
    from: BlockRef,
    instr: &GenericForLoopInstr,
) {
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.body_target),
        EdgeKind::LoopBody,
    );
    add_edge(
        edges,
        preds,
        succs,
        from,
        block_for_instr(instr_to_block, instr.exit_target),
        EdgeKind::LoopExit,
    );
}

fn add_exit_edge(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    from: BlockRef,
    exit_block: BlockRef,
    kind: EdgeKind,
) {
    add_edge(edges, preds, succs, from, exit_block, kind);
}

fn add_edge(
    edges: &mut Vec<CfgEdge>,
    preds: &mut [Vec<EdgeRef>],
    succs: &mut [Vec<EdgeRef>],
    from: BlockRef,
    to: BlockRef,
    kind: EdgeKind,
) {
    let edge_ref = EdgeRef(edges.len());
    edges.push(CfgEdge { from, to, kind });
    succs[from.index()].push(edge_ref);
    preds[to.index()].push(edge_ref);
}

fn block_for_instr(instr_to_block: &[BlockRef], target: InstrRef) -> BlockRef {
    instr_to_block[target.index()]
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

trait NumericLoopTargets {
    fn body_target(&self) -> InstrRef;
    fn exit_target(&self) -> InstrRef;
}

impl NumericLoopTargets for NumericForInitInstr {
    fn body_target(&self) -> InstrRef {
        self.body_target
    }

    fn exit_target(&self) -> InstrRef {
        self.exit_target
    }
}

impl NumericLoopTargets for NumericForLoopInstr {
    fn body_target(&self) -> InstrRef {
        self.body_target
    }

    fn exit_target(&self) -> InstrRef {
        self.exit_target
    }
}
