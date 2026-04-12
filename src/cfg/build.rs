//! 这个文件实现 shared CFG 构建。
//!
//! 这里坚持只按控制流切块，不夹带结构恢复语义，是为了让后续 GraphFacts /
//! Dataflow 都能在同一份"最原始但稳定"的图上复用分析结果。
//!
//! `CfgBuilder` 把构图过程中反复传递的 `edges/preds/succs/instr_to_block`
//! 收敛到一个可变上下文里，消除了原先十几个 helper 各带 6 个参数的模式。

use std::collections::BTreeSet;

use crate::transformer::{InstrRef, LowInstr, LoweredProto};

use super::common::{
    BasicBlock, BlockKind, BlockRef, Cfg, CfgEdge, CfgGraph, EdgeKind, EdgeRef, InstrRange,
};

/// 对 proto 树递归构建 CFG。
pub fn build_cfg_proto(proto: &LoweredProto) -> CfgGraph {
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

        match &instrs[last_instr.index()] {
            LowInstr::Jump(instr) => {
                builder.add_target_edge(&instr_to_block, block_ref, instr.target, EdgeKind::Jump);
            }
            LowInstr::Branch(instr) => {
                builder.add_target_edge(&instr_to_block, block_ref, instr.then_target, EdgeKind::BranchTrue);
                builder.add_target_edge(&instr_to_block, block_ref, instr.else_target, EdgeKind::BranchFalse);
            }
            LowInstr::NumericForInit(instr) => {
                builder.add_target_edge(&instr_to_block, block_ref, instr.body_target, EdgeKind::LoopBody);
                builder.add_target_edge(&instr_to_block, block_ref, instr.exit_target, EdgeKind::LoopExit);
            }
            LowInstr::NumericForLoop(instr) => {
                builder.add_target_edge(&instr_to_block, block_ref, instr.body_target, EdgeKind::LoopBody);
                builder.add_target_edge(&instr_to_block, block_ref, instr.exit_target, EdgeKind::LoopExit);
            }
            LowInstr::GenericForLoop(instr) => {
                builder.add_target_edge(&instr_to_block, block_ref, instr.body_target, EdgeKind::LoopBody);
                builder.add_target_edge(&instr_to_block, block_ref, instr.exit_target, EdgeKind::LoopExit);
            }
            LowInstr::Return(_) => {
                builder.add_edge(block_ref, exit_block, EdgeKind::Return);
            }
            LowInstr::TailCall(_) => {
                builder.add_edge(block_ref, exit_block, EdgeKind::TailCall);
            }
            _ => {
                if let Some(next_block) = block_order.get(index + 1).copied() {
                    builder.add_edge(block_ref, next_block, EdgeKind::Fallthrough);
                }
            }
        }
    }

    let entry_block = BlockRef(0);
    let reachable_blocks = compute_reachable_blocks(entry_block, &builder.edges, &builder.succs);

    Cfg {
        blocks,
        edges: builder.edges,
        entry_block,
        exit_block,
        block_order,
        instr_to_block,
        preds: builder.preds,
        succs: builder.succs,
        reachable_blocks,
    }
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
    ) {
        let to = instr_to_block[target.index()];
        self.add_edge(from, to, kind);
    }
}

fn collect_leaders(instrs: &[LowInstr]) -> BTreeSet<usize> {
    let mut leaders = BTreeSet::from([0]);

    for (index, instr) in instrs.iter().enumerate() {
        collect_jump_targets(instr, |target| {
            assert!(
                target.index() < instrs.len(),
                "low-IR jump target @{} must stay inside proto",
                target.index()
            );
            leaders.insert(target.index());
        });

        if is_terminator(instr) && index + 1 < instrs.len() {
            leaders.insert(index + 1);
        }
    }

    leaders
}

/// 把指令的跳转目标通过回调交给调用方，避免为至多 2 个元素分配 `Vec`。
fn collect_jump_targets(instr: &LowInstr, mut f: impl FnMut(InstrRef)) {
    match instr {
        LowInstr::Jump(instr) => f(instr.target),
        LowInstr::Branch(instr) => {
            f(instr.then_target);
            f(instr.else_target);
        }
        LowInstr::NumericForInit(instr) => {
            f(instr.body_target);
            f(instr.exit_target);
        }
        LowInstr::NumericForLoop(instr) => {
            f(instr.body_target);
            f(instr.exit_target);
        }
        LowInstr::GenericForLoop(instr) => {
            f(instr.body_target);
            f(instr.exit_target);
        }
        _ => {}
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
