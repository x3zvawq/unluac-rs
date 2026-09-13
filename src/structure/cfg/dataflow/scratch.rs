//! 原调用返回后未进入普通 SSA 的物理槽残值。
//!
//! CALL（包括 Ignore）可让 callee 的值留在 caller 高槽；逻辑 reaching value 仍是 Entry
//! 不代表该槽仍为 nil。本域只记录这种可能的未知残值，以及后续 fixed Def 覆盖它的责任，
//! 不创建逻辑 Def，也不推导源码 local。例如 CALL r4 后两路 MOVE r6,r0 合流，后面的
//! GETTABLE r6 可在 __index 中观察旧槽；两路 MOVE 的物理覆盖不能因同值 phi 而丢弃。
//!
//! 复用有限寄存器域与稠密集合；先按基本块冻结 gen/keep，再沿共享 CFG 求 may-union。
//! 回边只重算块摘要，收敛后一次遍历记录原写入；不会为每个 Def 重扫路径或后缀。

use super::liveness::DenseRegSet;
use super::*;

struct Transfer {
    generated: DenseRegSet,
    keep: DenseRegSet,
}

/// 首个可能含无 fixed SSA 身份结果/残值的槽；边界只来自现有原协议摘要。
fn clobber_start(
    instr: &LowInstr,
    effect: &InstrEffect,
    summary: &SideEffectSummary,
) -> Option<usize> {
    let call_start = match (instr, summary.root_observation) {
        // __call 可把原 callee 槽自身改成 tag method；Ignore/开放零返回不会写回该槽。
        (LowInstr::Call(_), RootObservation::Call { caller_end }) => Some(caller_end.index()),
        (LowInstr::GenericForCall(_), RootObservation::PrefixLowerBound { end }) => Some(end),
        _ => None,
    };
    // OPEN 的结果数可能为零；它不能消除更高槽的旧残值。实际写出的结果也没有逐槽 fixed
    // Def，因而同样保留为未知；固定 VARARG 则使用正常 fixed 写清除这些物理残值。
    call_start
        .into_iter()
        .chain(effect.open_must_def.map(Reg::index))
        .min()
}

/// 循环协议的逻辑 binding/control 定义可只在继续边物理写入；退出边仍保留残值。
fn clears_scratch(instr: &LowInstr, reg: Reg) -> bool {
    match instr {
        LowInstr::NumericForInit(init) => reg != init.binding || reg == init.index,
        // PUC 5.1 FORLOOP 在退出边连内部 index 也不写；其它方言不借此假定清空。
        LowInstr::NumericForLoop(_) => false,
        LowInstr::GenericForLoop(loop_) => reg != loop_.control_target,
        _ => true,
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "同一 Dataflow owner 借用原 CFG、效果和 fixed Def 映射，不复制完整分析状态"
)]
pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    effects: &[InstrEffect],
    summaries: &[SideEffectSummary],
    defs: &[Def],
    instr_defs: &[Vec<DefId>],
    reg_count: usize,
    execution: &super::execution::ExecutionFacts,
) -> Vec<bool> {
    let mut transfers = (0..cfg.blocks.len())
        .map(|_| Transfer {
            generated: DenseRegSet::new(reg_count),
            keep: DenseRegSet {
                bits: vec![true; reg_count],
            },
        })
        .collect::<Vec<_>>();
    for &block in &cfg.block_order {
        let transfer = &mut transfers[block.index()];
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            if let Some(start) =
                clobber_start(&proto.instrs[index], &effects[index], &summaries[index])
            {
                transfer.generated.bits[start..].fill(true);
                transfer.keep.bits[start..].fill(false);
            }
            for reg in effects[index].fixed_must_defs() {
                if clears_scratch(&proto.instrs[index], *reg) {
                    transfer.generated.bits[reg.index()] = false;
                    transfer.keep.bits[reg.index()] = false;
                }
            }
        }
    }

    let mut entries = vec![DenseRegSet::new(reg_count); cfg.blocks.len()];
    let mut exits = entries.clone();
    let mut queue = graph
        .rpo
        .iter()
        .copied()
        .filter(|block| execution.blocks[block.index()])
        .collect::<VecDeque<_>>();
    let mut queued = vec![false; cfg.blocks.len()];
    for block in &queue {
        queued[block.index()] = true;
    }
    let mut outgoing = DenseRegSet::new(reg_count);
    while let Some(block) = queue.pop_front() {
        queued[block.index()] = false;
        let transfer = &transfers[block.index()];
        for (slot, value) in outgoing.bits.iter_mut().enumerate() {
            *value = transfer.generated.bits[slot]
                || entries[block.index()].bits[slot] && transfer.keep.bits[slot];
        }
        if outgoing != exits[block.index()] {
            std::mem::swap(&mut outgoing, &mut exits[block.index()]);
            for edge in &cfg.succs[block.index()] {
                let successor = cfg.edges[edge.index()].to;
                // 单调 union 直接投递后继入口，不在高入度 join 每次重扫全部前驱。
                if execution.edges[edge.index()]
                    && execution.blocks[successor.index()]
                    && entries[successor.index()].extend_from(&exits[block.index()])
                    && !queued[successor.index()]
                {
                    queued[successor.index()] = true;
                    queue.push_back(successor);
                }
            }
        }
    }

    let mut overwritten = vec![false; defs.len()];
    for &block in &graph.rpo {
        if !execution.blocks[block.index()] {
            continue;
        }
        let current = &mut entries[block.index()];
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            if let Some(start) =
                clobber_start(&proto.instrs[index], &effects[index], &summaries[index])
            {
                current.bits[start..].fill(true);
            }
            for &def in &instr_defs[index] {
                let slot = defs[def.index()].reg.index();
                overwritten[def.index()] = current.bits[slot];
                if clears_scratch(&proto.instrs[index], defs[def.index()].reg) {
                    current.bits[slot] = false;
                }
            }
        }
    }
    overwritten
}
