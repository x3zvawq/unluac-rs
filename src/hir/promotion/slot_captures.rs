//! 计算每个程序点之前物理槽是否可能仍有开放的引用捕获。
//!
//! 消费 Transformer 的 Capture/Close 与共享 CFG；不从 HIR closure 文本重建路径。
//! Capture 建立开放 cell，覆盖槽值不关闭 cell，Close 则终止它。例如先 `f(t.x)`、后在
//! 同一寄存器建立捕获 local，不能把未来的捕获当作先前参数槽仍属于 caller 的证据。
//! 先汇总块内生成与关闭，再传播单调的入口 may 位；每块最多入队一次，回边也参与合流。

use super::{CaptureSource, Cfg, LowInstr, LoweredProto, Reg, VecDeque};

pub(super) fn before_instructions(proto: &LoweredProto, cfg: &Cfg, reg: Reg) -> Vec<bool> {
    let mut closes = vec![false; cfg.blocks.len()];
    let mut outgoing = vec![false; cfg.blocks.len()];
    let mut pending = VecDeque::new();
    for block in &cfg.reachable_blocks {
        let range = cfg.blocks[block.index()].instrs;
        for instr in &proto.instrs[range.start.index()..range.end()] {
            if let Some(open) = transition(instr, reg) {
                closes[block.index()] |= !open;
                outgoing[block.index()] = open;
            }
        }
        if outgoing[block.index()] {
            pending.push_back(*block);
        }
    }
    let mut incoming = vec![false; cfg.blocks.len()];
    while let Some(block) = pending.pop_front() {
        for successor in cfg.reachable_successors(block) {
            if incoming[successor.index()] {
                continue;
            }
            incoming[successor.index()] = true;
            if !closes[successor.index()] && !outgoing[successor.index()] {
                outgoing[successor.index()] = true;
                pending.push_back(successor);
            }
        }
    }
    let mut before = vec![false; proto.instrs.len()];
    for block in &cfg.reachable_blocks {
        let range = cfg.blocks[block.index()].instrs;
        let mut open = incoming[block.index()];
        for (index, before) in before
            .iter_mut()
            .enumerate()
            .take(range.end())
            .skip(range.start.index())
        {
            *before = open;
            if let Some(next) = transition(&proto.instrs[index], reg) {
                open = next;
            }
        }
    }
    before
}

fn transition(instr: &LowInstr, reg: Reg) -> Option<bool> {
    match instr {
        LowInstr::Close(close) if close.from.index() <= reg.index() => Some(false),
        LowInstr::Closure(closure)
            if closure
                .captures
                .iter()
                .any(|capture| capture.source == CaptureSource::ByReference(reg)) =>
        {
            Some(true)
        }
        _ => None,
    }
}
