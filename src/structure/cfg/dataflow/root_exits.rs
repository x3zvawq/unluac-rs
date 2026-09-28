//! 冻结直到 frame 退出的无根观察后缀。
//!
//! 消费 CFG 与观察摘要，为生命周期 owner 提供共享查询，不推断值或声明身份。

use super::{Cfg, RootObservation, SideEffectSummary};

pub(super) fn unobserved_forward_exits(cfg: &Cfg, summaries: &[SideEffectSummary]) -> Vec<bool> {
    let mut after = vec![false; summaries.len()];
    let mut at_entry = vec![false; cfg.blocks.len()];
    // block_order 由 CFG builder 按原指令位置发布，排除 synthetic exit。
    for &block in cfg.block_order.iter().rev() {
        let range = cfg.blocks[block.index()].instrs;
        let successors = cfg.reachable_successors(block);
        let mut safe = !successors.is_empty()
            && successors.iter().all(|successor| {
                let next = cfg.blocks[successor.index()].instrs;
                !next.is_empty() && next.start.index() >= range.end() && at_entry[successor.index()]
            });
        for index in (range.start.index()..range.end()).rev() {
            after[index] = safe;
            let summary = &summaries[index];
            safe = match summary.root_observation {
                RootObservation::FrameExit => true,
                RootObservation::Close { .. } => false,
                _ => safe && !summary.may_observe_gc_roots(),
            };
        }
        at_entry[block.index()] = safe;
    }
    after
}
