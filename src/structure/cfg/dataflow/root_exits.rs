//! 冻结当前位置之后直到 frame 退出的无根观察后缀，供生命周期 owner 共享查询。
//!
//! 事实来自 CFG 的向前边与 Dataflow 的观察摘要，不解码调用协议或推断值/声明身份。
//! 例如 `MOVE; if flag then flag=false else flag=true end; RETURN` 的两路共享安全出口；
//! join 不等于循环。回边仍不签发终止证明，Close 或退出前的 GC 观察会截断安全后缀。
//! 按 CFG 已有的指令顺序逆向求解，每条指令与边只处理一次，不为每个覆写重走后缀。

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
