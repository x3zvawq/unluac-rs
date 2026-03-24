//! 这个模块承载 StructureFacts 层的共享实现。
//!
//! 从这一层开始，我们正式把图事实和数据流事实转成更贴近源码恢复的候选集合，
//! 但仍然刻意停在“候选/约束”层，不替 HIR 过早做最终语法决定。

mod analyze;
mod branches;
mod common;
mod debug;
mod goto;
mod helpers;
mod loops;
mod regions;
mod scope;
mod short_circuit;

pub use analyze::analyze_structure;
pub use common::{
    BranchCandidate, BranchKind, GotoReason, GotoRequirement, LoopCandidate, LoopKindHint,
    RegionFact, RegionKind, ScopeCandidate, ScopeKind, ShortCircuitCandidate, ShortCircuitKindHint,
    StructureFacts,
};
pub use debug::dump_structure;
