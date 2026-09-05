//! 保存原始 cleanup 指令的唯一执行位置及物理入边事件。
//!
//! origin 来自 Structure 的 CFG may-flow；本模块不恢复 HIR 词法作用域。
//! 例如两条入边分别携带 A 和空集，汇合处 Close(A) 分别冻结为 Close(A) 和无事件，
//! 原指令只保留 label 锚点，不因另一条相同 origin 的 Close 存在而丢失自己的执行。

use super::{RegionId, ScopePlanId};

/// 目标 block 的显式入口 Close 在这条物理入边上的执行事件。
/// origins 由入边 may-out 与原指令实际关闭集合的交集冻结；空交集不产生事件。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdgeCleanupAction {
    pub instr: crate::transformer::InstrRef,
    pub origins: Vec<crate::transformer::InstrRef>,
}

/// 一条 cleanup 指令在最终结构计划中的唯一语义归属。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanupDisposition {
    /// 指令所在 block 不可达，不生成源码。
    Unreachable,
    /// 显式 `<close>` 声明注册点。
    ExplicitTbc,
    /// cleanup 是最终 loop region 的词法结束边界。
    LoopTbcBoundary(RegionId),
    /// 原指令位置执行的 TBC 关闭事件，不与其它同 origins 的 Close 合并。
    ExplicitClose,
    /// 入口 Close 已由全部真实入边各自拥有，原 block 只保留 label 的位置锚点。
    IncomingEdges,
    /// 普通词法 scope 的结束边界。
    LexicalScope(ScopePlanId),
}
