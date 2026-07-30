use super::{RegionId, ScopePlanId, TbcScopePlanId};

/// 一条 cleanup 指令在最终结构计划中的唯一语义归属。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanupDisposition {
    /// 指令所在 block 不可达，不生成源码。
    Unreachable,
    /// 显式 `<close>` 声明注册点。
    ExplicitTbc,
    /// cleanup 是最终 loop region 的词法结束边界。
    LoopTbcBoundary(RegionId),
    /// 显式 TBC scope 在物理 layout 中的 canonical 词法边界。
    ExplicitTbcBoundary(TbcScopePlanId),
    /// 同一 TBC scope 的其它 CFG 出口；canonical 边界已代表其源码语义。
    ExplicitTbcExit(TbcScopePlanId),
    /// 普通词法 scope 的结束边界。
    LexicalScope(ScopePlanId),
}
