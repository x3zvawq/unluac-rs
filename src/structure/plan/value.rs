use super::RegionId;
use crate::structure::{BlockRef, EdgeRef, PhiId, SsaValue};
use crate::transformer::Reg;

/// 一个 canonical phi incoming 在最终结构计划中的唯一语义归属。
///
/// 不可达 incoming 与整项死亡 phi 都归 `Dead`；这样稠密 incoming 槽无需再保留一套
/// 仅供实现使用的“不可达 owner”。其余分类都直接指向最终 region，而不是候选下标。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PhiIncomingDisposition {
    /// 从 region 外部进入其入口的初始值。
    RegionInput(RegionId),
    /// 结构化 region 在 continuation 上产生的结果。
    RegionResult(RegionId),
    /// 循环内部回到 header 的下一轮值。
    LoopCarried(RegionId),
    /// 必须与对应 CFG edge 同时执行的 canonical copy。
    EdgeCopy,
    /// 没有可观察消费者，或 incoming 来自不可达边。
    Dead,
    /// 当前 plan 无法证明唯一结构 owner；宽松模式只能显式诊断。
    DiagnosticUnresolved,
}

impl PhiIncomingDisposition {
    pub const fn region(self) -> Option<RegionId> {
        match self {
            Self::RegionInput(region) | Self::RegionResult(region) | Self::LoopCarried(region) => {
                Some(region)
            }
            Self::EdgeCopy | Self::Dead | Self::DiagnosticUnresolved => None,
        }
    }
}

/// 一个 canonical phi incoming 的冻结计划。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhiIncomingPlan {
    pub edge: Option<EdgeRef>,
    pub value: SsaValue,
    pub disposition: PhiIncomingDisposition,
}

/// 一个 phi 的最终 value plan；诊断所需的 target 与 source 身份都保存在这里。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhiPlan {
    pub phi: PhiId,
    pub block: BlockRef,
    pub reg: Reg,
    pub incomings: Vec<PhiIncomingPlan>,
}

impl PhiPlan {
    pub fn has_unresolved(&self) -> bool {
        self.incomings.iter().any(|incoming| {
            matches!(
                incoming.disposition,
                PhiIncomingDisposition::DiagnosticUnresolved
            )
        })
    }
}
