//! 冻结 canonical phi 的逐输入处置及循环状态身份。
//!
//! 消费最终 owner 和原 incoming，向 HIR 发布唯一值转移归属。

use super::{RegionId, RegionPlan};
use crate::structure::{BlockRef, EdgeRef, PhiId, SsaValue, StructurePlan};
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
    pub(in crate::structure) loop_carried_input: Option<usize>,
}

impl PhiPlan {
    pub fn loop_carried(&self) -> Option<LoopCarriedPhi> {
        let input = &self.incomings[self.loop_carried_input?];
        let PhiIncomingDisposition::RegionInput(owner) = input.disposition else {
            unreachable!("certified loop input remains a RegionInput");
        };
        Some(LoopCarriedPhi {
            owner,
            input: input.value,
        })
    }

    pub fn has_unresolved(&self) -> bool {
        self.incomings.iter().any(|incoming| {
            matches!(
                incoming.disposition,
                PhiIncomingDisposition::DiagnosticUnresolved
            )
        })
    }
}

/// 最终 incoming 共同证明的循环 owner 与唯一入口值，不包含 HIR binding 分配决定。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopCarriedPhi {
    pub owner: RegionId,
    pub input: SsaValue,
}

pub(in crate::structure) fn loop_carried_input(
    plan: &StructurePlan,
    incomings: &[PhiIncomingPlan],
) -> Option<usize> {
    let mut owner = None;
    let mut input = None;
    let mut has_carried = false;
    for (index, incoming) in incomings.iter().enumerate() {
        let region = match incoming.disposition {
            PhiIncomingDisposition::RegionInput(region) => {
                if input.replace(index).is_some() {
                    return None;
                }
                region
            }
            PhiIncomingDisposition::LoopCarried(region) => {
                has_carried = true;
                region
            }
            PhiIncomingDisposition::Dead => continue,
            PhiIncomingDisposition::RegionResult(_)
            | PhiIncomingDisposition::EdgeCopy
            | PhiIncomingDisposition::DiagnosticUnresolved => return None,
        };
        if owner.replace(region).is_some_and(|owner| owner != region) {
            return None;
        }
    }
    let owner = owner?;
    (has_carried && matches!(plan.region(owner), Some(RegionPlan::Loop { .. }))).then_some(input?)
}
