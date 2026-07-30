//! 这个文件定义 low-IR 到 HIR 恢复阶段的可诊断错误。
//!
//! 结构计划来自用户输入字节码的控制流分析；计划无法完整降低时必须沿 pipeline
//! 返回错误，不能用 panic 把不受信任的输入升级成进程崩溃。

use thiserror::Error;

use crate::structure::BlockRef;

/// low-IR 到 HIR 恢复期间可能产生的错误。
#[derive(Debug, Error)]
pub enum HirLowerError {
    #[error("HIR proto#{proto} could not lower the structure region starting at block {block}")]
    UnlowerableStructureRegion { proto: usize, block: BlockRef },
    #[error("HIR proto#{proto} structure plan left reachable block {block} uncovered")]
    UncoveredReachableBlock { proto: usize, block: BlockRef },
    #[error("HIR proto#{proto} references missing structure region#{region}")]
    MissingPlanRegion { proto: usize, region: usize },
    #[error("HIR proto#{proto} references missing {kind} plan payload#{id}")]
    MissingPlanPayload {
        proto: usize,
        kind: &'static str,
        id: usize,
    },
    #[error("HIR proto#{proto} has invalid structure region#{region}: {detail}")]
    InvalidPlanRegion {
        proto: usize,
        region: usize,
        detail: &'static str,
    },
}
