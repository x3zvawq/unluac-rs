//! 这个文件定义跨 Structure、HIR 与 AST 共享的 proto 级恢复诊断。
//!
//! 单个 proto 失败时，后序 pipeline 仍需要保留它在 proto 树中的稳定位置，并说明失败发生
//! 在哪一层、最后完成了哪一层以及当时可观察到的中间产物。这里仅承载这份诊断事实，
//! 不决定是否恢复；Strict/Permissive 策略仍由各阶段入口负责。

use std::fmt;
use std::sync::Arc;

/// proto 内部可独立观察的恢复层次。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ProtoArtifactStage {
    Dataflow,
    Structure,
    Hir,
}

impl fmt::Display for ProtoArtifactStage {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Dataflow => "dataflow",
            Self::Structure => "structure",
            Self::Hir => "hir",
        })
    }
}

/// 一个 proto 停止推进时保留下来的失败事实与最后成功产物。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ProtoFailure {
    pub proto: usize,
    pub failed_stage: ProtoArtifactStage,
    pub last_completed_stage: ProtoArtifactStage,
    pub error: Arc<str>,
    pub last_completed_dump: Arc<str>,
}

impl ProtoFailure {
    pub(crate) fn diagnostic(&self) -> String {
        format!(
            "proto#{} failed during {}: {}\nlast completed stage: {}\n{}",
            self.proto,
            self.failed_stage,
            self.error,
            self.last_completed_stage,
            self.last_completed_dump.trim_end(),
        )
    }
}
