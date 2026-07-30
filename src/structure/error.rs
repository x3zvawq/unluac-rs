//! Structure/CFG 分析对输入形状的可诊断错误。

use thiserror::Error;

/// 控制流、region 或 value plan 无法满足最终一致性合同时返回的错误。
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("invalid structure plan: {detail}")]
pub struct StructureError {
    detail: String,
}

impl StructureError {
    pub(crate) fn invalid(detail: impl Into<String>) -> Self {
        Self {
            detail: detail.into(),
        }
    }

    pub(crate) fn context(self, context: impl std::fmt::Display) -> Self {
        Self::invalid(format!("{context}: {}", self.detail))
    }
}
