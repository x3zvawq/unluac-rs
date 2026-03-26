//! Naming 层错误。

use thiserror::Error;

/// Naming 阶段可能遇到的结构错误。
#[derive(Debug, Error)]
pub enum NamingError {
    #[error(
        "naming evidence proto count mismatch: parser/raw proto count is {raw_count}, hir proto count is {hir_count}"
    )]
    EvidenceProtoCountMismatch { raw_count: usize, hir_count: usize },
    #[error("ast references function proto#{function}, but that function does not exist in HIR")]
    MissingFunction { function: usize },
    #[error(
        "naming requires readability output without raw temp bindings, but proto#{function} still contains temp t{temp}"
    )]
    UnexpectedTemp { function: usize, temp: usize },
}
