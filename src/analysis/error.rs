//! Analysis 层错误类型。
//!
//! 仅在输入 Low-IR 存在越界目标或非法图结构时返回显式错误，
//! 不因高阶控制流形状复杂而中断分析。

use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum AnalysisError {
    #[error("proto#{proto} instruction @{instr} jumps to out-of-range target @{target}")]
    InvalidJumpTarget {
        proto: usize,
        instr: usize,
        target: usize,
    },
    #[error("proto#{proto} dominator tree computation failed: {detail}")]
    DominatorFailure { proto: usize, detail: String },
}
