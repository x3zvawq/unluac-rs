//! 跨层共享的可读性配置。
//!
//! 这组参数不是 AST 私有选项：前层 HIR 如果会做影响源码形状的表达式折叠，也必须消费
//! 同一份阈值，避免“前层先压扁、后层再兜底拉回来”的分层漂移。

/// 可调的源码形状阈值。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadabilityOptions {
    pub return_inline_max_complexity: usize,
    pub index_inline_max_complexity: usize,
    pub args_inline_max_complexity: usize,
}

impl Default for ReadabilityOptions {
    fn default() -> Self {
        Self {
            return_inline_max_complexity: 10,
            index_inline_max_complexity: 10,
            args_inline_max_complexity: 6,
        }
    }
}
