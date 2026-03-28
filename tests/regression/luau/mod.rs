//! 这个模块归档 Luau 的 regression 测试。
//!
//! 这里优先固定那些“CFG 已经可结构化，但一旦回归就会直接退回 goto/unresolved”的
//! case，避免后续继续扩展 Luau parser/transformer 时把已经打通的 HIR 链路重新打断。

mod pipeline;
