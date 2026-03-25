//! 这个模块归档 Lua 5.5 的 regression 测试。
//!
//! 当前先锁 parser/transformer/HIR 已经能稳定覆盖 `global` 和 named-vararg table
//! 这两类 5.5 核心新增语义；clean-HIR 总回归等 AST 路线更稳定后再决定是否打开。

mod pipeline;
