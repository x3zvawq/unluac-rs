//! Lua 5.2 的层内契约测试入口。
//!
//! 这里先覆盖 parser/transformer 两层，确保 5.2 新增的 upvalue-table 访问、
//! generic-for pair 和 close 语义都已经在进入 CFG 前被稳定表达出来。

mod parser;
mod transformer;
