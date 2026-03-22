//! 这个目录承载 Lua 5.1 的 transformer 实现。
//!
//! 这里集中放 Lua 5.1 raw 指令到统一 low-IR 的 lowering 规则，避免这些强
//! 方言语义污染公共 transformer 入口。

mod lower;

pub(crate) use lower::lower_chunk;
