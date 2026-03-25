//! 这个目录承载 Lua 5.3 的 transformer 实现。
//!
//! Lua 5.3 延续了 5.2 的 `GETTABUP/SETTABUP`、`LOADKX/EXTRAARG`、分离的
//! `TFORCALL/TFORLOOP` 和 `JMP(A)` close 语义，同时新增了整除和位运算 opcode；
//! 这些规则都应该在这里被一次性 lowering 成统一 low-IR。

mod lower;

pub(crate) use lower::lower_chunk;
