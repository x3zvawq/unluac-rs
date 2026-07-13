//! 这个目录承载 Lua 5.3 的 transformer 实现。
//!
//! Lua 5.3 延续了 5.2 的 `GETTABUP/SETTABUP`、`LOADKX/EXTRAARG`、分离的
//! `TFORCALL/TFORLOOP` 和 `JMP(A)` close 语义，同时新增了整除和位运算 opcode；
//! 这些规则都应该在这里被一次性 lowering 成统一 low-IR。

use crate::parser::RawChunk;
use crate::transformer::dialect::puc_lua::lua52_53::{self, FamilyDialect};
use crate::transformer::{LoweredChunk, TransformError};

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    lua52_53::lower_chunk(chunk, FamilyDialect::Lua53)
}
