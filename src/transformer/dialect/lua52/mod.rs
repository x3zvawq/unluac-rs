//! 这个目录承载 Lua 5.2 的 transformer 实现。
//!
//! Lua 5.2 相比 5.1 引入了 `GETTABUP/SETTABUP`、`LOADKX/EXTRAARG`、分离的
//! `TFORCALL/TFORLOOP`，以及 `JMP(A)` 的 close 语义；这些规则都应该在这里被
//! 一次性 lowering 掉，而不是留给 low-IR 消费方继续猜。

use crate::parser::RawChunk;
use crate::transformer::dialect::puc_lua::lua52_53::{self, FamilyDialect};
use crate::transformer::{LoweredChunk, TransformError};

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    lua52_53::lower_chunk(chunk, FamilyDialect::Lua52)
}
