//! 这个模块选择 Lua 5.5 typed raw 协议并交给 5.4/5.5 共享 lowerer。

use crate::parser::RawChunk;
use crate::transformer::dialect::puc_lua::lua54_55::{self, FamilyDialect};
use crate::transformer::{LoweredChunk, TransformError};

pub(crate) fn lower_chunk(chunk: &RawChunk) -> Result<LoweredChunk, TransformError> {
    lua54_55::lower_chunk(chunk, FamilyDialect::Lua55)
}
