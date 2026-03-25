//! 这个文件承载 parser 层对外暴露的调试入口。
//!
//! 具体某个 dialect 的 dump 逻辑放在各自目录里，这里只负责根据解析结果做
//! 分派。

use crate::debug::{DebugDetail, DebugFilters};

use super::dialect::lua51;
use super::dialect::lua52;
use super::{DialectVersion, RawChunk};

/// 根据 chunk 的实际 dialect 分派到对应的 parser dump 实现。
pub fn dump_parser(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    match chunk.header.version {
        DialectVersion::Lua51 => lua51::dump_chunk(chunk, detail, filters),
        DialectVersion::Lua52 => lua52::dump_chunk(chunk, detail, filters),
    }
}
