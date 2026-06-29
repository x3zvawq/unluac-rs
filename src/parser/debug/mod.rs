//! 这个文件承载 parser 层对外暴露的调试入口。
//!
//! 具体某个 dialect 的 dump 逻辑放在各自目录里，这里只负责从主 pipeline state
//! 读取 parser 产物并根据解析结果做分派；跨 dialect 的 traversal/focus/基础格式化
//! 放在 `common`，避免每个 dialect debug 文件复制同一套展示语义。

mod common;

pub(crate) use common::{
    ParserProtoEntry, build_parser_summary_row, collect_parser_proto_entries, format_endianness,
    format_literal, format_optional_line, format_optional_raw_word, format_optional_source,
    format_optional_u32, format_origin, format_raw_string, plan_parser_focus, write_elided_summary,
};

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, define_stage_dump};
use crate::decompile::DecompileDialect;

use super::RawChunk;
use super::dialect::lua51;
use super::dialect::lua52;
use super::dialect::lua53;
use super::dialect::lua54;
use super::dialect::lua55;
use super::dialect::luajit;
use super::dialect::luau;

define_stage_dump! {
    /// Parser 阶段的调试导出。
    pub fn dump_parser(state, options) => Parser,
        dump_parser_chunk(
            state.require_raw_chunk()?,
            options.detail,
            &options.filters,
            options.color
        );
}

/// 根据 chunk 的实际 dialect 分派到对应的 parser dump 实现。
fn dump_parser_chunk(
    chunk: &RawChunk,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    match chunk.header.version {
        DecompileDialect::Lua51 => lua51::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Lua52 => lua52::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Lua53 => lua53::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Lua54 => lua54::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Lua55 => lua55::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Luajit => luajit::dump_chunk(chunk, detail, filters, color),
        DecompileDialect::Luau => luau::dump_chunk(chunk, detail, filters, color),
    }
}
