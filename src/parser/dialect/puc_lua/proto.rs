//! 这个模块承载 PUC-Lua family 共享的 proto 外层骨架。
//!
//! 它只负责“proto 公共前导字段怎么收口、父 source 怎么继承、公共 RawProto 怎么组装”
//! 这些跨版本稳定事实；真正的 section 读取顺序和版本语义仍留在各个 parser 里。

use crate::parser::error::ParseError;
use crate::parser::raw::{
    DialectProtoExtra, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawConstPool,
    RawDebugInfo, RawInstr, RawProto, RawProtoCommon, RawString, RawUpvalueInfo, Span,
};
use crate::parser::reader::BinaryReader;

#[derive(Debug, Clone, Copy)]
pub(crate) struct PucLuaProtoPrelude {
    pub(crate) start: usize,
    pub(crate) line_range: ProtoLineRange,
    pub(crate) num_params: u8,
    pub(crate) raw_flag: u8,
    pub(crate) max_stack_size: u8,
}

#[derive(Debug)]
pub(crate) struct PucLuaProtoSections {
    pub(crate) instructions: Vec<RawInstr>,
    pub(crate) constants: RawConstPool,
    pub(crate) upvalues: RawUpvalueInfo,
    pub(crate) debug_info: RawDebugInfo,
    pub(crate) children: Vec<RawProto>,
}

pub(crate) fn read_proto_prelude<ReadSource, ReadLine>(
    reader: &mut BinaryReader<'_>,
    mut read_source: ReadSource,
    mut read_line: ReadLine,
) -> Result<(PucLuaProtoPrelude, Option<RawString>), ParseError>
where
    ReadSource: FnMut(&mut BinaryReader<'_>) -> Result<Option<RawString>, ParseError>,
    ReadLine: FnMut(&mut BinaryReader<'_>, &'static str) -> Result<u32, ParseError>,
{
    let start = reader.offset();
    let source = read_source(reader)?;
    let defined_start = read_line(reader, "linedefined")?;
    let defined_end = read_line(reader, "lastlinedefined")?;
    let num_params = reader.read_u8()?;
    let raw_flag = reader.read_u8()?;
    let max_stack_size = reader.read_u8()?;

    Ok((
        PucLuaProtoPrelude {
            start,
            line_range: ProtoLineRange {
                defined_start,
                defined_end,
            },
            num_params,
            raw_flag,
            max_stack_size,
        },
        source,
    ))
}

pub(crate) fn inherit_source(
    local_source: Option<RawString>,
    parent_source: Option<&RawString>,
) -> Option<RawString> {
    local_source.or_else(|| parent_source.cloned())
}

pub(crate) fn finish_puc_lua_proto(
    prelude: PucLuaProtoPrelude,
    source: Option<RawString>,
    signature: ProtoSignature,
    sections: PucLuaProtoSections,
    extra: DialectProtoExtra,
    end_offset: usize,
) -> RawProto {
    RawProto {
        common: RawProtoCommon {
            source,
            line_range: prelude.line_range,
            signature,
            frame: ProtoFrameInfo {
                max_stack_size: prelude.max_stack_size,
            },
            instructions: sections.instructions,
            constants: sections.constants,
            upvalues: sections.upvalues,
            debug_info: sections.debug_info,
            children: sections.children,
        },
        extra,
        origin: Origin {
            span: Span {
                offset: prelude.start,
                size: end_offset - prelude.start,
            },
            raw_word: None,
        },
    }
}
