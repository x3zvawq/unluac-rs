//! 这个文件实现 Lua 5.4 chunk 的实际解析逻辑。
//!
//! Lua 5.4 的 header/proto/debug 布局已经明显偏离 5.3：opcode 扩成 7 bit，
//! `int/size_t` 风格的计数都改成 varint，upvalue 描述符多了 `kind`，而行号信息
//! 也变成 `lineinfo + abslineinfo` 两段式。这里按真实格式显式实现，避免把这些
//! 差异硬塞回 5.3 的读取路径。

use crate::parser::dialect::puc_lua::{
    AbsDebugDriver, AbsLineInfoConfig, LUA54_LUAC_DATA, LUA54_LUAC_INT, LUA54_LUAC_NUM,
    PucLuaLayout, PucLuaProtoSections, build_raw_string, count_u8, decode_instruction_word_54,
    define_puc_lua_instruction_codec, finish_puc_lua_proto, inherit_source,
    parse_abs_debug_sections, parse_child_protos, parse_luac_data_header_prelude,
    parse_puc_lua_instruction_section, parse_tagged_literal_pool, parse_upvalues_with_kinds,
    read_f64_sentinel, read_i64_sentinel_endianness, read_layout_lua_integer, read_proto_prelude,
    require_present, validate_instruction_word_size, validate_main_proto_upvalue_count,
    validate_optional_count_match,
};
use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Origin, ProtoSignature, PucLuaChunkLayout, RawChunk, RawConstPool, RawConstPoolCommon,
    RawDebugInfo, RawInstrOpcode, RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto,
    RawString, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua54AbsLineInfo, Lua54ConstPoolExtra, Lua54DebugExtra, Lua54ExtraWordPolicy, Lua54HeaderExtra,
    Lua54InstrExtra, Lua54Opcode, Lua54ProtoExtra, Lua54UpvalueExtra,
};

const LUA54_VERSION: u8 = 0x54;
const LUA54_FORMAT: u8 = 0;
const LUA_VNIL: u8 = 0;
const LUA_VFALSE: u8 = 1;
const LUA_VTRUE: u8 = 17;
const LUA_VNUMINT: u8 = 3;
const LUA_VNUMFLT: u8 = 19;
const LUA_VSHRSTR: u8 = 4;
const LUA_VLNGSTR: u8 = 20;
const ABSLINEINFO: i8 = -0x80;

pub(crate) struct Lua54Parser {
    options: ParseOptions,
}

struct Lua54AbsDebugDriver<'a> {
    parser: &'a Lua54Parser,
    upvalue_count: u8,
}

impl<'a, 'bytes> AbsDebugDriver<'bytes> for Lua54AbsDebugDriver<'a> {
    fn read_count(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        reader.read_varint_u32_lua54(field)
    }

    fn read_line_delta(&mut self, reader: &mut BinaryReader<'bytes>) -> Result<i8, ParseError> {
        Ok(reader.read_u8()? as i8)
    }

    fn prepare_abs_line_info(
        &mut self,
        _: &mut BinaryReader<'bytes>,
        _: u32,
    ) -> Result<(), ParseError> {
        Ok(())
    }

    fn read_abs_line_pair(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<(u32, u32), ParseError> {
        Ok((
            reader.read_varint_u32_lua54("abs line info pc")?,
            reader.read_varint_u32_lua54("abs line info line")?,
        ))
    }

    fn parse_local_var(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<RawLocalVar, ParseError> {
        Ok(RawLocalVar {
            name: require_present(
                self.parser.parse_optional_string(reader)?,
                "local var name length",
            )?,
            start_pc: reader.read_varint_u32_lua54("local var startpc")?,
            end_pc: reader.read_varint_u32_lua54("local var endpc")?,
        })
    }

    fn validate_upvalue_count(&mut self, count: u32) -> Result<(), ParseError> {
        validate_optional_count_match(
            self.parser.options.mode.is_permissive(),
            "upvalue name count",
            count,
            self.upvalue_count,
        )
    }

    fn parse_upvalue_name(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parser.parse_optional_string(reader)
    }
}

impl Lua54Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let header_layout = header
            .puc_lua_layout()
            .expect("lua54 parser must produce a PUC-Lua header layout");
        let layout = PucLuaLayout {
            endianness: header_layout.endianness,
            integer_size: 0,
            lua_integer_size: header_layout.lua_integer_size,
            size_t_size: 0,
            instruction_size: header_layout.instruction_size,
            number_size: header_layout.number_size,
            integral_number: false,
        };
        let main_upvalue_count = reader.read_u8()?;
        let main = self.parse_proto(&mut reader, &layout, None)?;

        validate_main_proto_upvalue_count(
            self.options.mode.is_permissive(),
            main_upvalue_count,
            main.common.upvalues.common.count,
        )?;

        Ok(RawChunk {
            header,
            main,
            origin: Origin {
                span: Span {
                    offset: 0,
                    size: bytes.len(),
                },
                raw_word: None,
            },
        })
    }

    fn parse_header(&self, reader: &mut BinaryReader<'_>) -> Result<ChunkHeader, ParseError> {
        let start = parse_luac_data_header_prelude(
            reader,
            LUA54_VERSION,
            LUA54_FORMAT,
            LUA54_LUAC_DATA,
            self.options.mode.is_permissive(),
        )?;

        let instruction_size = reader.read_u8()?;
        let lua_integer_size = reader.read_u8()?;
        let number_size = reader.read_u8()?;

        validate_instruction_word_size(instruction_size)?;

        let endianness = read_i64_sentinel_endianness(
            reader,
            lua_integer_size,
            LUA54_LUAC_INT,
            "lua_Integer",
            "luac_int",
            self.options.mode.is_permissive(),
        )?;
        read_f64_sentinel(
            reader,
            number_size,
            endianness,
            LUA54_LUAC_NUM,
            "number_size",
            "luac_num",
            self.options.mode.is_permissive(),
        )?;

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua54,
            layout: ChunkLayout::PucLua(PucLuaChunkLayout {
                format: LUA54_FORMAT,
                endianness,
                integer_size: 0,
                lua_integer_size: Some(lua_integer_size),
                size_t_size: 0,
                instruction_size,
                number_size,
                integral_number: false,
            }),
            extra: DialectHeaderExtra::Lua54(Lua54HeaderExtra),
            origin: Origin {
                span: Span {
                    offset: start,
                    size: reader.offset() - start,
                },
                raw_word: None,
            },
        })
    }

    fn parse_proto(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let (prelude, header_source) = read_proto_prelude(
            reader,
            |reader| self.parse_optional_string(reader),
            |reader, field| reader.read_varint_u32_lua54(field),
        )?;
        let source = inherit_source(header_source, parent_source);
        let raw_is_vararg = prelude.raw_flag;

        let (raw_instruction_words, instructions) =
            parse_puc_lua_instruction_section::<Lua54InstructionCodec, _, _>(
                reader,
                layout,
                |reader, field| reader.read_varint_u32_lua54(field),
                |_, _| Ok(()),
                "instruction",
            )?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader)?;
        let child_count = reader.read_varint_u32_lua54("child proto count")?;
        let children = parse_child_protos(child_count, || {
            self.parse_proto(reader, layout, source.as_ref())
        })?;
        let debug_info = self.parse_debug_info(
            reader,
            raw_instruction_words,
            prelude.line_range.defined_start,
            upvalues.common.count,
        )?;

        Ok(finish_puc_lua_proto(
            prelude,
            source,
            ProtoSignature {
                num_params: prelude.num_params,
                is_vararg: raw_is_vararg != 0,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            PucLuaProtoSections {
                instructions,
                constants,
                upvalues,
                debug_info,
                children,
            },
            DialectProtoExtra::Lua54(Lua54ProtoExtra { raw_is_vararg }),
            reader.offset(),
        ))
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<RawConstPool, ParseError> {
        let literals = parse_tagged_literal_pool(
            reader,
            |reader, field| reader.read_varint_u32_lua54(field),
            |tag, offset, reader| {
                Ok(match tag {
                    LUA_VNIL => RawLiteralConst::Nil,
                    LUA_VFALSE => RawLiteralConst::Boolean(false),
                    LUA_VTRUE => RawLiteralConst::Boolean(true),
                    LUA_VNUMFLT => RawLiteralConst::Number(
                        reader.read_f64_sized(layout.number_size, layout.endianness)?,
                    ),
                    LUA_VNUMINT => RawLiteralConst::Integer(read_layout_lua_integer(
                        reader,
                        layout,
                        "lua_Integer",
                        "lua54",
                    )?),
                    LUA_VSHRSTR | LUA_VLNGSTR => {
                        let value =
                            require_present(self.parse_string(reader)?, "string constant length")?;
                        RawLiteralConst::String(value)
                    }
                    _ => return Err(ParseError::InvalidConstantTag { offset, tag }),
                })
            },
        )?;

        Ok(RawConstPool {
            common: RawConstPoolCommon { literals },
            extra: DialectConstPoolExtra::Lua54(Lua54ConstPoolExtra),
        })
    }

    fn parse_upvalues(&self, reader: &mut BinaryReader<'_>) -> Result<RawUpvalueInfo, ParseError> {
        let count = reader.read_varint_u32_lua54("upvalue count")?;
        let count_u8 = count_u8(count, "upvalue count")?;
        let (descriptors, kinds) = parse_upvalues_with_kinds(reader, count)?;

        Ok(RawUpvalueInfo {
            common: RawUpvalueInfoCommon {
                count: count_u8,
                descriptors,
            },
            extra: DialectUpvalueExtra::Lua54(Lua54UpvalueExtra { kinds }),
        })
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        raw_instruction_words: usize,
        defined_start: u32,
        upvalue_count: u8,
    ) -> Result<RawDebugInfo, ParseError> {
        let mut driver = Lua54AbsDebugDriver {
            parser: self,
            upvalue_count,
        };
        let sections = parse_abs_debug_sections(
            reader,
            AbsLineInfoConfig {
                raw_instruction_words,
                defined_start,
                abslineinfo_marker: ABSLINEINFO,
                permissive: self.options.mode.is_permissive(),
            },
            &mut driver,
        )?;
        let abs_line_info = sections
            .abs_line_pairs
            .into_iter()
            .map(|(pc, line)| Lua54AbsLineInfo { pc, line })
            .collect();

        Ok(RawDebugInfo {
            common: sections.common,
            extra: DialectDebugExtra::Lua54(Lua54DebugExtra {
                line_deltas: sections.line_deltas,
                abs_line_info,
            }),
        })
    }

    fn parse_optional_string(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader)
    }

    fn parse_string(&self, reader: &mut BinaryReader<'_>) -> Result<Option<RawString>, ParseError> {
        let size = reader.read_varint_u64_lua54(u64::MAX, "string size")?;
        if size == 0 {
            return Ok(None);
        }

        let payload_size = size.checked_sub(1).ok_or(ParseError::UnsupportedValue {
            field: "string size",
            value: size,
        })?;
        let byte_count =
            usize::try_from(payload_size).map_err(|_| ParseError::IntegerOverflow {
                field: "string size",
                value: payload_size,
            })?;
        let offset = reader.offset();
        let bytes = reader.read_exact(byte_count)?.to_vec();
        Ok(Some(build_raw_string(
            self.options,
            offset,
            bytes,
            byte_count,
        )?))
    }
}

define_puc_lua_instruction_codec!(
    codec: Lua54InstructionCodec,
    opcode: Lua54Opcode,
    fields: crate::parser::dialect::puc_lua::DecodedInstructionFields54,
    extra_word_policy: Lua54ExtraWordPolicy,
    operands: super::raw::Lua54Operands,
    decode_fields: decode_instruction_word_54,
    extra_arg_opcode: Lua54Opcode::ExtraArg,
    should_read_extra_word: |policy, fields| match policy {
        Lua54ExtraWordPolicy::None => false,
        Lua54ExtraWordPolicy::ExtraArg => true,
        Lua54ExtraWordPolicy::ExtraArgIfK => fields.k,
    },
    wrap_opcode: RawInstrOpcode::Lua54,
    wrap_operands: RawInstrOperands::Lua54,
    wrap_extra: |pc, word_len, extra_arg| DialectInstrExtra::Lua54(Lua54InstrExtra {
        pc,
        word_len,
        extra_arg,
    }),
);
