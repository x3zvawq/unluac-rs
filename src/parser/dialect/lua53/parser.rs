//! 这个文件实现 Lua 5.3 chunk 的实际解析逻辑。
//!
//! 它复用 PUC-Lua 家族共享的位域拆解 helper，同时显式保留 5.3 自己的
//! header 校验、字符串长度编码、整数/浮点常量标签，以及新增位运算 opcode 的
//! 解析规则，避免把版本差异揉成一个“差不多能用”的弱抽象。

use crate::parser::dialect::puc_lua::{
    ClassicDebugDriver, LUA53_LUAC_DATA, LUA53_LUAC_INT, LUA53_LUAC_NUM, PucLuaLayout,
    PucLuaProtoSections, build_raw_string, count_u8, decode_instruction_word,
    define_puc_lua_instruction_codec, finish_puc_lua_proto, inherit_source, parse_child_protos,
    parse_classic_debug_sections, parse_luac_data_header_prelude,
    parse_puc_lua_instruction_section, parse_tagged_literal_pool, parse_upvalue_descriptors,
    read_f64_sentinel, read_i64_sentinel_endianness, read_layout_lua_integer, read_proto_prelude,
    read_sized_u32, require_present, validate_instruction_word_size,
    validate_main_proto_upvalue_count,
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
    Lua53ConstPoolExtra, Lua53DebugExtra, Lua53ExtraWordPolicy, Lua53HeaderExtra, Lua53InstrExtra,
    Lua53Opcode, Lua53ProtoExtra, Lua53UpvalueExtra,
};

const LUA53_VERSION: u8 = 0x53;
const LUA53_FORMAT: u8 = 0;
const LUA_TNIL: u8 = 0;
const LUA_TBOOLEAN: u8 = 1;
const LUA_TNUMBER: u8 = 3;
const LUA_TSHRSTR: u8 = 4;
const LUA_TNUMFLT: u8 = LUA_TNUMBER;
const LUA_TLNGSTR: u8 = LUA_TSHRSTR | (1 << 4);
const LUA_TNUMINT: u8 = LUA_TNUMBER | (1 << 4);
const LUA53_LONG_STRING_MARKER: u8 = 0xff;

pub(crate) struct Lua53Parser {
    options: ParseOptions,
}

struct Lua53ClassicDebugDriver<'a> {
    parser: &'a Lua53Parser,
    layout: &'a PucLuaLayout,
}

impl<'a, 'bytes> ClassicDebugDriver<'bytes> for Lua53ClassicDebugDriver<'a> {
    fn read_source(
        &mut self,
        _: &mut BinaryReader<'bytes>,
    ) -> Result<Option<RawString>, ParseError> {
        Ok(None)
    }

    fn read_count(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        self.parser.read_count(reader, self.layout, field)
    }

    fn read_line(&mut self, reader: &mut BinaryReader<'bytes>) -> Result<u32, ParseError> {
        read_sized_u32(reader, self.layout, "line info")
    }

    fn parse_local_var(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<RawLocalVar, ParseError> {
        Ok(RawLocalVar {
            name: require_present(
                self.parser.parse_string(reader, self.layout)?,
                "local var name length",
            )?,
            start_pc: read_sized_u32(reader, self.layout, "local var startpc")?,
            end_pc: read_sized_u32(reader, self.layout, "local var endpc")?,
        })
    }

    fn validate_upvalue_count(&mut self, _: u32) -> Result<(), ParseError> {
        Ok(())
    }

    fn parse_upvalue_name(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parser.parse_string(reader, self.layout)
    }
}

impl Lua53Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let header_layout = header
            .puc_lua_layout()
            .expect("lua53 parser must produce a PUC-Lua header layout");
        let layout = PucLuaLayout {
            endianness: header_layout.endianness,
            integer_size: header_layout.integer_size,
            lua_integer_size: header_layout.lua_integer_size,
            size_t_size: header_layout.size_t_size,
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
            LUA53_VERSION,
            LUA53_FORMAT,
            LUA53_LUAC_DATA,
            self.options.mode.is_permissive(),
        )?;

        let integer_size = reader.read_u8()?;
        let size_t_size = reader.read_u8()?;
        let instruction_size = reader.read_u8()?;
        let lua_integer_size = reader.read_u8()?;
        let number_size = reader.read_u8()?;

        validate_instruction_word_size(instruction_size)?;

        let endianness = read_i64_sentinel_endianness(
            reader,
            lua_integer_size,
            LUA53_LUAC_INT,
            "lua_Integer",
            "luac_int",
            self.options.mode.is_permissive(),
        )?;
        read_f64_sentinel(
            reader,
            number_size,
            endianness,
            LUA53_LUAC_NUM,
            "number_size",
            "luac_num",
            self.options.mode.is_permissive(),
        )?;

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua53,
            layout: ChunkLayout::PucLua(PucLuaChunkLayout {
                format: LUA53_FORMAT,
                endianness,
                integer_size,
                lua_integer_size: Some(lua_integer_size),
                size_t_size,
                instruction_size,
                number_size,
                integral_number: false,
            }),
            extra: DialectHeaderExtra::Lua53(Lua53HeaderExtra),
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
            |reader| self.parse_optional_string(reader, layout),
            |reader, field| read_sized_u32(reader, layout, field),
        )?;
        let source = inherit_source(header_source, parent_source);
        let raw_is_vararg = prelude.raw_flag;

        let (raw_instruction_words, instructions) =
            parse_puc_lua_instruction_section::<Lua53InstructionCodec, _, _>(
                reader,
                layout,
                |reader, field| self.read_count(reader, layout, field),
                |_, _| Ok(()),
                "instruction_size",
            )?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader, layout)?;
        let child_count = self.read_count(reader, layout, "child proto count")?;
        let children = parse_child_protos(child_count, || {
            self.parse_proto(reader, layout, source.as_ref())
        })?;
        let debug_info = self.parse_debug_info(reader, layout, raw_instruction_words)?;

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
            DialectProtoExtra::Lua53(Lua53ProtoExtra { raw_is_vararg }),
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
            |reader, field| self.read_count(reader, layout, field),
            |tag, offset, reader| {
                Ok(match tag {
                    LUA_TNIL => RawLiteralConst::Nil,
                    LUA_TBOOLEAN => RawLiteralConst::Boolean(reader.read_u8()? != 0),
                    LUA_TNUMFLT => RawLiteralConst::Number(
                        reader.read_f64_sized(layout.number_size, layout.endianness)?,
                    ),
                    LUA_TNUMINT => RawLiteralConst::Integer(read_layout_lua_integer(
                        reader,
                        layout,
                        "lua_Integer",
                        "lua53",
                    )?),
                    LUA_TSHRSTR | LUA_TLNGSTR => {
                        let value = require_present(
                            self.parse_string(reader, layout)?,
                            "string constant length",
                        )?;
                        RawLiteralConst::String(value)
                    }
                    _ => return Err(ParseError::InvalidConstantTag { offset, tag }),
                })
            },
        )?;

        Ok(RawConstPool {
            common: RawConstPoolCommon { literals },
            extra: DialectConstPoolExtra::Lua53(Lua53ConstPoolExtra),
        })
    }

    fn parse_upvalues(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<RawUpvalueInfo, ParseError> {
        let count = self.read_count(reader, layout, "upvalue count")?;
        let count_u8 = count_u8(count, "upvalue count")?;
        let descriptors = parse_upvalue_descriptors(reader, count)?;

        Ok(RawUpvalueInfo {
            common: RawUpvalueInfoCommon {
                count: count_u8,
                descriptors,
            },
            extra: DialectUpvalueExtra::Lua53(Lua53UpvalueExtra),
        })
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        raw_instruction_words: usize,
    ) -> Result<RawDebugInfo, ParseError> {
        let mut driver = Lua53ClassicDebugDriver {
            parser: self,
            layout,
        };
        let sections = parse_classic_debug_sections(
            reader,
            raw_instruction_words,
            self.options.mode.is_permissive(),
            &mut driver,
        )?;

        Ok(RawDebugInfo {
            common: sections.common,
            extra: DialectDebugExtra::Lua53(Lua53DebugExtra),
        })
    }

    fn parse_optional_string(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader, layout)
    }

    fn parse_string(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<Option<RawString>, ParseError> {
        let size = match reader.read_u8()? {
            0 => return Ok(None),
            LUA53_LONG_STRING_MARKER => {
                reader.read_u64_sized(layout.size_t_size, layout.endianness, "size_t")?
            }
            size => u64::from(size),
        };
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

    fn read_count(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        read_sized_u32(reader, layout, field)
    }
}

define_puc_lua_instruction_codec!(
    codec: Lua53InstructionCodec,
    opcode: Lua53Opcode,
    fields: crate::parser::dialect::puc_lua::DecodedInstructionFields,
    extra_word_policy: Lua53ExtraWordPolicy,
    operands: super::raw::Lua53Operands,
    decode_fields: decode_instruction_word,
    extra_arg_opcode: Lua53Opcode::ExtraArg,
    should_read_extra_word: |policy, fields| match policy {
        Lua53ExtraWordPolicy::None => false,
        Lua53ExtraWordPolicy::ExtraArg => true,
        Lua53ExtraWordPolicy::ExtraArgIfCZero => fields.c == 0,
    },
    wrap_opcode: RawInstrOpcode::Lua53,
    wrap_operands: RawInstrOperands::Lua53,
    wrap_extra: |pc, word_len, extra_arg| DialectInstrExtra::Lua53(Lua53InstrExtra {
        pc,
        word_len,
        extra_arg,
    }),
);
