//! 这个文件实现 Lua 5.2 chunk 的实际解析逻辑。
//!
//! 它一方面复用 PUC-Lua 家族共享的位域拆解 helper，另一方面明确保留 5.2 自己的
//! header tail、upvalue 描述符、`LOADKX/EXTRAARG` 等布局差异，避免把版本细节
//! 模糊成“差不多一样”的弱抽象。

use crate::parser::dialect::puc_lua::{
    ClassicDebugDriver, LUA_SIGNATURE, LUA52_LUAC_TAIL, PucLuaLayout, PucLuaProtoSections,
    build_raw_string, count_u8, decode_instruction_word, define_puc_lua_instruction_codec,
    finish_puc_lua_proto, inherit_source, parse_child_protos, parse_classic_debug_sections,
    parse_puc_lua_instruction_section, parse_tagged_literal_pool, parse_upvalue_descriptors,
    read_proto_prelude, read_sized_i64, read_sized_u32, require_present,
    validate_instruction_word_size,
};
use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, ProtoSignature, PucLuaChunkLayout, RawChunk, RawConstPool,
    RawConstPoolCommon, RawDebugInfo, RawInstrOpcode, RawInstrOperands, RawLiteralConst,
    RawLocalVar, RawProto, RawString, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua52ConstPoolExtra, Lua52DebugExtra, Lua52ExtraWordPolicy, Lua52HeaderExtra, Lua52InstrExtra,
    Lua52Opcode, Lua52ProtoExtra, Lua52UpvalueExtra,
};

const LUA52_VERSION: u8 = 0x52;
const LUA52_FORMAT: u8 = 0;
const LUA52_HEADER_SIZE: usize = 18;
const LUA_TNIL: u8 = 0;
const LUA_TBOOLEAN: u8 = 1;
const LUA_TNUMBER: u8 = 3;
const LUA_TSTRING: u8 = 4;

pub(crate) struct Lua52Parser {
    options: ParseOptions,
}

struct Lua52ClassicDebugDriver<'a> {
    parser: &'a Lua52Parser,
    layout: &'a PucLuaLayout,
}

impl<'a, 'bytes> ClassicDebugDriver<'bytes> for Lua52ClassicDebugDriver<'a> {
    fn read_source(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parser.parse_optional_string(reader, self.layout)
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

impl Lua52Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let header_layout = header
            .puc_lua_layout()
            .expect("lua52 parser must produce a PUC-Lua header layout");
        let layout = PucLuaLayout {
            endianness: header_layout.endianness,
            integer_size: header_layout.integer_size,
            lua_integer_size: None,
            size_t_size: header_layout.size_t_size,
            instruction_size: header_layout.instruction_size,
            number_size: header_layout.number_size,
            integral_number: header_layout.integral_number,
        };
        let main = self.parse_proto(&mut reader, &layout)?;

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
        let start = reader.offset();
        let signature = reader.read_array::<4>()?;
        if signature != *LUA_SIGNATURE {
            return Err(ParseError::InvalidSignature { offset: start });
        }

        let version = reader.read_u8()?;
        if version != LUA52_VERSION {
            return Err(ParseError::UnsupportedVersion { found: version });
        }

        let format = reader.read_u8()?;
        if format != LUA52_FORMAT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedHeaderFormat { found: format });
        }

        let endianness = match reader.read_u8()? {
            0 => Endianness::Big,
            1 => Endianness::Little,
            value => {
                if !self.options.mode.is_permissive() {
                    return Err(ParseError::UnsupportedValue {
                        field: "endianness",
                        value: u64::from(value),
                    });
                }
                Endianness::Little
            }
        };
        let integer_size = reader.read_u8()?;
        let size_t_size = reader.read_u8()?;
        let instruction_size = reader.read_u8()?;
        let number_size = reader.read_u8()?;
        let integral_number = reader.read_u8()? != 0;
        let tail = reader.read_array::<6>()?;

        validate_instruction_word_size(instruction_size)?;
        if tail != *LUA52_LUAC_TAIL && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_tail",
                value: u64::from(u32::from_le_bytes([tail[0], tail[1], tail[2], tail[3]])),
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua52,
            layout: ChunkLayout::PucLua(PucLuaChunkLayout {
                format,
                endianness,
                integer_size,
                lua_integer_size: None,
                size_t_size,
                instruction_size,
                number_size,
                integral_number,
            }),
            extra: DialectHeaderExtra::Lua52(Lua52HeaderExtra),
            origin: Origin {
                span: Span {
                    offset: start,
                    size: LUA52_HEADER_SIZE,
                },
                raw_word: None,
            },
        })
    }

    fn parse_proto(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<RawProto, ParseError> {
        let (prelude, header_source) = read_proto_prelude(
            reader,
            |_| Ok(None),
            |reader, field| read_sized_u32(reader, layout, field),
        )?;
        let raw_is_vararg = prelude.raw_flag;

        let (raw_instruction_words, instructions) =
            parse_puc_lua_instruction_section::<Lua52InstructionCodec, _, _>(
                reader,
                layout,
                |reader, field| self.read_count(reader, layout, field),
                |_, _| Ok(()),
                "instruction_size",
            )?;
        let (constants, children) = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader, layout)?;
        let (source, debug_info) = self.parse_debug_info(reader, layout, raw_instruction_words)?;
        let source = inherit_source(source.or(header_source), None);

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
            DialectProtoExtra::Lua52(Lua52ProtoExtra { raw_is_vararg }),
            reader.offset(),
        ))
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<(RawConstPool, Vec<RawProto>), ParseError> {
        let literals = parse_tagged_literal_pool(
            reader,
            |reader, field| self.read_count(reader, layout, field),
            |tag, offset, reader| {
                Ok(match tag {
                    LUA_TNIL => RawLiteralConst::Nil,
                    LUA_TBOOLEAN => RawLiteralConst::Boolean(reader.read_u8()? != 0),
                    LUA_TNUMBER => {
                        if layout.integral_number {
                            RawLiteralConst::Integer(read_sized_i64(reader, layout, "lua_Number")?)
                        } else {
                            RawLiteralConst::Number(
                                reader.read_f64_sized(layout.number_size, layout.endianness)?,
                            )
                        }
                    }
                    LUA_TSTRING => {
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

        let child_count = self.read_count(reader, layout, "child proto count")?;
        let children = parse_child_protos(child_count, || self.parse_proto(reader, layout))?;

        Ok((
            RawConstPool {
                common: RawConstPoolCommon { literals },
                extra: DialectConstPoolExtra::Lua52(Lua52ConstPoolExtra),
            },
            children,
        ))
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
            extra: DialectUpvalueExtra::Lua52(Lua52UpvalueExtra),
        })
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        raw_instruction_words: usize,
    ) -> Result<(Option<RawString>, RawDebugInfo), ParseError> {
        let mut driver = Lua52ClassicDebugDriver {
            parser: self,
            layout,
        };
        let sections = parse_classic_debug_sections(
            reader,
            raw_instruction_words,
            self.options.mode.is_permissive(),
            &mut driver,
        )?;

        Ok((
            sections.source,
            RawDebugInfo {
                common: sections.common,
                extra: DialectDebugExtra::Lua52(Lua52DebugExtra),
            },
        ))
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
        let size = reader.read_u64_sized(layout.size_t_size, layout.endianness, "size_t")?;
        if size == 0 {
            return Ok(None);
        }

        let byte_count = usize::try_from(size).map_err(|_| ParseError::IntegerOverflow {
            field: "string size",
            value: size,
        })?;
        let offset = reader.offset();
        let payload = reader.read_exact(byte_count)?.to_vec();
        let bytes = match payload.split_last() {
            Some((&0, bytes_without_nul)) => bytes_without_nul.to_vec(),
            _ if self.options.mode.is_permissive() => payload,
            _ => return Err(ParseError::UnterminatedString { offset }),
        };
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
    codec: Lua52InstructionCodec,
    opcode: Lua52Opcode,
    fields: crate::parser::dialect::puc_lua::DecodedInstructionFields,
    extra_word_policy: Lua52ExtraWordPolicy,
    operands: super::raw::Lua52Operands,
    decode_fields: decode_instruction_word,
    extra_arg_opcode: Lua52Opcode::ExtraArg,
    should_read_extra_word: |policy, fields| match policy {
        Lua52ExtraWordPolicy::None => false,
        Lua52ExtraWordPolicy::ExtraArg => true,
        Lua52ExtraWordPolicy::ExtraArgIfCZero => fields.c == 0,
    },
    wrap_opcode: RawInstrOpcode::Lua52,
    wrap_operands: RawInstrOperands::Lua52,
    wrap_extra: |pc, word_len, extra_arg| DialectInstrExtra::Lua52(Lua52InstrExtra {
        pc,
        word_len,
        extra_arg,
    }),
);
