//! 这个文件实现 Lua 5.5 chunk 的实际解析逻辑。
//!
//! Lua 5.5 在 5.4 基础上又往前走了一步：header 增加了 `int/instruction` 的
//! 机器格式校验，dump 里的字符串改成了带重用表的格式，整数常量和若干计数继续
//! 使用 varint，且 `NEWTABLE/SETLIST` 改成了 `ivABC` 变体。这里按真实格式
//! 显式实现，避免把这些变化继续塞回 5.4 的读取假设里。

use crate::parser::dialect::puc_lua::{
    AbsDebugDriver, AbsLineInfoConfig, LUA55_LUAC_DATA, LUA55_LUAC_INST, LUA55_LUAC_INT,
    LUA55_LUAC_NUM, PucLuaLayout, PucLuaProtoSections, build_raw_string, count_u8,
    decode_instruction_word_55, define_puc_lua_instruction_codec, finish_puc_lua_proto,
    inherit_source, parse_abs_debug_sections, parse_child_protos, parse_luac_data_header_prelude,
    parse_puc_lua_instruction_section, parse_tagged_literal_pool, parse_upvalues_with_kinds,
    read_f64_sentinel, read_i64_sentinel, read_i64_sentinel_endianness, read_proto_prelude,
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
    Lua55AbsLineInfo, Lua55ConstPoolExtra, Lua55DebugExtra, Lua55ExtraWordPolicy, Lua55HeaderExtra,
    Lua55InstrExtra, Lua55Opcode, Lua55ProtoExtra, Lua55UpvalueExtra,
};

const LUA55_VERSION: u8 = 0x55;
const LUA55_FORMAT: u8 = 0;
const LUA_VNIL: u8 = 0;
const LUA_VFALSE: u8 = 1;
const LUA_VTRUE: u8 = 17;
const LUA_VNUMINT: u8 = 3;
const LUA_VNUMFLT: u8 = 19;
const LUA_VSHRSTR: u8 = 4;
const LUA_VLNGSTR: u8 = 20;
const ABSLINEINFO: i8 = -0x80;
const PF_VAHID: u8 = 1;
const PF_VATAB: u8 = 2;
const PF_FIXED: u8 = 4;

pub(crate) struct Lua55Parser {
    options: ParseOptions,
}

struct Lua55ParserState {
    options: ParseOptions,
    saved_strings: Vec<RawString>,
}

struct Lua55AbsDebugDriver<'a> {
    parser: &'a mut Lua55ParserState,
    layout: &'a PucLuaLayout,
    permissive: bool,
    upvalue_count: u8,
}

impl<'a, 'bytes> AbsDebugDriver<'bytes> for Lua55AbsDebugDriver<'a> {
    fn read_count(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        reader.read_varint_u32_lua55(field)
    }

    fn read_line_delta(&mut self, reader: &mut BinaryReader<'bytes>) -> Result<i8, ParseError> {
        Ok(reader.read_u8()? as i8)
    }

    fn prepare_abs_line_info(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
        abs_line_count: u32,
    ) -> Result<(), ParseError> {
        if abs_line_count != 0 {
            self.parser
                .skip_align(reader, usize::from(self.layout.integer_size))?;
        }
        Ok(())
    }

    fn read_abs_line_pair(
        &mut self,
        reader: &mut BinaryReader<'bytes>,
    ) -> Result<(u32, u32), ParseError> {
        Ok((
            reader.read_varint_u32_lua55("abs line info pc")?,
            reader.read_varint_u32_lua55("abs line info line")?,
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
            start_pc: reader.read_varint_u32_lua55("local var startpc")?,
            end_pc: reader.read_varint_u32_lua55("local var endpc")?,
        })
    }

    fn validate_upvalue_count(&mut self, count: u32) -> Result<(), ParseError> {
        validate_optional_count_match(
            self.permissive,
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

impl Lua55Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        Lua55ParserState {
            options: self.options,
            saved_strings: Vec::new(),
        }
        .parse(bytes)
    }
}

impl Lua55ParserState {
    fn parse(&mut self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let header_layout = header
            .puc_lua_layout()
            .expect("lua55 parser must produce a PUC-Lua header layout");
        let layout = PucLuaLayout {
            endianness: header_layout.endianness,
            integer_size: header_layout.integer_size,
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
            LUA55_VERSION,
            LUA55_FORMAT,
            LUA55_LUAC_DATA,
            self.options.mode.is_permissive(),
        )?;

        let integer_size = reader.read_u8()?;
        let endianness = read_i64_sentinel_endianness(
            reader,
            integer_size,
            LUA55_LUAC_INT,
            "int",
            "luac_int",
            self.options.mode.is_permissive(),
        )?;

        let instruction_size = reader.read_u8()?;
        validate_instruction_word_size(instruction_size)?;
        let instruction_sentinel =
            reader.read_u64_sized(instruction_size, endianness, "instruction")?;
        if instruction_sentinel != u64::from(LUA55_LUAC_INST) && !self.options.mode.is_permissive()
        {
            return Err(ParseError::UnsupportedValue {
                field: "luac_instruction",
                value: instruction_sentinel,
            });
        }

        let lua_integer_size = reader.read_u8()?;
        read_i64_sentinel(
            reader,
            lua_integer_size,
            endianness,
            LUA55_LUAC_INT,
            "lua_Integer",
            "luac_lua_integer",
            self.options.mode.is_permissive(),
        )?;

        let number_size = reader.read_u8()?;
        read_f64_sentinel(
            reader,
            number_size,
            endianness,
            LUA55_LUAC_NUM,
            "number_size",
            "luac_num",
            self.options.mode.is_permissive(),
        )?;

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua55,
            layout: ChunkLayout::PucLua(PucLuaChunkLayout {
                format: LUA55_FORMAT,
                endianness,
                integer_size,
                lua_integer_size: Some(lua_integer_size),
                size_t_size: 0,
                instruction_size,
                number_size,
                integral_number: false,
            }),
            extra: DialectHeaderExtra::Lua55(Lua55HeaderExtra),
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
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let (prelude, header_source) = read_proto_prelude(
            reader,
            |_| Ok(None),
            |reader, field| reader.read_varint_u32_lua55(field),
        )?;
        let raw_flag = prelude.raw_flag;
        let semantic_flag = raw_flag & !PF_FIXED;

        let (raw_instruction_words, instructions) =
            parse_puc_lua_instruction_section::<Lua55InstructionCodec, _, _>(
                reader,
                layout,
                |reader, field| reader.read_varint_u32_lua55(field),
                |reader, layout| self.skip_align(reader, usize::from(layout.instruction_size)),
                "instruction",
            )?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader)?;
        let child_count = reader.read_varint_u32_lua55("child proto count")?;
        let children = parse_child_protos(child_count, || {
            self.parse_proto(reader, layout, parent_source)
        })?;
        let source = inherit_source(
            self.parse_optional_string(reader)?.or(header_source),
            parent_source,
        );
        let debug_info = self.parse_debug_info(
            reader,
            layout,
            raw_instruction_words,
            prelude.line_range.defined_start,
            upvalues.common.count,
        )?;

        Ok(finish_puc_lua_proto(
            prelude,
            source,
            ProtoSignature {
                num_params: prelude.num_params,
                is_vararg: semantic_flag & (PF_VAHID | PF_VATAB) != 0,
                has_vararg_param_reg: semantic_flag & (PF_VAHID | PF_VATAB) != 0,
                named_vararg_table: semantic_flag & PF_VATAB != 0,
            },
            PucLuaProtoSections {
                instructions,
                constants,
                upvalues,
                debug_info,
                children,
            },
            DialectProtoExtra::Lua55(Lua55ProtoExtra { raw_flag }),
            reader.offset(),
        ))
    }

    fn parse_constants(
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<RawConstPool, ParseError> {
        let literals = parse_tagged_literal_pool(
            reader,
            |reader, field| reader.read_varint_u32_lua55(field),
            |tag, offset, reader| {
                Ok(match tag {
                    LUA_VNIL => RawLiteralConst::Nil,
                    LUA_VFALSE => RawLiteralConst::Boolean(false),
                    LUA_VTRUE => RawLiteralConst::Boolean(true),
                    LUA_VNUMFLT => RawLiteralConst::Number(
                        reader.read_f64_sized(layout.number_size, layout.endianness)?,
                    ),
                    LUA_VNUMINT => {
                        RawLiteralConst::Integer(self.read_lua_integer(reader, "lua_Integer")?)
                    }
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
            extra: DialectConstPoolExtra::Lua55(Lua55ConstPoolExtra),
        })
    }

    fn parse_upvalues(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<RawUpvalueInfo, ParseError> {
        let count = reader.read_varint_u32_lua55("upvalue count")?;
        let count_u8 = count_u8(count, "upvalue count")?;
        let (descriptors, kinds) = parse_upvalues_with_kinds(reader, count)?;

        Ok(RawUpvalueInfo {
            common: RawUpvalueInfoCommon {
                count: count_u8,
                descriptors,
            },
            extra: DialectUpvalueExtra::Lua55(Lua55UpvalueExtra { kinds }),
        })
    }

    fn parse_debug_info(
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        raw_instruction_words: usize,
        defined_start: u32,
        upvalue_count: u8,
    ) -> Result<RawDebugInfo, ParseError> {
        let permissive = self.options.mode.is_permissive();
        let mut driver = Lua55AbsDebugDriver {
            parser: self,
            layout,
            permissive,
            upvalue_count,
        };
        let sections = parse_abs_debug_sections(
            reader,
            AbsLineInfoConfig {
                raw_instruction_words,
                defined_start,
                abslineinfo_marker: ABSLINEINFO,
                permissive,
            },
            &mut driver,
        )?;
        let abs_line_info = sections
            .abs_line_pairs
            .into_iter()
            .map(|(pc, line)| Lua55AbsLineInfo { pc, line })
            .collect();

        Ok(RawDebugInfo {
            common: sections.common,
            extra: DialectDebugExtra::Lua55(Lua55DebugExtra {
                line_deltas: sections.line_deltas,
                abs_line_info,
            }),
        })
    }

    fn parse_optional_string(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader)
    }

    fn parse_string(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        let size = reader.read_varint_u64_lua55(u64::MAX, "string size")?;
        if size == 0 {
            let index = reader.read_varint_u64_lua55(u64::MAX, "string reuse index")?;
            if index == 0 {
                return Ok(None);
            }

            let saved_index =
                usize::try_from(index - 1).map_err(|_| ParseError::IntegerOverflow {
                    field: "string reuse index",
                    value: index,
                })?;
            let saved = self.saved_strings.get(saved_index).cloned().ok_or(
                ParseError::UnsupportedValue {
                    field: "string reuse index",
                    value: index,
                },
            )?;
            return Ok(Some(saved));
        }

        let payload_size = size.checked_sub(1).ok_or(ParseError::UnsupportedValue {
            field: "string size",
            value: size,
        })?;
        let byte_count = usize::try_from(size).map_err(|_| ParseError::IntegerOverflow {
            field: "string size",
            value: size,
        })?;
        let payload_len =
            usize::try_from(payload_size).map_err(|_| ParseError::IntegerOverflow {
                field: "string size",
                value: payload_size,
            })?;
        let offset = reader.offset();
        let bytes = reader.read_exact(byte_count)?;
        if bytes[payload_len] != 0 {
            return Err(ParseError::UnterminatedString {
                offset: offset + payload_len,
            });
        }
        let payload = &bytes[..payload_len];
        let raw = build_raw_string(self.options, offset, payload.to_vec(), byte_count)?;
        self.saved_strings.push(raw.clone());
        Ok(Some(raw))
    }

    fn read_lua_integer(
        &self,
        reader: &mut BinaryReader<'_>,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        let encoded = reader.read_varint_u64_lua55(u64::MAX, field)?;
        let magnitude = encoded >> 1;
        let magnitude_i64 = i64::try_from(magnitude).map_err(|_| ParseError::IntegerOverflow {
            field,
            value: encoded,
        })?;
        if (encoded & 1) != 0 {
            Ok(!magnitude_i64)
        } else {
            Ok(magnitude_i64)
        }
    }

    fn skip_align(&self, reader: &mut BinaryReader<'_>, align: usize) -> Result<(), ParseError> {
        if align <= 1 {
            return Ok(());
        }
        let misalignment = reader.offset() % align;
        if misalignment == 0 {
            return Ok(());
        }
        let padding = align - misalignment;
        let _ = reader.read_exact(padding)?;
        Ok(())
    }
}

define_puc_lua_instruction_codec!(
    codec: Lua55InstructionCodec,
    opcode: Lua55Opcode,
    fields: crate::parser::dialect::puc_lua::DecodedInstructionFields55,
    extra_word_policy: Lua55ExtraWordPolicy,
    operands: super::raw::Lua55Operands,
    decode_fields: decode_instruction_word_55,
    extra_arg_opcode: Lua55Opcode::ExtraArg,
    should_read_extra_word: |policy, fields| match policy {
        Lua55ExtraWordPolicy::None => false,
        Lua55ExtraWordPolicy::ExtraArg => true,
        Lua55ExtraWordPolicy::ExtraArgIfK => fields.k,
    },
    wrap_opcode: RawInstrOpcode::Lua55,
    wrap_operands: RawInstrOperands::Lua55,
    wrap_extra: |pc, word_len, extra_arg| DialectInstrExtra::Lua55(Lua55InstrExtra {
        pc,
        word_len,
        extra_arg,
    }),
);
