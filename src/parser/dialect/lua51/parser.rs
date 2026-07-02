//! 这个文件实现 Lua 5.1 chunk 的实际解析逻辑。
//!
//! 实现直接对照官方 `lundump.c` 的布局规则，目的是让 parser 在源头上
//! 保真，而不是在更后面的层次再去猜原始结构。

use crate::decompile::DecompileDialect;
use crate::parser::error::ParseError;
use crate::parser::family::puc_lua::{
    DecodedInstructionFields, LUA_SIGNATURE, PucLuaInstructionCodec, RawInstructionWord,
    build_raw_string, decode_instruction_word, parse_puc_lua_instruction_section, read_sized_i64,
    read_sized_u32,
};
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, Endianness,
    Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, PucLuaChunkLayout, RawChunk,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto, RawProtoCommon, RawString,
    RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua51ExtraWordPolicy, Lua51InstrExtra, Lua51Opcode, Lua51Operands, Lua51ProtoExtra,
};

const LUA51_VERSION: u8 = 0x51;
const LUA51_FORMAT: u8 = 0;
const LUA51_HEADER_SIZE: usize = 12;
const LUA_TNIL: u8 = 0;
const LUA_TBOOLEAN: u8 = 1;
const LUA_TNUMBER: u8 = 3;
const LUA_TSTRING: u8 = 4;

pub(crate) struct Lua51Parser {
    options: ParseOptions,
}

impl Lua51Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let layout = header
            .puc_lua_layout()
            .expect("lua51 parser must produce a PUC-Lua header layout");
        let main = self.parse_proto(&mut reader, layout, None)?;

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
        if version != LUA51_VERSION {
            return Err(ParseError::UnsupportedVersion { found: version });
        }

        let format = reader.read_u8()?;
        if format != LUA51_FORMAT && !self.options.mode.is_permissive() {
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

        if instruction_size != 4 {
            return Err(ParseError::UnsupportedSize {
                field: "instruction_size",
                value: instruction_size,
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DecompileDialect::Lua51,
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
            extra: DialectHeaderExtra::Lua51,
            origin: Origin {
                span: Span {
                    offset: start,
                    size: LUA51_HEADER_SIZE,
                },
                raw_word: None,
            },
        })
    }

    fn parse_proto(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaChunkLayout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let start = reader.offset();
        let source = self
            .parse_string(reader, layout)?
            .or_else(|| parent_source.cloned());
        let defined_start = read_sized_u32(reader, layout, "linedefined")?;
        let defined_end = read_sized_u32(reader, layout, "lastlinedefined")?;
        let upvalue_count = reader.read_u8()?;
        let num_params = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;

        let (raw_instruction_words, instructions) =
            parse_puc_lua_instruction_section::<Lua51InstructionCodec, _, _>(
                reader,
                layout,
                |reader, field| read_sized_u32(reader, layout, field),
                |_, _| Ok(()),
                "instruction_size",
            )?;
        let constants = self.parse_constants(reader, layout)?;
        let children = self.parse_children(reader, layout, source.as_ref())?;
        let debug_info = self.parse_debug_info(reader, layout, raw_instruction_words)?;

        Ok(RawProto {
            common: RawProtoCommon {
                source,
                line_range: ProtoLineRange {
                    defined_start,
                    defined_end,
                },
                signature: ProtoSignature {
                    num_params,
                    is_vararg: raw_is_vararg != 0,
                    has_vararg_param_reg: false,
                    named_vararg_table: false,
                },
                frame: ProtoFrameInfo { max_stack_size },
                instructions,
                constants,
                upvalues: RawUpvalueInfo {
                    common: RawUpvalueInfoCommon {
                        count: upvalue_count,
                        descriptors: Vec::new(),
                    },
                    extra: DialectUpvalueExtra::Lua51,
                },
                debug_info,
                children,
            },
            extra: DialectProtoExtra::Lua51(Lua51ProtoExtra { raw_is_vararg }),
            origin: Origin {
                span: Span {
                    offset: start,
                    size: reader.offset() - start,
                },
                raw_word: None,
            },
        })
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaChunkLayout,
    ) -> Result<RawConstPool, ParseError> {
        let constant_count = read_sized_u32(reader, layout, "constant count")?;
        let mut literals = Vec::with_capacity(constant_count as usize);

        for _ in 0..constant_count {
            let offset = reader.offset();
            let tag = reader.read_u8()?;
            let literal = match tag {
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
                    let value =
                        self.parse_string(reader, layout)?
                            .ok_or(ParseError::UnsupportedValue {
                                field: "string constant length",
                                value: 0,
                            })?;
                    RawLiteralConst::String(value)
                }
                _ => return Err(ParseError::InvalidConstantTag { offset, tag }),
            };
            literals.push(literal);
        }

        Ok(RawConstPool {
            common: RawConstPoolCommon { literals },
            extra: DialectConstPoolExtra::Lua51,
        })
    }

    fn parse_children(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaChunkLayout,
        parent_source: Option<&RawString>,
    ) -> Result<Vec<RawProto>, ParseError> {
        let child_count = read_sized_u32(reader, layout, "child proto count")?;
        let mut children = Vec::with_capacity(child_count as usize);

        for _ in 0..child_count {
            children.push(self.parse_proto(reader, layout, parent_source)?);
        }

        Ok(children)
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaChunkLayout,
        raw_instruction_words: usize,
    ) -> Result<RawDebugInfo, ParseError> {
        let line_count = read_sized_u32(reader, layout, "line info count")?;
        let mut line_info = Vec::with_capacity(line_count as usize);

        for _ in 0..line_count {
            line_info.push(read_sized_u32(reader, layout, "line info")?);
        }

        let local_count = read_sized_u32(reader, layout, "local var count")?;
        let mut local_vars = Vec::with_capacity(local_count as usize);
        for _ in 0..local_count {
            let name = self
                .parse_string(reader, layout)?
                .ok_or(ParseError::UnsupportedValue {
                    field: "local var name length",
                    value: 0,
                })?;
            let start_pc = read_sized_u32(reader, layout, "local var startpc")?;
            let end_pc = read_sized_u32(reader, layout, "local var endpc")?;
            local_vars.push(RawLocalVar {
                name,
                start_pc,
                end_pc,
            });
        }

        let upvalue_name_count = read_sized_u32(reader, layout, "upvalue name count")?;
        let mut upvalue_names = Vec::with_capacity(upvalue_name_count as usize);
        for _ in 0..upvalue_name_count {
            upvalue_names.push(self.parse_string(reader, layout)?);
        }

        if !self.options.mode.is_permissive()
            && !line_info.is_empty()
            && line_info.len() != raw_instruction_words
        {
            return Err(ParseError::UnsupportedValue {
                field: "line info length",
                value: line_info.len() as u64,
            });
        }

        Ok(RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info,
                local_vars,
                upvalue_names,
            },
            extra: DialectDebugExtra::Lua51,
        })
    }

    fn parse_string(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaChunkLayout,
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
}

struct Lua51InstructionCodec;

impl PucLuaInstructionCodec for Lua51InstructionCodec {
    type Opcode = Lua51Opcode;
    type Fields = DecodedInstructionFields;
    type ExtraWordPolicy = Lua51ExtraWordPolicy;
    type Operands = Lua51Operands;

    fn decode_fields(word: u32) -> Self::Fields {
        decode_instruction_word(word)
    }

    fn opcode_byte(fields: Self::Fields) -> u8 {
        fields.opcode
    }

    fn decode_operands(opcode: Self::Opcode, fields: Self::Fields) -> Self::Operands {
        opcode.decode_operands(fields)
    }

    fn extra_word_policy(opcode: Self::Opcode) -> Self::ExtraWordPolicy {
        opcode.extra_word_policy()
    }

    fn should_read_extra_word(policy: Self::ExtraWordPolicy, fields: Self::Fields) -> bool {
        matches!(policy, Lua51ExtraWordPolicy::SetListWordIfCZero) && fields.c == 0
    }

    fn opcode_label(opcode: Self::Opcode) -> &'static str {
        opcode.label()
    }

    fn extra_arg_opcode() -> Self::Opcode {
        unreachable!("lua51 SETLIST helper word is raw data, not an EXTRAARG opcode")
    }

    fn extra_arg_ax(fields: Self::Fields) -> u32 {
        fields.ax
    }

    fn read_extra_word(
        words: &[RawInstructionWord],
        pc: usize,
        _opcode: Self::Opcode,
    ) -> Result<u32, ParseError> {
        let Some(extra_word) = words.get(pc + 1).copied() else {
            return Err(ParseError::MissingSetListWord { pc });
        };
        Ok(extra_word.word)
    }

    fn wrap_opcode(opcode: Self::Opcode) -> RawInstrOpcode {
        RawInstrOpcode::Lua51(opcode)
    }

    fn wrap_operands(operands: Self::Operands) -> RawInstrOperands {
        RawInstrOperands::Lua51(operands)
    }

    fn wrap_extra(pc: u32, word_len: u8, setlist_extra_arg: Option<u32>) -> DialectInstrExtra {
        DialectInstrExtra::Lua51(Lua51InstrExtra {
            pc,
            word_len,
            setlist_extra_arg,
        })
    }
}
