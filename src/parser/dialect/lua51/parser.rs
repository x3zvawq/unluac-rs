//! 这个文件实现 Lua 5.1 chunk 的实际解析逻辑。
//!
//! 实现直接对照官方 `lundump.c` 的布局规则，目的是让 parser 在源头上
//! 保真，而不是在更后面的层次再去猜原始结构。

use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawChunk, RawConstPool,
    RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto, RawProtoCommon, RawString,
    RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua51ConstPoolExtra, Lua51DebugExtra, Lua51HeaderExtra, Lua51InstrExtra, Lua51Opcode,
    Lua51Operands, Lua51ProtoExtra, Lua51UpvalueExtra,
};

const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
const LUA51_VERSION: u8 = 0x51;
const LUA51_FORMAT: u8 = 0;
const LUA51_HEADER_SIZE: usize = 12;
const LUA_TNIL: u8 = 0;
const LUA_TBOOLEAN: u8 = 1;
const LUA_TNUMBER: u8 = 3;
const LUA_TSTRING: u8 = 4;
const MAXARG_SBX: i32 = ((1 << 18) - 1) >> 1;

pub(crate) struct Lua51Parser {
    options: ParseOptions,
}

#[derive(Debug, Clone, Copy)]
struct Lua51Layout {
    endianness: Endianness,
    integer_size: u8,
    size_t_size: u8,
    instruction_size: u8,
    number_size: u8,
    integral_number: bool,
}

#[derive(Debug, Clone, Copy)]
struct RawInstructionWord {
    offset: usize,
    word: u32,
}

impl Lua51Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let layout = Lua51Layout {
            endianness: header.endianness,
            integer_size: header.integer_size,
            size_t_size: header.size_t_size,
            instruction_size: header.instruction_size,
            number_size: header.number_size,
            integral_number: header.integral_number,
        };
        let main = self.parse_proto(&mut reader, &layout, None)?;

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
            version: DialectVersion::Lua51,
            format,
            endianness,
            integer_size,
            lua_integer_size: None,
            size_t_size,
            instruction_size,
            number_size,
            integral_number,
            extra: DialectHeaderExtra::Lua51(Lua51HeaderExtra),
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
        layout: &Lua51Layout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let start = reader.offset();
        let source = self
            .parse_optional_string(reader, layout)?
            .or_else(|| parent_source.cloned());
        let defined_start = self.read_u32(reader, layout, "linedefined")?;
        let defined_end = self.read_u32(reader, layout, "lastlinedefined")?;
        let upvalue_count = reader.read_u8()?;
        let num_params = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;

        let instruction_words = self.parse_instruction_words(reader, layout)?;
        let instructions = self.decode_instructions(&instruction_words)?;
        let constants = self.parse_constants(reader, layout)?;
        let children = self.parse_children(reader, layout, source.as_ref())?;
        let debug_info = self.parse_debug_info(reader, layout, instruction_words.len())?;

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
                },
                frame: ProtoFrameInfo { max_stack_size },
                instructions,
                constants,
                upvalues: RawUpvalueInfo {
                    common: RawUpvalueInfoCommon {
                        count: upvalue_count,
                        descriptors: Vec::new(),
                    },
                    extra: DialectUpvalueExtra::Lua51(Lua51UpvalueExtra),
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

    fn parse_instruction_words(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
    ) -> Result<Vec<RawInstructionWord>, ParseError> {
        let count = self.read_count(reader, layout, "instruction count")?;
        let mut words = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let offset = reader.offset();
            let word = reader.read_u64_sized(
                layout.instruction_size,
                layout.endianness,
                "instruction_size",
            )?;
            let word = u32::try_from(word).map_err(|_| ParseError::UnsupportedValue {
                field: "instruction word",
                value: word,
            })?;
            words.push(RawInstructionWord { offset, word });
        }

        Ok(words)
    }

    fn decode_instructions(
        &self,
        words: &[RawInstructionWord],
    ) -> Result<Vec<RawInstr>, ParseError> {
        let mut instructions = Vec::with_capacity(words.len());
        let mut pc = 0_usize;

        while pc < words.len() {
            let entry = words[pc];
            let opcode_byte = (entry.word & 0x3f) as u8;
            let opcode = Lua51Opcode::try_from(opcode_byte)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;
            let a = ((entry.word >> 6) & 0xff) as u8;
            let c = ((entry.word >> 14) & 0x1ff) as u16;
            let b = ((entry.word >> 23) & 0x1ff) as u16;
            let bx = (entry.word >> 14) & 0x3ffff;
            let sbx = bx as i32 - MAXARG_SBX;

            let mut word_len = 1_u8;
            let mut setlist_extra_arg = None;

            let operands = match opcode {
                Lua51Opcode::Move
                | Lua51Opcode::LoadNil
                | Lua51Opcode::GetUpVal
                | Lua51Opcode::SetUpVal
                | Lua51Opcode::Unm
                | Lua51Opcode::Not
                | Lua51Opcode::Len
                | Lua51Opcode::Return
                | Lua51Opcode::VarArg => Lua51Operands::AB { a, b },
                Lua51Opcode::LoadK
                | Lua51Opcode::GetGlobal
                | Lua51Opcode::SetGlobal
                | Lua51Opcode::Closure => Lua51Operands::ABx { a, bx },
                Lua51Opcode::LoadBool
                | Lua51Opcode::GetTable
                | Lua51Opcode::SetTable
                | Lua51Opcode::NewTable
                | Lua51Opcode::Self_
                | Lua51Opcode::Add
                | Lua51Opcode::Sub
                | Lua51Opcode::Mul
                | Lua51Opcode::Div
                | Lua51Opcode::Mod
                | Lua51Opcode::Pow
                | Lua51Opcode::Concat
                | Lua51Opcode::Eq
                | Lua51Opcode::Lt
                | Lua51Opcode::Le
                | Lua51Opcode::TestSet
                | Lua51Opcode::Call
                | Lua51Opcode::TailCall => Lua51Operands::ABC { a, b, c },
                Lua51Opcode::Jmp | Lua51Opcode::ForLoop | Lua51Opcode::ForPrep => {
                    Lua51Operands::AsBx { a, sbx }
                }
                Lua51Opcode::Test | Lua51Opcode::TForLoop => Lua51Operands::AC { a, c },
                Lua51Opcode::SetList => {
                    if c == 0 {
                        let Some(extra_word) = words.get(pc + 1).copied() else {
                            return Err(ParseError::MissingSetListWord { pc });
                        };
                        setlist_extra_arg = Some(extra_word.word);
                        word_len = 2;
                    }
                    Lua51Operands::ABC { a, b, c }
                }
                Lua51Opcode::Close => Lua51Operands::A { a },
            };

            let span_size = usize::from(word_len) * 4;
            instructions.push(RawInstr {
                opcode: RawInstrOpcode::Lua51(opcode),
                operands: RawInstrOperands::Lua51(operands),
                extra: DialectInstrExtra::Lua51(Lua51InstrExtra {
                    pc: pc as u32,
                    word_len,
                    setlist_extra_arg,
                }),
                origin: Origin {
                    span: Span {
                        offset: entry.offset,
                        size: span_size,
                    },
                    raw_word: Some(u64::from(entry.word)),
                },
            });

            pc += usize::from(word_len);
        }

        Ok(instructions)
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
    ) -> Result<RawConstPool, ParseError> {
        let constant_count = self.read_count(reader, layout, "constant count")?;
        let mut literals = Vec::with_capacity(constant_count as usize);

        for _ in 0..constant_count {
            let offset = reader.offset();
            let tag = reader.read_u8()?;
            let literal = match tag {
                LUA_TNIL => RawLiteralConst::Nil,
                LUA_TBOOLEAN => RawLiteralConst::Boolean(reader.read_u8()? != 0),
                LUA_TNUMBER => {
                    if layout.integral_number {
                        RawLiteralConst::Integer(self.read_i64(reader, layout, "lua_Number")?)
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
            extra: DialectConstPoolExtra::Lua51(Lua51ConstPoolExtra),
        })
    }

    fn parse_children(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
        parent_source: Option<&RawString>,
    ) -> Result<Vec<RawProto>, ParseError> {
        let child_count = self.read_count(reader, layout, "child proto count")?;
        let mut children = Vec::with_capacity(child_count as usize);

        for _ in 0..child_count {
            children.push(self.parse_proto(reader, layout, parent_source)?);
        }

        Ok(children)
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
        raw_instruction_words: usize,
    ) -> Result<RawDebugInfo, ParseError> {
        let line_count = self.read_count(reader, layout, "line info count")?;
        let mut line_info = Vec::with_capacity(line_count as usize);

        for _ in 0..line_count {
            line_info.push(self.read_u32(reader, layout, "line info")?);
        }

        let local_count = self.read_count(reader, layout, "local var count")?;
        let mut local_vars = Vec::with_capacity(local_count as usize);
        for _ in 0..local_count {
            let name = self
                .parse_string(reader, layout)?
                .ok_or(ParseError::UnsupportedValue {
                    field: "local var name length",
                    value: 0,
                })?;
            let start_pc = self.read_u32(reader, layout, "local var startpc")?;
            let end_pc = self.read_u32(reader, layout, "local var endpc")?;
            local_vars.push(RawLocalVar {
                name,
                start_pc,
                end_pc,
            });
        }

        let upvalue_name_count = self.read_count(reader, layout, "upvalue name count")?;
        let mut upvalue_names = Vec::with_capacity(upvalue_name_count as usize);
        for _ in 0..upvalue_name_count {
            if let Some(name) = self.parse_string(reader, layout)? {
                upvalue_names.push(name);
            }
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
            extra: DialectDebugExtra::Lua51(Lua51DebugExtra),
        })
    }

    fn parse_optional_string(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader, layout)
    }

    fn parse_string(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
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
        let text = self.decode_string_text(offset, &bytes)?;

        Ok(Some(RawString {
            bytes,
            text,
            origin: Origin {
                span: Span {
                    offset,
                    size: byte_count,
                },
                raw_word: None,
            },
        }))
    }

    fn decode_string_text(
        &self,
        offset: usize,
        bytes: &[u8],
    ) -> Result<Option<DecodedText>, ParseError> {
        let encoding = self.options.string_encoding;
        let value = encoding.decode(offset, bytes, self.options.string_decode_mode)?;

        Ok(Some(DecodedText { encoding, value }))
    }

    fn read_count(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        self.read_u32(reader, layout, field)
    }

    fn read_u32(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        let value = self.read_i64(reader, layout, field)?;
        if value < 0 {
            return Err(ParseError::NegativeValue { field, value });
        }

        u32::try_from(value).map_err(|_| ParseError::IntegerOverflow {
            field,
            value: value as u64,
        })
    }

    fn read_i64(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &Lua51Layout,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        reader.read_i64_sized(layout.integer_size, layout.endianness, field)
    }
}
