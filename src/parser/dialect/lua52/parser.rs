//! 这个文件实现 Lua 5.2 chunk 的实际解析逻辑。
//!
//! 它一方面复用 PUC-Lua 家族共享的位域拆解 helper，另一方面明确保留 5.2 自己的
//! header tail、upvalue 描述符、`LOADKX/EXTRAARG` 等布局差异，避免把版本细节
//! 模糊成“差不多一样”的弱抽象。

use crate::parser::dialect::puc_lua::{
    LUA_SIGNATURE, LUA52_LUAC_TAIL, PucLuaLayout, RawInstructionWord, decode_instruction_word,
};
use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawChunk, RawConstPool,
    RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto, RawProtoCommon, RawString,
    RawUpvalueDescriptor, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua52ConstPoolExtra, Lua52DebugExtra, Lua52HeaderExtra, Lua52InstrExtra, Lua52Opcode,
    Lua52Operands, Lua52ProtoExtra, Lua52UpvalueExtra,
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

impl Lua52Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let layout = PucLuaLayout {
            endianness: header.endianness,
            integer_size: header.integer_size,
            size_t_size: header.size_t_size,
            instruction_size: header.instruction_size,
            number_size: header.number_size,
            integral_number: header.integral_number,
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

        if instruction_size != 4 {
            return Err(ParseError::UnsupportedSize {
                field: "instruction_size",
                value: instruction_size,
            });
        }
        if tail != *LUA52_LUAC_TAIL && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_tail",
                value: u64::from(u32::from_le_bytes([tail[0], tail[1], tail[2], tail[3]])),
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua52,
            format,
            endianness,
            integer_size,
            size_t_size,
            instruction_size,
            number_size,
            integral_number,
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
        let start = reader.offset();
        let defined_start = self.read_u32(reader, layout, "linedefined")?;
        let defined_end = self.read_u32(reader, layout, "lastlinedefined")?;
        let num_params = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;

        let instruction_words = self.parse_instruction_words(reader, layout)?;
        let instructions = self.decode_instructions(&instruction_words)?;
        let (constants, children) = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader, layout)?;
        let (source, debug_info) =
            self.parse_debug_info(reader, layout, instruction_words.len())?;

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
                upvalues,
                debug_info,
                children,
            },
            extra: DialectProtoExtra::Lua52(Lua52ProtoExtra { raw_is_vararg }),
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
        layout: &PucLuaLayout,
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
            let fields = decode_instruction_word(entry.word);
            let opcode = Lua52Opcode::try_from(fields.opcode)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;

            let mut word_len = 1_u8;
            let mut extra_arg = None;

            let operands = match opcode {
                Lua52Opcode::Move
                | Lua52Opcode::LoadNil
                | Lua52Opcode::GetUpVal
                | Lua52Opcode::SetUpVal
                | Lua52Opcode::Unm
                | Lua52Opcode::Not
                | Lua52Opcode::Len
                | Lua52Opcode::Return
                | Lua52Opcode::VarArg => Lua52Operands::AB {
                    a: fields.a,
                    b: fields.b,
                },
                Lua52Opcode::LoadK | Lua52Opcode::Closure => Lua52Operands::ABx {
                    a: fields.a,
                    bx: fields.bx,
                },
                Lua52Opcode::LoadKx => {
                    let helper = self.extra_arg_word(words, pc, opcode)?;
                    extra_arg = Some(helper);
                    word_len = 2;
                    Lua52Operands::A { a: fields.a }
                }
                Lua52Opcode::LoadBool
                | Lua52Opcode::GetTabUp
                | Lua52Opcode::GetTable
                | Lua52Opcode::SetTabUp
                | Lua52Opcode::SetTable
                | Lua52Opcode::NewTable
                | Lua52Opcode::Self_
                | Lua52Opcode::Add
                | Lua52Opcode::Sub
                | Lua52Opcode::Mul
                | Lua52Opcode::Div
                | Lua52Opcode::Mod
                | Lua52Opcode::Pow
                | Lua52Opcode::Concat
                | Lua52Opcode::Eq
                | Lua52Opcode::Lt
                | Lua52Opcode::Le
                | Lua52Opcode::TestSet
                | Lua52Opcode::Call
                | Lua52Opcode::TailCall
                | Lua52Opcode::TForCall => Lua52Operands::ABC {
                    a: fields.a,
                    b: fields.b,
                    c: fields.c,
                },
                Lua52Opcode::Jmp
                | Lua52Opcode::ForLoop
                | Lua52Opcode::ForPrep
                | Lua52Opcode::TForLoop => Lua52Operands::AsBx {
                    a: fields.a,
                    sbx: fields.sbx,
                },
                Lua52Opcode::Test => Lua52Operands::AC {
                    a: fields.a,
                    c: fields.c,
                },
                Lua52Opcode::SetList => {
                    if fields.c == 0 {
                        extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                        word_len = 2;
                    }
                    Lua52Operands::ABC {
                        a: fields.a,
                        b: fields.b,
                        c: fields.c,
                    }
                }
                Lua52Opcode::ExtraArg => Lua52Operands::Ax { ax: fields.ax },
            };

            instructions.push(RawInstr {
                opcode: RawInstrOpcode::Lua52(opcode),
                operands: RawInstrOperands::Lua52(operands),
                extra: DialectInstrExtra::Lua52(Lua52InstrExtra {
                    pc: pc as u32,
                    word_len,
                    extra_arg,
                }),
                origin: Origin {
                    span: Span {
                        offset: entry.offset,
                        size: usize::from(word_len) * 4,
                    },
                    raw_word: Some(u64::from(entry.word)),
                },
            });

            pc += usize::from(word_len);
        }

        Ok(instructions)
    }

    fn extra_arg_word(
        &self,
        words: &[RawInstructionWord],
        pc: usize,
        opcode: Lua52Opcode,
    ) -> Result<u32, ParseError> {
        let Some(helper) = words.get(pc + 1).copied() else {
            return Err(ParseError::MissingExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
            });
        };
        let helper_fields = decode_instruction_word(helper.word);
        let helper_opcode = Lua52Opcode::try_from(helper_fields.opcode).map_err(|found| {
            ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found,
            }
        })?;
        if helper_opcode != Lua52Opcode::ExtraArg {
            return Err(ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found: helper_fields.opcode,
            });
        }
        Ok(helper_fields.ax)
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
    ) -> Result<(RawConstPool, Vec<RawProto>), ParseError> {
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

        let child_count = self.read_count(reader, layout, "child proto count")?;
        let mut children = Vec::with_capacity(child_count as usize);
        for _ in 0..child_count {
            children.push(self.parse_proto(reader, layout)?);
        }

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
        let count_u8 = u8::try_from(count).map_err(|_| ParseError::IntegerOverflow {
            field: "upvalue count",
            value: u64::from(count),
        })?;
        let mut descriptors = Vec::with_capacity(count as usize);

        for _ in 0..count {
            descriptors.push(RawUpvalueDescriptor {
                in_stack: reader.read_u8()? != 0,
                index: reader.read_u8()?,
            });
        }

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
        let source = self.parse_optional_string(reader, layout)?;

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

        Ok((
            source,
            RawDebugInfo {
                common: RawDebugInfoCommon {
                    line_info,
                    local_vars,
                    upvalue_names,
                },
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
        layout: &PucLuaLayout,
        field: &'static str,
    ) -> Result<u32, ParseError> {
        self.read_u32(reader, layout, field)
    }

    fn read_u32(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
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
        layout: &PucLuaLayout,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        reader.read_i64_sized(layout.integer_size, layout.endianness, field)
    }
}

fn opcode_label(opcode: Lua52Opcode) -> &'static str {
    match opcode {
        Lua52Opcode::Move => "MOVE",
        Lua52Opcode::LoadK => "LOADK",
        Lua52Opcode::LoadKx => "LOADKX",
        Lua52Opcode::LoadBool => "LOADBOOL",
        Lua52Opcode::LoadNil => "LOADNIL",
        Lua52Opcode::GetUpVal => "GETUPVAL",
        Lua52Opcode::GetTabUp => "GETTABUP",
        Lua52Opcode::GetTable => "GETTABLE",
        Lua52Opcode::SetTabUp => "SETTABUP",
        Lua52Opcode::SetUpVal => "SETUPVAL",
        Lua52Opcode::SetTable => "SETTABLE",
        Lua52Opcode::NewTable => "NEWTABLE",
        Lua52Opcode::Self_ => "SELF",
        Lua52Opcode::Add => "ADD",
        Lua52Opcode::Sub => "SUB",
        Lua52Opcode::Mul => "MUL",
        Lua52Opcode::Div => "DIV",
        Lua52Opcode::Mod => "MOD",
        Lua52Opcode::Pow => "POW",
        Lua52Opcode::Unm => "UNM",
        Lua52Opcode::Not => "NOT",
        Lua52Opcode::Len => "LEN",
        Lua52Opcode::Concat => "CONCAT",
        Lua52Opcode::Jmp => "JMP",
        Lua52Opcode::Eq => "EQ",
        Lua52Opcode::Lt => "LT",
        Lua52Opcode::Le => "LE",
        Lua52Opcode::Test => "TEST",
        Lua52Opcode::TestSet => "TESTSET",
        Lua52Opcode::Call => "CALL",
        Lua52Opcode::TailCall => "TAILCALL",
        Lua52Opcode::Return => "RETURN",
        Lua52Opcode::ForLoop => "FORLOOP",
        Lua52Opcode::ForPrep => "FORPREP",
        Lua52Opcode::TForCall => "TFORCALL",
        Lua52Opcode::TForLoop => "TFORLOOP",
        Lua52Opcode::SetList => "SETLIST",
        Lua52Opcode::Closure => "CLOSURE",
        Lua52Opcode::VarArg => "VARARG",
        Lua52Opcode::ExtraArg => "EXTRAARG",
    }
}
