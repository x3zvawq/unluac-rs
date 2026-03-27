//! 这个文件实现 Lua 5.3 chunk 的实际解析逻辑。
//!
//! 它复用 PUC-Lua 家族共享的位域拆解 helper，同时显式保留 5.3 自己的
//! header 校验、字符串长度编码、整数/浮点常量标签，以及新增位运算 opcode 的
//! 解析规则，避免把版本差异揉成一个“差不多能用”的弱抽象。

use crate::parser::dialect::puc_lua::{
    LUA_SIGNATURE, LUA53_LUAC_DATA, LUA53_LUAC_INT, LUA53_LUAC_NUM, PucLuaLayout,
    RawInstructionWord, decode_instruction_word,
};
use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    Endianness, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, PucLuaChunkLayout,
    RawChunk, RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstr,
    RawInstrOpcode, RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto, RawProtoCommon,
    RawString, RawUpvalueDescriptor, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    Lua53ConstPoolExtra, Lua53DebugExtra, Lua53HeaderExtra, Lua53InstrExtra, Lua53Opcode,
    Lua53Operands, Lua53ProtoExtra, Lua53UpvalueExtra,
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

        if !self.options.mode.is_permissive()
            && main.common.upvalues.common.count != main_upvalue_count
        {
            return Err(ParseError::UnsupportedValue {
                field: "main proto upvalue count",
                value: u64::from(main_upvalue_count),
            });
        }

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
        if version != LUA53_VERSION {
            return Err(ParseError::UnsupportedVersion { found: version });
        }

        let format = reader.read_u8()?;
        if format != LUA53_FORMAT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedHeaderFormat { found: format });
        }

        let luac_data = reader.read_array::<6>()?;
        if luac_data != *LUA53_LUAC_DATA && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_data",
                value: u64::from(u32::from_le_bytes([
                    luac_data[0],
                    luac_data[1],
                    luac_data[2],
                    luac_data[3],
                ])),
            });
        }

        let integer_size = reader.read_u8()?;
        let size_t_size = reader.read_u8()?;
        let instruction_size = reader.read_u8()?;
        let lua_integer_size = reader.read_u8()?;
        let number_size = reader.read_u8()?;

        if instruction_size != 4 {
            return Err(ParseError::UnsupportedSize {
                field: "instruction_size",
                value: instruction_size,
            });
        }

        let luac_int_bytes = reader.read_exact(usize::from(lua_integer_size))?;
        let endianness = self.detect_endianness(luac_int_bytes)?;
        let luac_int = decode_i64_bytes(luac_int_bytes, endianness, "lua_Integer")?;
        if luac_int != LUA53_LUAC_INT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_int",
                value: luac_int as u64,
            });
        }

        let luac_num_bytes = reader.read_exact(usize::from(number_size))?;
        let luac_num = decode_f64_bytes(luac_num_bytes, endianness)?;
        if luac_num != LUA53_LUAC_NUM && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_num",
                value: luac_num.to_bits(),
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua53,
            layout: ChunkLayout::PucLua(PucLuaChunkLayout {
                format,
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

    fn detect_endianness(&self, bytes: &[u8]) -> Result<Endianness, ParseError> {
        let little = decode_i64_bytes(bytes, Endianness::Little, "lua_Integer")?;
        if little == LUA53_LUAC_INT {
            return Ok(Endianness::Little);
        }

        let big = decode_i64_bytes(bytes, Endianness::Big, "lua_Integer")?;
        if big == LUA53_LUAC_INT {
            return Ok(Endianness::Big);
        }

        if self.options.mode.is_permissive() {
            Ok(Endianness::Little)
        } else {
            Err(ParseError::UnsupportedValue {
                field: "luac_int",
                value: little as u64,
            })
        }
    }

    fn parse_proto(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let start = reader.offset();
        let source = self
            .parse_optional_string(reader, layout)?
            .or_else(|| parent_source.cloned());
        let defined_start = self.read_u32(reader, layout, "linedefined")?;
        let defined_end = self.read_u32(reader, layout, "lastlinedefined")?;
        let num_params = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;

        let instruction_words = self.parse_instruction_words(reader, layout)?;
        let instructions = self.decode_instructions(&instruction_words)?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader, layout)?;
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
                    has_vararg_param_reg: false,
                    named_vararg_table: false,
                },
                frame: ProtoFrameInfo { max_stack_size },
                instructions,
                constants,
                upvalues,
                debug_info,
                children,
            },
            extra: DialectProtoExtra::Lua53(Lua53ProtoExtra { raw_is_vararg }),
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
            let opcode = Lua53Opcode::try_from(fields.opcode)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;

            let mut word_len = 1_u8;
            let mut extra_arg = None;

            let operands = match opcode {
                Lua53Opcode::Move
                | Lua53Opcode::LoadNil
                | Lua53Opcode::GetUpVal
                | Lua53Opcode::SetUpVal
                | Lua53Opcode::Unm
                | Lua53Opcode::BNot
                | Lua53Opcode::Not
                | Lua53Opcode::Len
                | Lua53Opcode::Return
                | Lua53Opcode::VarArg => Lua53Operands::AB {
                    a: fields.a,
                    b: fields.b,
                },
                Lua53Opcode::LoadK | Lua53Opcode::Closure => Lua53Operands::ABx {
                    a: fields.a,
                    bx: fields.bx,
                },
                Lua53Opcode::LoadKx => {
                    let helper = self.extra_arg_word(words, pc, opcode)?;
                    extra_arg = Some(helper);
                    word_len = 2;
                    Lua53Operands::A { a: fields.a }
                }
                Lua53Opcode::LoadBool
                | Lua53Opcode::GetTabUp
                | Lua53Opcode::GetTable
                | Lua53Opcode::SetTabUp
                | Lua53Opcode::SetTable
                | Lua53Opcode::NewTable
                | Lua53Opcode::Self_
                | Lua53Opcode::Add
                | Lua53Opcode::Sub
                | Lua53Opcode::Mul
                | Lua53Opcode::Mod
                | Lua53Opcode::Pow
                | Lua53Opcode::Div
                | Lua53Opcode::Idiv
                | Lua53Opcode::Band
                | Lua53Opcode::Bor
                | Lua53Opcode::Bxor
                | Lua53Opcode::Shl
                | Lua53Opcode::Shr
                | Lua53Opcode::Concat
                | Lua53Opcode::Eq
                | Lua53Opcode::Lt
                | Lua53Opcode::Le
                | Lua53Opcode::TestSet
                | Lua53Opcode::Call
                | Lua53Opcode::TailCall
                | Lua53Opcode::TForCall => Lua53Operands::ABC {
                    a: fields.a,
                    b: fields.b,
                    c: fields.c,
                },
                Lua53Opcode::Jmp
                | Lua53Opcode::ForLoop
                | Lua53Opcode::ForPrep
                | Lua53Opcode::TForLoop => Lua53Operands::AsBx {
                    a: fields.a,
                    sbx: fields.sbx,
                },
                Lua53Opcode::Test => Lua53Operands::AC {
                    a: fields.a,
                    c: fields.c,
                },
                Lua53Opcode::SetList => {
                    if fields.c == 0 {
                        extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                        word_len = 2;
                    }
                    Lua53Operands::ABC {
                        a: fields.a,
                        b: fields.b,
                        c: fields.c,
                    }
                }
                Lua53Opcode::ExtraArg => Lua53Operands::Ax { ax: fields.ax },
            };

            instructions.push(RawInstr {
                opcode: RawInstrOpcode::Lua53(opcode),
                operands: RawInstrOperands::Lua53(operands),
                extra: DialectInstrExtra::Lua53(Lua53InstrExtra {
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
        opcode: Lua53Opcode,
    ) -> Result<u32, ParseError> {
        let Some(helper) = words.get(pc + 1).copied() else {
            return Err(ParseError::MissingExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
            });
        };
        let helper_fields = decode_instruction_word(helper.word);
        let helper_opcode = Lua53Opcode::try_from(helper_fields.opcode).map_err(|found| {
            ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found,
            }
        })?;
        if helper_opcode != Lua53Opcode::ExtraArg {
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
    ) -> Result<RawConstPool, ParseError> {
        let constant_count = self.read_count(reader, layout, "constant count")?;
        let mut literals = Vec::with_capacity(constant_count as usize);

        for _ in 0..constant_count {
            let offset = reader.offset();
            let tag = reader.read_u8()?;
            let literal = match tag {
                LUA_TNIL => RawLiteralConst::Nil,
                LUA_TBOOLEAN => RawLiteralConst::Boolean(reader.read_u8()? != 0),
                LUA_TNUMFLT => RawLiteralConst::Number(
                    reader.read_f64_sized(layout.number_size, layout.endianness)?,
                ),
                LUA_TNUMINT => RawLiteralConst::Integer(self.read_lua_integer(
                    reader,
                    layout,
                    "lua_Integer",
                )?),
                LUA_TSHRSTR | LUA_TLNGSTR => {
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
            extra: DialectConstPoolExtra::Lua53(Lua53ConstPoolExtra),
        })
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
            extra: DialectUpvalueExtra::Lua53(Lua53UpvalueExtra),
        })
    }

    fn parse_children(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
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
        layout: &PucLuaLayout,
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

    fn read_lua_integer(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        let Some(size) = layout.lua_integer_size else {
            unreachable!("lua53 parser should always carry lua_integer_size in layout");
        };
        reader.read_i64_sized(size, layout.endianness, field)
    }
}

fn decode_i64_bytes(
    bytes: &[u8],
    endianness: Endianness,
    field: &'static str,
) -> Result<i64, ParseError> {
    if !(1..=8).contains(&bytes.len()) {
        return Err(ParseError::UnsupportedSize {
            field,
            value: bytes.len() as u8,
        });
    }

    let mut buffer = [0_u8; 8];
    match endianness {
        Endianness::Little => buffer[..bytes.len()].copy_from_slice(bytes),
        Endianness::Big => buffer[8 - bytes.len()..].copy_from_slice(bytes),
    }

    if bytes.len() == 8 {
        return Ok(match endianness {
            Endianness::Little => i64::from_le_bytes(buffer),
            Endianness::Big => i64::from_be_bytes(buffer),
        });
    }

    let unsigned = match endianness {
        Endianness::Little => u64::from_le_bytes(buffer),
        Endianness::Big => u64::from_be_bytes(buffer),
    };
    let bits = (bytes.len() as u32) * 8;
    let shift = 64 - bits;
    Ok(((unsigned << shift) as i64) >> shift)
}

fn decode_f64_bytes(bytes: &[u8], endianness: Endianness) -> Result<f64, ParseError> {
    match bytes.len() {
        4 => {
            let mut buffer = [0_u8; 4];
            buffer.copy_from_slice(bytes);
            Ok(match endianness {
                Endianness::Little => f32::from_le_bytes(buffer),
                Endianness::Big => f32::from_be_bytes(buffer),
            } as f64)
        }
        8 => {
            let mut buffer = [0_u8; 8];
            buffer.copy_from_slice(bytes);
            Ok(match endianness {
                Endianness::Little => f64::from_le_bytes(buffer),
                Endianness::Big => f64::from_be_bytes(buffer),
            })
        }
        value => Err(ParseError::UnsupportedSize {
            field: "number_size",
            value: value as u8,
        }),
    }
}

fn opcode_label(opcode: Lua53Opcode) -> &'static str {
    match opcode {
        Lua53Opcode::Move => "MOVE",
        Lua53Opcode::LoadK => "LOADK",
        Lua53Opcode::LoadKx => "LOADKX",
        Lua53Opcode::LoadBool => "LOADBOOL",
        Lua53Opcode::LoadNil => "LOADNIL",
        Lua53Opcode::GetUpVal => "GETUPVAL",
        Lua53Opcode::GetTabUp => "GETTABUP",
        Lua53Opcode::GetTable => "GETTABLE",
        Lua53Opcode::SetTabUp => "SETTABUP",
        Lua53Opcode::SetUpVal => "SETUPVAL",
        Lua53Opcode::SetTable => "SETTABLE",
        Lua53Opcode::NewTable => "NEWTABLE",
        Lua53Opcode::Self_ => "SELF",
        Lua53Opcode::Add => "ADD",
        Lua53Opcode::Sub => "SUB",
        Lua53Opcode::Mul => "MUL",
        Lua53Opcode::Mod => "MOD",
        Lua53Opcode::Pow => "POW",
        Lua53Opcode::Div => "DIV",
        Lua53Opcode::Idiv => "IDIV",
        Lua53Opcode::Band => "BAND",
        Lua53Opcode::Bor => "BOR",
        Lua53Opcode::Bxor => "BXOR",
        Lua53Opcode::Shl => "SHL",
        Lua53Opcode::Shr => "SHR",
        Lua53Opcode::Unm => "UNM",
        Lua53Opcode::BNot => "BNOT",
        Lua53Opcode::Not => "NOT",
        Lua53Opcode::Len => "LEN",
        Lua53Opcode::Concat => "CONCAT",
        Lua53Opcode::Jmp => "JMP",
        Lua53Opcode::Eq => "EQ",
        Lua53Opcode::Lt => "LT",
        Lua53Opcode::Le => "LE",
        Lua53Opcode::Test => "TEST",
        Lua53Opcode::TestSet => "TESTSET",
        Lua53Opcode::Call => "CALL",
        Lua53Opcode::TailCall => "TAILCALL",
        Lua53Opcode::Return => "RETURN",
        Lua53Opcode::ForLoop => "FORLOOP",
        Lua53Opcode::ForPrep => "FORPREP",
        Lua53Opcode::TForCall => "TFORCALL",
        Lua53Opcode::TForLoop => "TFORLOOP",
        Lua53Opcode::SetList => "SETLIST",
        Lua53Opcode::Closure => "CLOSURE",
        Lua53Opcode::VarArg => "VARARG",
        Lua53Opcode::ExtraArg => "EXTRAARG",
    }
}
