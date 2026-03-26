//! 这个文件实现 Lua 5.4 chunk 的实际解析逻辑。
//!
//! Lua 5.4 的 header/proto/debug 布局已经明显偏离 5.3：opcode 扩成 7 bit，
//! `int/size_t` 风格的计数都改成 varint，upvalue 描述符多了 `kind`，而行号信息
//! 也变成 `lineinfo + abslineinfo` 两段式。这里按真实格式显式实现，避免把这些
//! 差异硬塞回 5.3 的读取路径。

use crate::parser::dialect::puc_lua::{
    LUA_SIGNATURE, LUA54_LUAC_DATA, LUA54_LUAC_INT, LUA54_LUAC_NUM, PucLuaLayout,
    RawInstructionWord, decode_instruction_word_54,
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
    Lua54AbsLineInfo, Lua54ConstPoolExtra, Lua54DebugExtra, Lua54HeaderExtra, Lua54InstrExtra,
    Lua54Opcode, Lua54Operands, Lua54ProtoExtra, Lua54UpvalueExtra,
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

impl Lua54Parser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let layout = PucLuaLayout {
            endianness: header.endianness,
            integer_size: 0,
            lua_integer_size: header.lua_integer_size,
            size_t_size: 0,
            instruction_size: header.instruction_size,
            number_size: header.number_size,
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
        if version != LUA54_VERSION {
            return Err(ParseError::UnsupportedVersion { found: version });
        }

        let format = reader.read_u8()?;
        if format != LUA54_FORMAT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedHeaderFormat { found: format });
        }

        let luac_data = reader.read_array::<6>()?;
        if luac_data != *LUA54_LUAC_DATA && !self.options.mode.is_permissive() {
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
        if luac_int != LUA54_LUAC_INT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_int",
                value: luac_int as u64,
            });
        }

        let luac_num_bytes = reader.read_exact(usize::from(number_size))?;
        let luac_num = decode_f64_bytes(luac_num_bytes, endianness)?;
        if luac_num != LUA54_LUAC_NUM && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_num",
                value: luac_num.to_bits(),
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua54,
            format,
            endianness,
            integer_size: 0,
            lua_integer_size: Some(lua_integer_size),
            size_t_size: 0,
            instruction_size,
            number_size,
            integral_number: false,
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

    fn detect_endianness(&self, bytes: &[u8]) -> Result<Endianness, ParseError> {
        let little = decode_i64_bytes(bytes, Endianness::Little, "lua_Integer")?;
        if little == LUA54_LUAC_INT {
            return Ok(Endianness::Little);
        }

        let big = decode_i64_bytes(bytes, Endianness::Big, "lua_Integer")?;
        if big == LUA54_LUAC_INT {
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
            .parse_optional_string(reader)?
            .or_else(|| parent_source.cloned());
        let defined_start = self.read_count(reader, "linedefined")?;
        let defined_end = self.read_count(reader, "lastlinedefined")?;
        let num_params = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;

        let instruction_words = self.parse_instruction_words(reader, layout)?;
        let instructions = self.decode_instructions(&instruction_words)?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader)?;
        let children = self.parse_children(reader, layout, source.as_ref())?;
        let debug_info = self.parse_debug_info(
            reader,
            layout,
            instruction_words.len(),
            defined_start,
            upvalues.common.count,
        )?;

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
            extra: DialectProtoExtra::Lua54(Lua54ProtoExtra { raw_is_vararg }),
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
        let count = self.read_count(reader, "instruction count")?;
        let mut words = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let offset = reader.offset();
            let word =
                reader.read_u64_sized(layout.instruction_size, layout.endianness, "instruction")?;
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
            let fields = decode_instruction_word_54(entry.word);
            let opcode = Lua54Opcode::try_from(fields.opcode)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;

            let mut word_len = 1_u8;
            let mut extra_arg = None;

            let operands = match opcode {
                Lua54Opcode::Return0 => Lua54Operands::None,
                Lua54Opcode::LoadKx => {
                    extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                    word_len = 2;
                    Lua54Operands::A { a: fields.a }
                }
                Lua54Opcode::LoadFalse
                | Lua54Opcode::LFalseSkip
                | Lua54Opcode::LoadTrue
                | Lua54Opcode::Return1
                | Lua54Opcode::Tbc
                | Lua54Opcode::VarArgPrep => Lua54Operands::A { a: fields.a },
                Lua54Opcode::Test => Lua54Operands::Ak {
                    a: fields.a,
                    k: fields.k,
                },
                Lua54Opcode::Move
                | Lua54Opcode::LoadNil
                | Lua54Opcode::GetUpVal
                | Lua54Opcode::SetUpVal
                | Lua54Opcode::Unm
                | Lua54Opcode::BNot
                | Lua54Opcode::Not
                | Lua54Opcode::Len
                | Lua54Opcode::Concat => Lua54Operands::AB {
                    a: fields.a,
                    b: fields.b,
                },
                Lua54Opcode::TForCall | Lua54Opcode::VarArg => Lua54Operands::AC {
                    a: fields.a,
                    c: fields.c,
                },
                Lua54Opcode::Eq
                | Lua54Opcode::Lt
                | Lua54Opcode::Le
                | Lua54Opcode::EqK
                | Lua54Opcode::TestSet => Lua54Operands::ABk {
                    a: fields.a,
                    b: fields.b,
                    k: fields.k,
                },
                Lua54Opcode::AddI | Lua54Opcode::ShrI | Lua54Opcode::ShlI => Lua54Operands::ABsCk {
                    a: fields.a,
                    b: fields.b,
                    sc: fields.sc,
                    k: fields.k,
                },
                Lua54Opcode::EqI
                | Lua54Opcode::LtI
                | Lua54Opcode::LeI
                | Lua54Opcode::GtI
                | Lua54Opcode::GeI
                | Lua54Opcode::MMBinI => Lua54Operands::AsBCk {
                    a: fields.a,
                    sb: fields.sb,
                    c: fields.c,
                    k: fields.k,
                },
                Lua54Opcode::LoadI | Lua54Opcode::LoadF => Lua54Operands::AsBx {
                    a: fields.a,
                    sbx: fields.sbx,
                },
                Lua54Opcode::LoadK
                | Lua54Opcode::Closure
                | Lua54Opcode::ForLoop
                | Lua54Opcode::ForPrep
                | Lua54Opcode::TForPrep
                | Lua54Opcode::TForLoop => Lua54Operands::ABx {
                    a: fields.a,
                    bx: fields.bx,
                },
                Lua54Opcode::Jmp => Lua54Operands::AsJ { sj: fields.sj },
                Lua54Opcode::GetTabUp
                | Lua54Opcode::GetTable
                | Lua54Opcode::GetI
                | Lua54Opcode::GetField
                | Lua54Opcode::SetTabUp
                | Lua54Opcode::SetTable
                | Lua54Opcode::SetI
                | Lua54Opcode::SetField
                | Lua54Opcode::Self_
                | Lua54Opcode::AddK
                | Lua54Opcode::SubK
                | Lua54Opcode::MulK
                | Lua54Opcode::ModK
                | Lua54Opcode::PowK
                | Lua54Opcode::DivK
                | Lua54Opcode::IdivK
                | Lua54Opcode::BandK
                | Lua54Opcode::BorK
                | Lua54Opcode::BxorK
                | Lua54Opcode::Add
                | Lua54Opcode::Sub
                | Lua54Opcode::Mul
                | Lua54Opcode::Mod
                | Lua54Opcode::Pow
                | Lua54Opcode::Div
                | Lua54Opcode::Idiv
                | Lua54Opcode::Band
                | Lua54Opcode::Bor
                | Lua54Opcode::Bxor
                | Lua54Opcode::Shl
                | Lua54Opcode::Shr
                | Lua54Opcode::MMBin
                | Lua54Opcode::MMBinK
                | Lua54Opcode::Call
                | Lua54Opcode::TailCall
                | Lua54Opcode::Return => Lua54Operands::ABCk {
                    a: fields.a,
                    b: fields.b,
                    c: fields.c,
                    k: fields.k,
                },
                Lua54Opcode::NewTable => {
                    extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                    word_len = 2;
                    Lua54Operands::ABCk {
                        a: fields.a,
                        b: fields.b,
                        c: fields.c,
                        k: fields.k,
                    }
                }
                Lua54Opcode::SetList => {
                    if fields.k {
                        extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                        word_len = 2;
                    }
                    Lua54Operands::ABCk {
                        a: fields.a,
                        b: fields.b,
                        c: fields.c,
                        k: fields.k,
                    }
                }
                Lua54Opcode::ExtraArg => Lua54Operands::Ax { ax: fields.ax },
                Lua54Opcode::Close => Lua54Operands::A { a: fields.a },
            };

            instructions.push(RawInstr {
                opcode: RawInstrOpcode::Lua54(opcode),
                operands: RawInstrOperands::Lua54(operands),
                extra: DialectInstrExtra::Lua54(Lua54InstrExtra {
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
        opcode: Lua54Opcode,
    ) -> Result<u32, ParseError> {
        let Some(helper) = words.get(pc + 1).copied() else {
            return Err(ParseError::MissingExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
            });
        };
        let helper_fields = decode_instruction_word_54(helper.word);
        let helper_opcode = Lua54Opcode::try_from(helper_fields.opcode).map_err(|found| {
            ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found,
            }
        })?;
        if helper_opcode != Lua54Opcode::ExtraArg {
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
        let count = self.read_count(reader, "constant count")?;
        let mut literals = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let offset = reader.offset();
            let tag = reader.read_u8()?;
            let literal = match tag {
                LUA_VNIL => RawLiteralConst::Nil,
                LUA_VFALSE => RawLiteralConst::Boolean(false),
                LUA_VTRUE => RawLiteralConst::Boolean(true),
                LUA_VNUMFLT => RawLiteralConst::Number(
                    reader.read_f64_sized(layout.number_size, layout.endianness)?,
                ),
                LUA_VNUMINT => RawLiteralConst::Integer(self.read_lua_integer(
                    reader,
                    layout,
                    "lua_Integer",
                )?),
                LUA_VSHRSTR | LUA_VLNGSTR => {
                    let value = self
                        .parse_string(reader)?
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
            extra: DialectConstPoolExtra::Lua54(Lua54ConstPoolExtra),
        })
    }

    fn parse_upvalues(&self, reader: &mut BinaryReader<'_>) -> Result<RawUpvalueInfo, ParseError> {
        let count = self.read_count(reader, "upvalue count")?;
        let count_u8 = u8::try_from(count).map_err(|_| ParseError::IntegerOverflow {
            field: "upvalue count",
            value: u64::from(count),
        })?;
        let mut descriptors = Vec::with_capacity(count as usize);
        let mut kinds = Vec::with_capacity(count as usize);

        for _ in 0..count {
            descriptors.push(RawUpvalueDescriptor {
                in_stack: reader.read_u8()? != 0,
                index: reader.read_u8()?,
            });
            kinds.push(reader.read_u8()?);
        }

        Ok(RawUpvalueInfo {
            common: RawUpvalueInfoCommon {
                count: count_u8,
                descriptors,
            },
            extra: DialectUpvalueExtra::Lua54(Lua54UpvalueExtra { kinds }),
        })
    }

    fn parse_children(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        parent_source: Option<&RawString>,
    ) -> Result<Vec<RawProto>, ParseError> {
        let count = self.read_count(reader, "child proto count")?;
        let mut children = Vec::with_capacity(count as usize);
        for _ in 0..count {
            children.push(self.parse_proto(reader, layout, parent_source)?);
        }
        Ok(children)
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        raw_instruction_words: usize,
        defined_start: u32,
        upvalue_count: u8,
    ) -> Result<RawDebugInfo, ParseError> {
        let line_count = self.read_count(reader, "line info count")?;
        let mut line_deltas = Vec::with_capacity(line_count as usize);
        for _ in 0..line_count {
            line_deltas.push(reader.read_u8()? as i8);
        }

        let abs_line_count = self.read_count(reader, "abs line info count")?;
        let mut abs_line_info = Vec::with_capacity(abs_line_count as usize);
        for _ in 0..abs_line_count {
            abs_line_info.push(Lua54AbsLineInfo {
                pc: self.read_count(reader, "abs line info pc")?,
                line: self.read_count(reader, "abs line info line")?,
            });
        }

        let local_count = self.read_count(reader, "local var count")?;
        let mut local_vars = Vec::with_capacity(local_count as usize);
        for _ in 0..local_count {
            let name = self
                .parse_optional_string(reader)?
                .ok_or(ParseError::UnsupportedValue {
                    field: "local var name length",
                    value: 0,
                })?;
            let start_pc = self.read_count(reader, "local var startpc")?;
            let end_pc = self.read_count(reader, "local var endpc")?;
            local_vars.push(RawLocalVar {
                name,
                start_pc,
                end_pc,
            });
        }

        let upvalue_name_count = self.read_count(reader, "upvalue name count")?;
        if !self.options.mode.is_permissive()
            && upvalue_name_count != 0
            && upvalue_name_count != u32::from(upvalue_count)
        {
            return Err(ParseError::UnsupportedValue {
                field: "upvalue name count",
                value: u64::from(upvalue_name_count),
            });
        }

        let mut upvalue_names = Vec::with_capacity(upvalue_name_count as usize);
        for _ in 0..upvalue_name_count {
            if let Some(name) = self.parse_optional_string(reader)? {
                upvalue_names.push(name);
            }
        }

        if !self.options.mode.is_permissive()
            && !line_deltas.is_empty()
            && line_deltas.len() != raw_instruction_words
        {
            return Err(ParseError::UnsupportedValue {
                field: "line info length",
                value: line_deltas.len() as u64,
            });
        }

        let line_info = self.reconstruct_line_info(defined_start, &line_deltas, &abs_line_info)?;

        let _ = layout;
        Ok(RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info,
                local_vars,
                upvalue_names,
            },
            extra: DialectDebugExtra::Lua54(Lua54DebugExtra {
                line_deltas,
                abs_line_info,
            }),
        })
    }

    fn reconstruct_line_info(
        &self,
        defined_start: u32,
        line_deltas: &[i8],
        abs_line_info: &[Lua54AbsLineInfo],
    ) -> Result<Vec<u32>, ParseError> {
        if line_deltas.is_empty() {
            return Ok(Vec::new());
        }

        let mut lines = Vec::with_capacity(line_deltas.len());
        let mut current = i64::from(defined_start);
        let mut abs_index = 0_usize;

        for (pc, delta) in line_deltas.iter().copied().enumerate() {
            if let Some(abs) = abs_line_info.get(abs_index)
                && abs.pc as usize == pc
            {
                current = i64::from(abs.line);
                lines.push(abs.line);
                abs_index += 1;
                continue;
            }

            if delta == ABSLINEINFO {
                if self.options.mode.is_permissive() {
                    lines.push(current.max(0) as u32);
                    continue;
                }
                return Err(ParseError::UnsupportedValue {
                    field: "abs line info marker",
                    value: pc as u64,
                });
            }

            current += i64::from(delta);
            if current < 0 {
                return Err(ParseError::NegativeValue {
                    field: "line info",
                    value: current,
                });
            }
            lines.push(
                u32::try_from(current).map_err(|_| ParseError::IntegerOverflow {
                    field: "line info",
                    value: current as u64,
                })?,
            );
        }

        Ok(lines)
    }

    fn parse_optional_string(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader)
    }

    fn parse_string(&self, reader: &mut BinaryReader<'_>) -> Result<Option<RawString>, ParseError> {
        let size = self.read_size(reader, "string size")?;
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
        field: &'static str,
    ) -> Result<u32, ParseError> {
        let value = reader.read_varint_u64_lua54(i32::MAX as u64, field)?;
        u32::try_from(value).map_err(|_| ParseError::IntegerOverflow { field, value })
    }

    fn read_size(
        &self,
        reader: &mut BinaryReader<'_>,
        field: &'static str,
    ) -> Result<u64, ParseError> {
        reader.read_varint_u64_lua54(u64::MAX, field)
    }

    fn read_lua_integer(
        &self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        let Some(size) = layout.lua_integer_size else {
            unreachable!("lua54 parser should always carry lua_integer_size in layout");
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

fn opcode_label(opcode: Lua54Opcode) -> &'static str {
    match opcode {
        Lua54Opcode::Move => "MOVE",
        Lua54Opcode::LoadI => "LOADI",
        Lua54Opcode::LoadF => "LOADF",
        Lua54Opcode::LoadK => "LOADK",
        Lua54Opcode::LoadKx => "LOADKX",
        Lua54Opcode::LoadFalse => "LOADFALSE",
        Lua54Opcode::LFalseSkip => "LFALSESKIP",
        Lua54Opcode::LoadTrue => "LOADTRUE",
        Lua54Opcode::LoadNil => "LOADNIL",
        Lua54Opcode::GetUpVal => "GETUPVAL",
        Lua54Opcode::SetUpVal => "SETUPVAL",
        Lua54Opcode::GetTabUp => "GETTABUP",
        Lua54Opcode::GetTable => "GETTABLE",
        Lua54Opcode::GetI => "GETI",
        Lua54Opcode::GetField => "GETFIELD",
        Lua54Opcode::SetTabUp => "SETTABUP",
        Lua54Opcode::SetTable => "SETTABLE",
        Lua54Opcode::SetI => "SETI",
        Lua54Opcode::SetField => "SETFIELD",
        Lua54Opcode::NewTable => "NEWTABLE",
        Lua54Opcode::Self_ => "SELF",
        Lua54Opcode::AddI => "ADDI",
        Lua54Opcode::AddK => "ADDK",
        Lua54Opcode::SubK => "SUBK",
        Lua54Opcode::MulK => "MULK",
        Lua54Opcode::ModK => "MODK",
        Lua54Opcode::PowK => "POWK",
        Lua54Opcode::DivK => "DIVK",
        Lua54Opcode::IdivK => "IDIVK",
        Lua54Opcode::BandK => "BANDK",
        Lua54Opcode::BorK => "BORK",
        Lua54Opcode::BxorK => "BXORK",
        Lua54Opcode::ShrI => "SHRI",
        Lua54Opcode::ShlI => "SHLI",
        Lua54Opcode::Add => "ADD",
        Lua54Opcode::Sub => "SUB",
        Lua54Opcode::Mul => "MUL",
        Lua54Opcode::Mod => "MOD",
        Lua54Opcode::Pow => "POW",
        Lua54Opcode::Div => "DIV",
        Lua54Opcode::Idiv => "IDIV",
        Lua54Opcode::Band => "BAND",
        Lua54Opcode::Bor => "BOR",
        Lua54Opcode::Bxor => "BXOR",
        Lua54Opcode::Shl => "SHL",
        Lua54Opcode::Shr => "SHR",
        Lua54Opcode::MMBin => "MMBIN",
        Lua54Opcode::MMBinI => "MMBINI",
        Lua54Opcode::MMBinK => "MMBINK",
        Lua54Opcode::Unm => "UNM",
        Lua54Opcode::BNot => "BNOT",
        Lua54Opcode::Not => "NOT",
        Lua54Opcode::Len => "LEN",
        Lua54Opcode::Concat => "CONCAT",
        Lua54Opcode::Close => "CLOSE",
        Lua54Opcode::Tbc => "TBC",
        Lua54Opcode::Jmp => "JMP",
        Lua54Opcode::Eq => "EQ",
        Lua54Opcode::Lt => "LT",
        Lua54Opcode::Le => "LE",
        Lua54Opcode::EqK => "EQK",
        Lua54Opcode::EqI => "EQI",
        Lua54Opcode::LtI => "LTI",
        Lua54Opcode::LeI => "LEI",
        Lua54Opcode::GtI => "GTI",
        Lua54Opcode::GeI => "GEI",
        Lua54Opcode::Test => "TEST",
        Lua54Opcode::TestSet => "TESTSET",
        Lua54Opcode::Call => "CALL",
        Lua54Opcode::TailCall => "TAILCALL",
        Lua54Opcode::Return => "RETURN",
        Lua54Opcode::Return0 => "RETURN0",
        Lua54Opcode::Return1 => "RETURN1",
        Lua54Opcode::ForLoop => "FORLOOP",
        Lua54Opcode::ForPrep => "FORPREP",
        Lua54Opcode::TForPrep => "TFORPREP",
        Lua54Opcode::TForCall => "TFORCALL",
        Lua54Opcode::TForLoop => "TFORLOOP",
        Lua54Opcode::SetList => "SETLIST",
        Lua54Opcode::Closure => "CLOSURE",
        Lua54Opcode::VarArg => "VARARG",
        Lua54Opcode::VarArgPrep => "VARARGPREP",
        Lua54Opcode::ExtraArg => "EXTRAARG",
    }
}
