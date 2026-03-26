//! 这个文件实现 Lua 5.5 chunk 的实际解析逻辑。
//!
//! Lua 5.5 在 5.4 基础上又往前走了一步：header 增加了 `int/instruction` 的
//! 机器格式校验，dump 里的字符串改成了带重用表的格式，整数常量和若干计数继续
//! 使用 varint，且 `NEWTABLE/SETLIST` 改成了 `ivABC` 变体。这里按真实格式
//! 显式实现，避免把这些变化继续塞回 5.4 的读取假设里。

use crate::parser::dialect::puc_lua::{
    LUA_SIGNATURE, LUA55_LUAC_DATA, LUA55_LUAC_INST, LUA55_LUAC_INT, LUA55_LUAC_NUM, PucLuaLayout,
    RawInstructionWord, decode_instruction_word_55,
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
    Lua55AbsLineInfo, Lua55ConstPoolExtra, Lua55DebugExtra, Lua55HeaderExtra, Lua55InstrExtra,
    Lua55Opcode, Lua55Operands, Lua55ProtoExtra, Lua55UpvalueExtra,
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
        let layout = PucLuaLayout {
            endianness: header.endianness,
            integer_size: header.integer_size,
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
        if version != LUA55_VERSION {
            return Err(ParseError::UnsupportedVersion { found: version });
        }

        let format = reader.read_u8()?;
        if format != LUA55_FORMAT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedHeaderFormat { found: format });
        }

        let luac_data = reader.read_array::<6>()?;
        if luac_data != *LUA55_LUAC_DATA && !self.options.mode.is_permissive() {
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
        let int_sentinel_bytes = reader.read_exact(usize::from(integer_size))?;
        let endianness = self.detect_endianness(int_sentinel_bytes)?;
        let int_sentinel = decode_i64_bytes(int_sentinel_bytes, endianness, "int")?;
        if int_sentinel != LUA55_LUAC_INT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_int",
                value: int_sentinel as u64,
            });
        }

        let instruction_size = reader.read_u8()?;
        if instruction_size != 4 {
            return Err(ParseError::UnsupportedSize {
                field: "instruction_size",
                value: instruction_size,
            });
        }
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
        let luac_lua_int_bytes = reader.read_exact(usize::from(lua_integer_size))?;
        let luac_lua_int = decode_i64_bytes(luac_lua_int_bytes, endianness, "lua_Integer")?;
        if luac_lua_int != LUA55_LUAC_INT && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_lua_integer",
                value: luac_lua_int as u64,
            });
        }

        let number_size = reader.read_u8()?;
        let luac_num_bytes = reader.read_exact(usize::from(number_size))?;
        let luac_num = decode_f64_bytes(luac_num_bytes, endianness)?;
        if luac_num != LUA55_LUAC_NUM && !self.options.mode.is_permissive() {
            return Err(ParseError::UnsupportedValue {
                field: "luac_num",
                value: luac_num.to_bits(),
            });
        }

        Ok(ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua55,
            format,
            endianness,
            integer_size,
            lua_integer_size: Some(lua_integer_size),
            size_t_size: 0,
            instruction_size,
            number_size,
            integral_number: false,
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

    fn detect_endianness(&self, bytes: &[u8]) -> Result<Endianness, ParseError> {
        let little = decode_i64_bytes(bytes, Endianness::Little, "int")?;
        if little == LUA55_LUAC_INT {
            return Ok(Endianness::Little);
        }

        let big = decode_i64_bytes(bytes, Endianness::Big, "int")?;
        if big == LUA55_LUAC_INT {
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
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: &PucLuaLayout,
        parent_source: Option<&RawString>,
    ) -> Result<RawProto, ParseError> {
        let start = reader.offset();
        let defined_start = self.read_count(reader, "linedefined")?;
        let defined_end = self.read_count(reader, "lastlinedefined")?;
        let num_params = reader.read_u8()?;
        let raw_flag = reader.read_u8()?;
        let semantic_flag = raw_flag & !PF_FIXED;
        let max_stack_size = reader.read_u8()?;

        let instruction_words = self.parse_instruction_words(reader, layout)?;
        let instructions = self.decode_instructions(&instruction_words)?;
        let constants = self.parse_constants(reader, layout)?;
        let upvalues = self.parse_upvalues(reader)?;
        let children = self.parse_children(reader, layout, parent_source)?;
        let source = self
            .parse_optional_string(reader)?
            .or_else(|| parent_source.cloned());
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
                    is_vararg: semantic_flag & (PF_VAHID | PF_VATAB) != 0,
                    has_vararg_param_reg: semantic_flag & (PF_VAHID | PF_VATAB) != 0,
                    named_vararg_table: semantic_flag & PF_VATAB != 0,
                },
                frame: ProtoFrameInfo { max_stack_size },
                instructions,
                constants,
                upvalues,
                debug_info,
                children,
            },
            extra: DialectProtoExtra::Lua55(Lua55ProtoExtra { raw_flag }),
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
        self.skip_align(reader, usize::from(layout.instruction_size))?;
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
            let fields = decode_instruction_word_55(entry.word);
            let opcode = Lua55Opcode::try_from(fields.opcode)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;

            let mut word_len = 1_u8;
            let mut extra_arg = None;

            let operands = match opcode {
                Lua55Opcode::Return0 => Lua55Operands::None,
                Lua55Opcode::LoadKx => {
                    extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                    word_len = 2;
                    Lua55Operands::A { a: fields.a }
                }
                Lua55Opcode::LoadFalse
                | Lua55Opcode::LFalseSkip
                | Lua55Opcode::LoadTrue
                | Lua55Opcode::Return1
                | Lua55Opcode::Tbc
                | Lua55Opcode::VarArgPrep
                | Lua55Opcode::Close => Lua55Operands::A { a: fields.a },
                Lua55Opcode::Test => Lua55Operands::Ak {
                    a: fields.a,
                    k: fields.k,
                },
                Lua55Opcode::Move
                | Lua55Opcode::LoadNil
                | Lua55Opcode::GetUpVal
                | Lua55Opcode::SetUpVal
                | Lua55Opcode::Unm
                | Lua55Opcode::BNot
                | Lua55Opcode::Not
                | Lua55Opcode::Len
                | Lua55Opcode::Concat => Lua55Operands::AB {
                    a: fields.a,
                    b: fields.b,
                },
                Lua55Opcode::TForCall => Lua55Operands::AC {
                    a: fields.a,
                    c: fields.c,
                },
                Lua55Opcode::GetVarg => Lua55Operands::ABC {
                    a: fields.a,
                    b: fields.b,
                    c: fields.c,
                },
                Lua55Opcode::Eq
                | Lua55Opcode::Lt
                | Lua55Opcode::Le
                | Lua55Opcode::EqK
                | Lua55Opcode::TestSet => Lua55Operands::ABk {
                    a: fields.a,
                    b: fields.b,
                    k: fields.k,
                },
                Lua55Opcode::AddI | Lua55Opcode::ShlI | Lua55Opcode::ShrI => Lua55Operands::ABsCk {
                    a: fields.a,
                    b: fields.b,
                    sc: fields.sc,
                    k: fields.k,
                },
                Lua55Opcode::EqI
                | Lua55Opcode::LtI
                | Lua55Opcode::LeI
                | Lua55Opcode::GtI
                | Lua55Opcode::GeI
                | Lua55Opcode::MMBinI => Lua55Operands::AsBCk {
                    a: fields.a,
                    sb: fields.sb,
                    c: fields.c,
                    k: fields.k,
                },
                Lua55Opcode::LoadI | Lua55Opcode::LoadF => Lua55Operands::AsBx {
                    a: fields.a,
                    sbx: fields.sbx,
                },
                Lua55Opcode::LoadK
                | Lua55Opcode::Closure
                | Lua55Opcode::ForLoop
                | Lua55Opcode::ForPrep
                | Lua55Opcode::TForPrep
                | Lua55Opcode::TForLoop
                | Lua55Opcode::ErrNNil => Lua55Operands::ABx {
                    a: fields.a,
                    bx: fields.bx,
                },
                Lua55Opcode::Jmp => Lua55Operands::AsJ { sj: fields.sj },
                Lua55Opcode::GetTabUp
                | Lua55Opcode::GetTable
                | Lua55Opcode::GetI
                | Lua55Opcode::GetField
                | Lua55Opcode::SetTabUp
                | Lua55Opcode::SetTable
                | Lua55Opcode::SetI
                | Lua55Opcode::SetField
                | Lua55Opcode::Self_
                | Lua55Opcode::AddK
                | Lua55Opcode::SubK
                | Lua55Opcode::MulK
                | Lua55Opcode::ModK
                | Lua55Opcode::PowK
                | Lua55Opcode::DivK
                | Lua55Opcode::IdivK
                | Lua55Opcode::BandK
                | Lua55Opcode::BorK
                | Lua55Opcode::BxorK
                | Lua55Opcode::Add
                | Lua55Opcode::Sub
                | Lua55Opcode::Mul
                | Lua55Opcode::Mod
                | Lua55Opcode::Pow
                | Lua55Opcode::Div
                | Lua55Opcode::Idiv
                | Lua55Opcode::Band
                | Lua55Opcode::Bor
                | Lua55Opcode::Bxor
                | Lua55Opcode::Shl
                | Lua55Opcode::Shr
                | Lua55Opcode::MMBin
                | Lua55Opcode::MMBinK
                | Lua55Opcode::Call
                | Lua55Opcode::TailCall
                | Lua55Opcode::Return
                | Lua55Opcode::VarArg => Lua55Operands::ABCk {
                    a: fields.a,
                    b: fields.b,
                    c: fields.c,
                    k: fields.k,
                },
                Lua55Opcode::NewTable => {
                    extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                    word_len = 2;
                    Lua55Operands::AvBCk {
                        a: fields.a,
                        vb: fields.vb,
                        vc: fields.vc,
                        k: fields.k,
                    }
                }
                Lua55Opcode::SetList => {
                    if fields.k {
                        extra_arg = Some(self.extra_arg_word(words, pc, opcode)?);
                        word_len = 2;
                    }
                    Lua55Operands::AvBCk {
                        a: fields.a,
                        vb: fields.vb,
                        vc: fields.vc,
                        k: fields.k,
                    }
                }
                Lua55Opcode::ExtraArg => Lua55Operands::Ax { ax: fields.ax },
            };

            instructions.push(RawInstr {
                opcode: RawInstrOpcode::Lua55(opcode),
                operands: RawInstrOperands::Lua55(operands),
                extra: DialectInstrExtra::Lua55(Lua55InstrExtra {
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
        opcode: Lua55Opcode,
    ) -> Result<u32, ParseError> {
        let Some(helper) = words.get(pc + 1).copied() else {
            return Err(ParseError::MissingExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
            });
        };
        let helper_fields = decode_instruction_word_55(helper.word);
        let helper_opcode = Lua55Opcode::try_from(helper_fields.opcode).map_err(|found| {
            ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found,
            }
        })?;
        if helper_opcode != Lua55Opcode::ExtraArg {
            return Err(ParseError::InvalidExtraArgWord {
                pc,
                opcode: opcode_label(opcode),
                found: helper_fields.opcode,
            });
        }
        Ok(helper_fields.ax)
    }

    fn parse_constants(
        &mut self,
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
                LUA_VNUMINT => {
                    RawLiteralConst::Integer(self.read_lua_integer(reader, "lua_Integer")?)
                }
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
            extra: DialectConstPoolExtra::Lua55(Lua55ConstPoolExtra),
        })
    }

    fn parse_upvalues(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<RawUpvalueInfo, ParseError> {
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
            extra: DialectUpvalueExtra::Lua55(Lua55UpvalueExtra { kinds }),
        })
    }

    fn parse_children(
        &mut self,
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
        &mut self,
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
        if abs_line_count != 0 {
            self.skip_align(reader, usize::from(layout.integer_size))?;
        }
        for _ in 0..abs_line_count {
            abs_line_info.push(Lua55AbsLineInfo {
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

        Ok(RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info,
                local_vars,
                upvalue_names,
            },
            extra: DialectDebugExtra::Lua55(Lua55DebugExtra {
                line_deltas,
                abs_line_info,
            }),
        })
    }

    fn reconstruct_line_info(
        &self,
        defined_start: u32,
        line_deltas: &[i8],
        abs_line_info: &[Lua55AbsLineInfo],
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
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        self.parse_string(reader)
    }

    fn parse_string(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        let size = self.read_size(reader, "string size")?;
        if size == 0 {
            let index = self.read_size(reader, "string reuse index")?;
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
        let text = self.decode_string_text(offset, payload)?;
        let raw = RawString {
            bytes: payload.to_vec(),
            text,
            origin: Origin {
                span: Span {
                    offset,
                    size: byte_count,
                },
                raw_word: None,
            },
        };
        self.saved_strings.push(raw.clone());
        Ok(Some(raw))
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
        let value = reader.read_varint_u64_lua55(i32::MAX as u64, field)?;
        u32::try_from(value).map_err(|_| ParseError::IntegerOverflow { field, value })
    }

    fn read_size(
        &self,
        reader: &mut BinaryReader<'_>,
        field: &'static str,
    ) -> Result<u64, ParseError> {
        reader.read_varint_u64_lua55(u64::MAX, field)
    }

    fn read_lua_integer(
        &self,
        reader: &mut BinaryReader<'_>,
        field: &'static str,
    ) -> Result<i64, ParseError> {
        let encoded = self.read_size(reader, field)?;
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

fn opcode_label(opcode: Lua55Opcode) -> &'static str {
    match opcode {
        Lua55Opcode::Move => "MOVE",
        Lua55Opcode::LoadI => "LOADI",
        Lua55Opcode::LoadF => "LOADF",
        Lua55Opcode::LoadK => "LOADK",
        Lua55Opcode::LoadKx => "LOADKX",
        Lua55Opcode::LoadFalse => "LOADFALSE",
        Lua55Opcode::LFalseSkip => "LFALSESKIP",
        Lua55Opcode::LoadTrue => "LOADTRUE",
        Lua55Opcode::LoadNil => "LOADNIL",
        Lua55Opcode::GetUpVal => "GETUPVAL",
        Lua55Opcode::SetUpVal => "SETUPVAL",
        Lua55Opcode::GetTabUp => "GETTABUP",
        Lua55Opcode::GetTable => "GETTABLE",
        Lua55Opcode::GetI => "GETI",
        Lua55Opcode::GetField => "GETFIELD",
        Lua55Opcode::SetTabUp => "SETTABUP",
        Lua55Opcode::SetTable => "SETTABLE",
        Lua55Opcode::SetI => "SETI",
        Lua55Opcode::SetField => "SETFIELD",
        Lua55Opcode::NewTable => "NEWTABLE",
        Lua55Opcode::Self_ => "SELF",
        Lua55Opcode::AddI => "ADDI",
        Lua55Opcode::AddK => "ADDK",
        Lua55Opcode::SubK => "SUBK",
        Lua55Opcode::MulK => "MULK",
        Lua55Opcode::ModK => "MODK",
        Lua55Opcode::PowK => "POWK",
        Lua55Opcode::DivK => "DIVK",
        Lua55Opcode::IdivK => "IDIVK",
        Lua55Opcode::BandK => "BANDK",
        Lua55Opcode::BorK => "BORK",
        Lua55Opcode::BxorK => "BXORK",
        Lua55Opcode::ShlI => "SHLI",
        Lua55Opcode::ShrI => "SHRI",
        Lua55Opcode::Add => "ADD",
        Lua55Opcode::Sub => "SUB",
        Lua55Opcode::Mul => "MUL",
        Lua55Opcode::Mod => "MOD",
        Lua55Opcode::Pow => "POW",
        Lua55Opcode::Div => "DIV",
        Lua55Opcode::Idiv => "IDIV",
        Lua55Opcode::Band => "BAND",
        Lua55Opcode::Bor => "BOR",
        Lua55Opcode::Bxor => "BXOR",
        Lua55Opcode::Shl => "SHL",
        Lua55Opcode::Shr => "SHR",
        Lua55Opcode::MMBin => "MMBIN",
        Lua55Opcode::MMBinI => "MMBINI",
        Lua55Opcode::MMBinK => "MMBINK",
        Lua55Opcode::Unm => "UNM",
        Lua55Opcode::BNot => "BNOT",
        Lua55Opcode::Not => "NOT",
        Lua55Opcode::Len => "LEN",
        Lua55Opcode::Concat => "CONCAT",
        Lua55Opcode::Close => "CLOSE",
        Lua55Opcode::Tbc => "TBC",
        Lua55Opcode::Jmp => "JMP",
        Lua55Opcode::Eq => "EQ",
        Lua55Opcode::Lt => "LT",
        Lua55Opcode::Le => "LE",
        Lua55Opcode::EqK => "EQK",
        Lua55Opcode::EqI => "EQI",
        Lua55Opcode::LtI => "LTI",
        Lua55Opcode::LeI => "LEI",
        Lua55Opcode::GtI => "GTI",
        Lua55Opcode::GeI => "GEI",
        Lua55Opcode::Test => "TEST",
        Lua55Opcode::TestSet => "TESTSET",
        Lua55Opcode::Call => "CALL",
        Lua55Opcode::TailCall => "TAILCALL",
        Lua55Opcode::Return => "RETURN",
        Lua55Opcode::Return0 => "RETURN0",
        Lua55Opcode::Return1 => "RETURN1",
        Lua55Opcode::ForLoop => "FORLOOP",
        Lua55Opcode::ForPrep => "FORPREP",
        Lua55Opcode::TForPrep => "TFORPREP",
        Lua55Opcode::TForCall => "TFORCALL",
        Lua55Opcode::TForLoop => "TFORLOOP",
        Lua55Opcode::SetList => "SETLIST",
        Lua55Opcode::Closure => "CLOSURE",
        Lua55Opcode::VarArg => "VARARG",
        Lua55Opcode::GetVarg => "GETVARG",
        Lua55Opcode::ErrNNil => "ERRNNIL",
        Lua55Opcode::VarArgPrep => "VARARGPREP",
        Lua55Opcode::ExtraArg => "EXTRAARG",
    }
}
