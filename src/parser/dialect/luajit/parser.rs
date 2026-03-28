//! 这个文件实现 LuaJIT bytecode 的解析入口。
//!
//! 第一阶段严格对照 LuaJIT 2.1 的 `BCDUMP_VERSION=2` dump 协议：
//! - 显式 header 校验，不伪装成 PUC-Lua；
//! - 按 proto 流顺序读取，并用 `KGC_CHILD` 重建父子关系；
//! - 把 LuaJIT 自己的 KGC/KNUM/TDUP 常量空间落到 dialect extra，同时把
//!   后续 low/HIR 能直接消费的字面量同步进公共 `RawLiteralConst` 表。

use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    LuaJitChunkLayout, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawChunk,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawProto, RawProtoCommon, RawString, RawUpvalueDescriptor,
    RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    LuaJitConstPoolExtra, LuaJitDebugExtra, LuaJitHeaderExtra, LuaJitInstrExtra, LuaJitKgcEntry,
    LuaJitNumberConstEntry, LuaJitOpcode, LuaJitOperands, LuaJitProtoExtra, LuaJitTableConst,
    LuaJitTableLiteral, LuaJitTableRecord, LuaJitUpvalueExtra,
};

const LUAJIT_HEAD1: u8 = 0x1b;
const LUAJIT_HEAD2: u8 = b'L';
const LUAJIT_HEAD3: u8 = b'J';
const LUAJIT_DUMP_VERSION: u8 = 2;

const BCDUMP_F_BE: u32 = 0x01;
const BCDUMP_F_STRIP: u32 = 0x02;
const BCDUMP_F_FFI: u32 = 0x04;
const BCDUMP_F_FR2: u32 = 0x08;
const BCDUMP_F_KNOWN: u32 = 0x0f;

const BCDUMP_KGC_CHILD: u32 = 0;
const BCDUMP_KGC_TAB: u32 = 1;
const BCDUMP_KGC_I64: u32 = 2;
const BCDUMP_KGC_U64: u32 = 3;
const BCDUMP_KGC_COMPLEX: u32 = 4;
const BCDUMP_KGC_STR: u32 = 5;

const BCDUMP_KTAB_NIL: u32 = 0;
const BCDUMP_KTAB_FALSE: u32 = 1;
const BCDUMP_KTAB_TRUE: u32 = 2;
const BCDUMP_KTAB_INT: u32 = 3;
const BCDUMP_KTAB_NUM: u32 = 4;
const BCDUMP_KTAB_STR: u32 = 5;

const PROTO_VARARG: u8 = 0x02;
const PROTO_UV_LOCAL: u16 = 0x8000;
const PROTO_UV_IMMUTABLE: u16 = 0x4000;

pub(crate) struct LuaJitParser {
    options: ParseOptions,
}

impl LuaJitParser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let header = self.parse_header(&mut reader)?;
        let chunk_name = match &header.extra {
            DialectHeaderExtra::LuaJit(extra) => extra.chunk_name.clone(),
            _ => None,
        };
        let layout = *header
            .luajit_layout()
            .expect("luajit parser must produce a luajit chunk layout");

        let mut proto_stack = Vec::new();
        loop {
            let len = reader.read_uleb128_u32("luajit proto length")?;
            if len == 0 {
                break;
            }

            let proto_offset = reader.offset();
            let proto_bytes = reader.read_exact(len as usize)?;
            let proto = self.parse_proto(
                proto_bytes,
                proto_offset,
                layout,
                chunk_name.as_ref(),
                &mut proto_stack,
            )?;
            proto_stack.push(proto);
        }

        if reader.remaining() != 0 {
            return Err(ParseError::UnsupportedValue {
                field: "luajit trailing bytes",
                value: reader.remaining() as u64,
            });
        }

        if proto_stack.len() != 1 {
            return Err(ParseError::UnsupportedValue {
                field: "luajit root proto count",
                value: proto_stack.len() as u64,
            });
        }

        let main = proto_stack
            .pop()
            .expect("root proto count was checked above");

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
        if signature
            != [
                LUAJIT_HEAD1,
                LUAJIT_HEAD2,
                LUAJIT_HEAD3,
                LUAJIT_DUMP_VERSION,
            ]
        {
            if signature[..3] != [LUAJIT_HEAD1, LUAJIT_HEAD2, LUAJIT_HEAD3] {
                return Err(ParseError::InvalidSignature { offset: start });
            }
            return Err(ParseError::UnsupportedValue {
                field: "luajit dump version",
                value: u64::from(signature[3]),
            });
        }

        let flags = reader.read_uleb128_u32("luajit dump flags")?;
        if (flags & !BCDUMP_F_KNOWN) != 0 {
            return Err(ParseError::UnsupportedValue {
                field: "luajit dump flags",
                value: u64::from(flags),
            });
        }

        let chunk_name = if (flags & BCDUMP_F_STRIP) != 0 {
            None
        } else {
            let name_start = reader.offset();
            let name_len = reader.read_uleb128_u32("luajit chunk name length")? as usize;
            let bytes = reader.read_exact(name_len)?.to_vec();
            Some(self.decode_raw_string(name_start, reader.offset() - name_start, bytes)?)
        };

        Ok(ChunkHeader {
            dialect: Dialect::LuaJit,
            version: DialectVersion::LuaJit,
            layout: ChunkLayout::LuaJit(LuaJitChunkLayout {
                dump_version: LUAJIT_DUMP_VERSION,
                flags,
            }),
            extra: DialectHeaderExtra::LuaJit(LuaJitHeaderExtra {
                chunk_name,
                stripped: (flags & BCDUMP_F_STRIP) != 0,
                uses_ffi: (flags & BCDUMP_F_FFI) != 0,
                fr2: (flags & BCDUMP_F_FR2) != 0,
                big_endian: (flags & BCDUMP_F_BE) != 0,
            }),
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
        bytes: &[u8],
        base_offset: usize,
        layout: LuaJitChunkLayout,
        chunk_name: Option<&RawString>,
        proto_stack: &mut Vec<RawProto>,
    ) -> Result<RawProto, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let flags = reader.read_u8()?;
        let num_params = reader.read_u8()?;
        let max_stack_size = reader.read_u8()?;
        let upvalue_count = reader.read_u8()?;
        let kgc_count = reader.read_uleb128_u32("luajit proto kgc count")? as usize;
        let knum_count = reader.read_uleb128_u32("luajit proto knum count")? as usize;
        let instruction_count = reader.read_uleb128_u32("luajit proto instruction count")? as usize;

        let stripped = (layout.flags & BCDUMP_F_STRIP) != 0;
        let (debug_size, first_line, line_count) = if stripped {
            (0_u32, None, None)
        } else {
            let debug_size = reader.read_uleb128_u32("luajit proto debug size")?;
            if debug_size == 0 {
                (0, None, None)
            } else {
                (
                    debug_size,
                    Some(reader.read_uleb128_u32("luajit proto first line")?),
                    Some(reader.read_uleb128_u32("luajit proto line count")?),
                )
            }
        };

        let instructions = self.parse_instructions(
            &mut reader,
            base_offset,
            instruction_count,
            (layout.flags & BCDUMP_F_BE) != 0,
        )?;
        let (descriptors, immutable) = self.parse_upvalues(
            &mut reader,
            upvalue_count,
            (layout.flags & BCDUMP_F_BE) != 0,
        )?;
        let ParsedConstPool {
            const_pool,
            children,
        } = self.parse_constants(&mut reader, base_offset, kgc_count, knum_count, proto_stack)?;

        let debug_info = if debug_size == 0 {
            RawDebugInfo {
                common: RawDebugInfoCommon {
                    line_info: Vec::new(),
                    local_vars: Vec::new(),
                    upvalue_names: Vec::new(),
                },
                extra: DialectDebugExtra::LuaJit(LuaJitDebugExtra {
                    stripped,
                    debug_size: 0,
                }),
            }
        } else {
            let debug_offset = reader.offset();
            let debug_bytes = reader.read_exact(debug_size as usize)?;
            self.parse_debug_info(
                debug_bytes,
                base_offset + debug_offset,
                instruction_count,
                upvalue_count,
                first_line.unwrap_or_default(),
                line_count.unwrap_or_default(),
                debug_size,
                stripped,
            )?
        };

        if reader.remaining() != 0 {
            return Err(ParseError::UnsupportedValue {
                field: "luajit proto trailing bytes",
                value: reader.remaining() as u64,
            });
        }

        let defined_start = first_line.unwrap_or(0);
        let defined_end = first_line
            .zip(line_count)
            .map(|(first, count)| first.saturating_add(count.saturating_sub(1)))
            .unwrap_or(defined_start);

        Ok(RawProto {
            common: RawProtoCommon {
                source: chunk_name.cloned(),
                line_range: ProtoLineRange {
                    defined_start,
                    defined_end,
                },
                signature: ProtoSignature {
                    num_params,
                    is_vararg: (flags & PROTO_VARARG) != 0,
                    has_vararg_param_reg: false,
                    named_vararg_table: false,
                },
                frame: ProtoFrameInfo { max_stack_size },
                instructions,
                constants: const_pool,
                upvalues: RawUpvalueInfo {
                    common: RawUpvalueInfoCommon {
                        count: upvalue_count,
                        descriptors,
                    },
                    extra: DialectUpvalueExtra::LuaJit(LuaJitUpvalueExtra { immutable }),
                },
                debug_info,
                children,
            },
            extra: DialectProtoExtra::LuaJit(LuaJitProtoExtra {
                flags,
                first_line,
                line_count,
                debug_size,
            }),
            origin: Origin {
                span: Span {
                    offset: base_offset,
                    size: bytes.len(),
                },
                raw_word: None,
            },
        })
    }

    fn parse_instructions(
        &self,
        reader: &mut BinaryReader<'_>,
        base_offset: usize,
        instruction_count: usize,
        big_endian: bool,
    ) -> Result<Vec<RawInstr>, ParseError> {
        let mut instructions = Vec::with_capacity(instruction_count);

        for pc in 0..instruction_count {
            let offset = reader.offset();
            let bytes = reader.read_array::<4>()?;
            let word = if big_endian {
                u32::from_be_bytes(bytes)
            } else {
                u32::from_le_bytes(bytes)
            };
            let opcode_byte = (word & 0xff) as u8;
            let opcode = LuaJitOpcode::try_from(opcode_byte)
                .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;
            let a = ((word >> 8) & 0xff) as u8;
            let d = ((word >> 16) & 0xffff) as u16;
            let c = ((word >> 16) & 0xff) as u8;
            let b = ((word >> 24) & 0xff) as u8;
            let operands = match opcode.operand_kind() {
                super::raw::LuaJitOperandKind::A => LuaJitOperands::A { a },
                super::raw::LuaJitOperandKind::AD => LuaJitOperands::AD { a, d },
                super::raw::LuaJitOperandKind::ABC => LuaJitOperands::ABC { a, b, c },
            };
            instructions.push(RawInstr {
                opcode: RawInstrOpcode::LuaJit(opcode),
                operands: RawInstrOperands::LuaJit(operands),
                extra: DialectInstrExtra::LuaJit(LuaJitInstrExtra {
                    pc: pc as u32,
                    raw_word: word,
                }),
                origin: Origin {
                    span: Span {
                        offset: base_offset + offset,
                        size: 4,
                    },
                    raw_word: Some(u64::from(word)),
                },
            });
        }

        Ok(instructions)
    }

    fn parse_upvalues(
        &self,
        reader: &mut BinaryReader<'_>,
        upvalue_count: u8,
        big_endian: bool,
    ) -> Result<(Vec<RawUpvalueDescriptor>, Vec<bool>), ParseError> {
        let mut descriptors = Vec::with_capacity(upvalue_count as usize);
        let mut immutable = Vec::with_capacity(upvalue_count as usize);

        for _ in 0..upvalue_count {
            let bytes = reader.read_array::<2>()?;
            let encoded = if big_endian {
                u16::from_be_bytes(bytes)
            } else {
                u16::from_le_bytes(bytes)
            };
            let index = (encoded & !(PROTO_UV_LOCAL | PROTO_UV_IMMUTABLE)) as u32;
            let index = u8::try_from(index).map_err(|_| ParseError::UnsupportedValue {
                field: "luajit upvalue index",
                value: u64::from(index),
            })?;
            descriptors.push(RawUpvalueDescriptor {
                in_stack: (encoded & PROTO_UV_LOCAL) != 0,
                index,
            });
            immutable.push((encoded & PROTO_UV_IMMUTABLE) != 0);
        }

        Ok((descriptors, immutable))
    }

    fn parse_constants(
        &self,
        reader: &mut BinaryReader<'_>,
        base_offset: usize,
        kgc_count: usize,
        knum_count: usize,
        proto_stack: &mut Vec<RawProto>,
    ) -> Result<ParsedConstPool, ParseError> {
        let mut literals = Vec::new();
        let mut kgc_entries = Vec::with_capacity(kgc_count);
        let mut children = Vec::new();

        for _ in 0..kgc_count {
            let tag = reader.read_uleb128_u32("luajit kgc tag")?;
            if tag >= BCDUMP_KGC_STR {
                let string_len = (tag - BCDUMP_KGC_STR) as usize;
                let start = reader.offset();
                let bytes = reader.read_exact(string_len)?.to_vec();
                let raw = self.decode_raw_string(start + base_offset, string_len, bytes)?;
                let literal_index = literals.len();
                let value = RawLiteralConst::String(raw.clone());
                literals.push(value.clone());
                kgc_entries.push(LuaJitKgcEntry::Literal {
                    value,
                    literal_index,
                });
                continue;
            }

            match tag {
                BCDUMP_KGC_CHILD => {
                    let child = proto_stack.pop().ok_or(ParseError::UnsupportedValue {
                        field: "luajit child proto stack",
                        value: 0,
                    })?;
                    let child_proto_index = children.len();
                    children.push(child);
                    kgc_entries.push(LuaJitKgcEntry::Child { child_proto_index });
                }
                BCDUMP_KGC_TAB => {
                    let table = self.parse_table_const(reader, base_offset, &mut literals)?;
                    kgc_entries.push(LuaJitKgcEntry::Table(table));
                }
                BCDUMP_KGC_I64 => {
                    let value = self.read_i64_from_uleb(reader)?;
                    let literal_index = literals.len();
                    let literal = RawLiteralConst::Int64(value);
                    literals.push(literal.clone());
                    kgc_entries.push(LuaJitKgcEntry::Literal {
                        value: literal,
                        literal_index,
                    });
                }
                BCDUMP_KGC_U64 => {
                    let value = self.read_u64_from_uleb(reader)?;
                    let literal_index = literals.len();
                    let literal = RawLiteralConst::UInt64(value);
                    literals.push(literal.clone());
                    kgc_entries.push(LuaJitKgcEntry::Literal {
                        value: literal,
                        literal_index,
                    });
                }
                BCDUMP_KGC_COMPLEX => {
                    let real = self.read_f64_from_uleb(reader)?;
                    let imag = self.read_f64_from_uleb(reader)?;
                    let literal_index = literals.len();
                    let literal = RawLiteralConst::Complex { real, imag };
                    literals.push(literal.clone());
                    kgc_entries.push(LuaJitKgcEntry::Literal {
                        value: literal,
                        literal_index,
                    });
                }
                value => {
                    return Err(ParseError::UnsupportedValue {
                        field: "luajit kgc tag",
                        value: u64::from(value),
                    });
                }
            }
        }

        let mut knum_entries = Vec::with_capacity(knum_count);
        for _ in 0..knum_count {
            let (lo, is_number) = reader.read_uleb128_33("luajit knum lo")?;
            if is_number {
                let hi = reader.read_uleb128_u32("luajit knum hi")?;
                let value = f64::from_bits(u64::from(lo) | (u64::from(hi) << 32));
                let literal_index = literals.len();
                literals.push(RawLiteralConst::Number(value));
                knum_entries.push(LuaJitNumberConstEntry::Number {
                    value,
                    literal_index,
                });
            } else {
                let value = i64::from(i32::from_ne_bytes(lo.to_ne_bytes()));
                let literal_index = literals.len();
                literals.push(RawLiteralConst::Integer(value));
                knum_entries.push(LuaJitNumberConstEntry::Integer {
                    value,
                    literal_index,
                });
            }
        }

        // LuaJIT serializes KGC entries in storage order, but bytecode operands address them via
        // `proto_kgc(pt, ~(ptrdiff_t)idx)`, i.e. the logical index space seen by instructions is
        // the reverse of the serialized stream. Normalize once here so later stages can look up
        // `kgc_entries[d]` directly without carrying a dialect-specific reversal rule around.
        kgc_entries.reverse();

        Ok(ParsedConstPool {
            const_pool: RawConstPool {
                common: RawConstPoolCommon { literals },
                extra: DialectConstPoolExtra::LuaJit(LuaJitConstPoolExtra {
                    kgc_entries,
                    knum_entries,
                }),
            },
            children,
        })
    }

    fn parse_table_const(
        &self,
        reader: &mut BinaryReader<'_>,
        base_offset: usize,
        literals: &mut Vec<RawLiteralConst>,
    ) -> Result<LuaJitTableConst, ParseError> {
        let array_len = reader.read_uleb128_u32("luajit table array length")? as usize;
        let hash_len = reader.read_uleb128_u32("luajit table hash length")? as usize;
        let mut array = Vec::with_capacity(array_len);
        let mut hash = Vec::with_capacity(hash_len);

        for _ in 0..array_len {
            array.push(self.parse_table_literal(reader, base_offset, literals)?);
        }

        for _ in 0..hash_len {
            let key = self.parse_table_literal(reader, base_offset, literals)?;
            if matches!(key.value, RawLiteralConst::Nil) {
                return Err(ParseError::UnsupportedValue {
                    field: "luajit table key",
                    value: 0,
                });
            }
            let value = self.parse_table_literal(reader, base_offset, literals)?;
            hash.push(LuaJitTableRecord { key, value });
        }

        Ok(LuaJitTableConst { array, hash })
    }

    fn parse_table_literal(
        &self,
        reader: &mut BinaryReader<'_>,
        base_offset: usize,
        literals: &mut Vec<RawLiteralConst>,
    ) -> Result<LuaJitTableLiteral, ParseError> {
        let tag = reader.read_uleb128_u32("luajit table literal tag")?;
        let value = if tag >= BCDUMP_KTAB_STR {
            let string_len = (tag - BCDUMP_KTAB_STR) as usize;
            let start = reader.offset();
            let bytes = reader.read_exact(string_len)?.to_vec();
            let raw = self.decode_raw_string(start + base_offset, string_len, bytes)?;
            RawLiteralConst::String(raw)
        } else {
            match tag {
                BCDUMP_KTAB_NIL => RawLiteralConst::Nil,
                BCDUMP_KTAB_FALSE => RawLiteralConst::Boolean(false),
                BCDUMP_KTAB_TRUE => RawLiteralConst::Boolean(true),
                BCDUMP_KTAB_INT => {
                    let value = reader.read_uleb128_u32("luajit table int")?;
                    RawLiteralConst::Integer(i64::from(i32::from_ne_bytes(value.to_ne_bytes())))
                }
                BCDUMP_KTAB_NUM => RawLiteralConst::Number(self.read_f64_from_uleb(reader)?),
                value => {
                    return Err(ParseError::UnsupportedValue {
                        field: "luajit table literal tag",
                        value: u64::from(value),
                    });
                }
            }
        };

        let literal_index = literals.len();
        literals.push(value.clone());
        Ok(LuaJitTableLiteral {
            value,
            literal_index,
        })
    }

    fn parse_debug_info(
        &self,
        bytes: &[u8],
        base_offset: usize,
        instruction_count: usize,
        upvalue_count: u8,
        first_line: u32,
        line_count: u32,
        debug_size: u32,
        stripped: bool,
    ) -> Result<RawDebugInfo, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let line_width = if line_count < 256 {
            1
        } else if line_count < 65_536 {
            2
        } else {
            4
        };
        let mut line_info = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            let offset = match line_width {
                1 => u32::from(reader.read_u8()?),
                2 => u32::from(u16::from_le_bytes(reader.read_array::<2>()?)),
                4 => u32::from_le_bytes(reader.read_array::<4>()?),
                _ => unreachable!(),
            };
            line_info.push(first_line.saturating_add(offset));
        }

        let mut upvalue_names = Vec::with_capacity(upvalue_count as usize);
        for _ in 0..upvalue_count {
            let start = reader.offset();
            let mut bytes = Vec::new();
            loop {
                let byte = reader.read_u8()?;
                if byte == 0 {
                    break;
                }
                bytes.push(byte);
            }
            upvalue_names.push(self.decode_raw_string(
                base_offset + start,
                reader.offset() - start,
                bytes,
            )?);
        }

        if reader.remaining() != 0 {
            let _ = reader.read_exact(reader.remaining())?;
        }

        Ok(RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info,
                local_vars: Vec::new(),
                upvalue_names,
            },
            extra: DialectDebugExtra::LuaJit(LuaJitDebugExtra {
                stripped,
                debug_size,
            }),
        })
    }

    fn decode_raw_string(
        &self,
        offset: usize,
        size: usize,
        bytes: Vec<u8>,
    ) -> Result<RawString, ParseError> {
        let text = self.decode_string_text(offset, &bytes)?;
        Ok(RawString {
            bytes,
            text,
            origin: Origin {
                span: Span { offset, size },
                raw_word: None,
            },
        })
    }

    fn decode_string_text(
        &self,
        offset: usize,
        bytes: &[u8],
    ) -> Result<Option<DecodedText>, ParseError> {
        if bytes.is_empty() {
            return Ok(Some(DecodedText {
                encoding: self.options.string_encoding,
                value: String::new(),
            }));
        }

        Ok(Some(DecodedText {
            encoding: self.options.string_encoding,
            value: self.options.string_encoding.decode(
                offset,
                bytes,
                self.options.string_decode_mode,
            )?,
        }))
    }

    fn read_u64_from_uleb(&self, reader: &mut BinaryReader<'_>) -> Result<u64, ParseError> {
        let lo = reader.read_uleb128_u32("luajit u64 lo")?;
        let hi = reader.read_uleb128_u32("luajit u64 hi")?;
        Ok(u64::from(lo) | (u64::from(hi) << 32))
    }

    fn read_i64_from_uleb(&self, reader: &mut BinaryReader<'_>) -> Result<i64, ParseError> {
        Ok(i64::from_ne_bytes(
            self.read_u64_from_uleb(reader)?.to_ne_bytes(),
        ))
    }

    fn read_f64_from_uleb(&self, reader: &mut BinaryReader<'_>) -> Result<f64, ParseError> {
        Ok(f64::from_bits(self.read_u64_from_uleb(reader)?))
    }
}

struct ParsedConstPool {
    const_pool: RawConstPool,
    children: Vec<RawProto>,
}
