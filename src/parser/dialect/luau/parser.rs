//! 这个文件实现 Luau bytecode 的实际解析逻辑。
//!
//! Luau 的 serialized bytecode 不是 PUC-Lua 的 `lundump` 变体：它使用独立的
//! 版本头、字符串表、平铺 proto 表和混合常量表。这里按 Luau loader 的真实格式
//! 直接解码，避免在公共层伪造 PUC-Lua 头或常量池形状。

use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{
    ChunkHeader, ChunkLayout, DecodedText, Dialect, DialectConstPoolExtra, DialectDebugExtra,
    DialectHeaderExtra, DialectInstrExtra, DialectProtoExtra, DialectUpvalueExtra, DialectVersion,
    LuauChunkLayout, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawChunk,
    RawConstPool, RawConstPoolCommon, RawDebugInfo, RawDebugInfoCommon, RawInstr, RawInstrOpcode,
    RawInstrOperands, RawLiteralConst, RawLocalVar, RawProto, RawProtoCommon, RawString,
    RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::reader::BinaryReader;

use super::raw::{
    LuauConstEntry, LuauConstPoolExtra, LuauDebugExtra, LuauHeaderExtra, LuauInstrExtra,
    LuauOpcode, LuauProtoExtra, LuauTableConstEntry, LuauUpvalueExtra,
};

const LUAU_ERROR_BLOB_VERSION: u8 = 0;

pub(crate) struct LuauParser {
    options: ParseOptions,
}

struct LuauParserState {
    options: ParseOptions,
    strings: Vec<RawString>,
}

struct FlatProto {
    proto: RawProto,
    child_indices: Vec<usize>,
}

enum FlatProtoSlot {
    Pending(Box<FlatProto>),
    Building,
    Consumed,
}

struct LuauSymbolDebugInfo {
    local_vars: Vec<RawLocalVar>,
    local_regs: Vec<u8>,
    upvalue_names: Vec<RawString>,
}

struct DecodedInstrs {
    instrs: Vec<RawInstr>,
    word_pc_by_raw: Vec<u32>,
    raw_by_word_pc: Vec<Option<u32>>,
}

impl LuauParser {
    pub(crate) const fn new(options: ParseOptions) -> Self {
        Self { options }
    }

    pub(crate) fn parse(&self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        LuauParserState {
            options: self.options,
            strings: Vec::new(),
        }
        .parse(bytes)
    }
}

impl LuauParserState {
    fn parse(&mut self, bytes: &[u8]) -> Result<RawChunk, ParseError> {
        let mut reader = BinaryReader::new(bytes);
        let mut header = self.parse_header(&mut reader)?;

        self.strings = self.parse_string_table(&mut reader)?;
        let userdata_type_names = self.parse_userdata_type_mapping(
            &mut reader,
            header
                .luau_layout()
                .and_then(|layout| layout.type_version)
                .unwrap_or_default(),
        )?;
        header.extra = DialectHeaderExtra::Luau(LuauHeaderExtra {
            userdata_type_names,
        });

        let layout = *header
            .luau_layout()
            .expect("luau parser must produce a luau chunk layout");
        let mut flat_protos = self
            .parse_proto_table(&mut reader, layout)?
            .into_iter()
            .map(|proto| FlatProtoSlot::Pending(Box::new(proto)))
            .collect::<Vec<_>>();
        let main_index = usize::try_from(reader.read_varint_u32_luau("luau main proto id")?)
            .map_err(|_| ParseError::IntegerOverflow {
                field: "luau main proto id",
                value: u64::MAX,
            })?;
        if main_index >= flat_protos.len() {
            return Err(ParseError::UnsupportedValue {
                field: "luau main proto id",
                value: main_index as u64,
            });
        }

        let main = build_proto_tree(main_index, &mut flat_protos)?;

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
        let bytecode_version = reader.read_u8()?;
        if bytecode_version == LUAU_ERROR_BLOB_VERSION {
            return Err(ParseError::UnsupportedValue {
                field: "luau error blob",
                value: 0,
            });
        }

        let type_version = if bytecode_version >= 4 {
            Some(reader.read_u8()?)
        } else {
            None
        };

        Ok(ChunkHeader {
            dialect: Dialect::Luau,
            version: DialectVersion::Luau,
            layout: ChunkLayout::Luau(LuauChunkLayout {
                bytecode_version,
                type_version,
            }),
            extra: DialectHeaderExtra::Luau(LuauHeaderExtra::default()),
            origin: Origin {
                span: Span {
                    offset: start,
                    size: reader.offset() - start,
                },
                raw_word: None,
            },
        })
    }

    fn parse_string_table(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Vec<RawString>, ParseError> {
        let string_count = usize::try_from(reader.read_varint_u32_luau("luau string count")?)
            .map_err(|_| ParseError::IntegerOverflow {
                field: "luau string count",
                value: u64::MAX,
            })?;
        let mut strings = Vec::with_capacity(string_count);

        for _ in 0..string_count {
            let offset = reader.offset();
            let length = usize::try_from(reader.read_varint_u32_luau("luau string length")?)
                .map_err(|_| ParseError::IntegerOverflow {
                    field: "luau string length",
                    value: u64::MAX,
                })?;
            let bytes = reader.read_exact(length)?.to_vec();
            let text = self.decode_string_text(offset, &bytes)?;
            strings.push(RawString {
                bytes,
                text,
                origin: Origin {
                    span: Span {
                        offset,
                        size: reader.offset() - offset,
                    },
                    raw_word: None,
                },
            });
        }

        Ok(strings)
    }

    fn parse_userdata_type_mapping(
        &self,
        reader: &mut BinaryReader<'_>,
        type_version: u8,
    ) -> Result<Vec<Option<RawString>>, ParseError> {
        if type_version != 3 {
            return Ok(Vec::new());
        }

        let mut names = Vec::new();
        loop {
            let index = reader.read_u8()?;
            if index == 0 {
                break;
            }
            let Some(name) = self.read_string_ref(reader)? else {
                return Err(ParseError::UnsupportedValue {
                    field: "luau userdata type name",
                    value: 0,
                });
            };
            let slot = usize::from(index - 1);
            if names.len() <= slot {
                names.resize(slot + 1, None);
            }
            names[slot] = Some(name);
        }
        Ok(names)
    }

    fn parse_proto_table(
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: LuauChunkLayout,
    ) -> Result<Vec<FlatProto>, ParseError> {
        let proto_count = usize::try_from(reader.read_varint_u32_luau("luau proto count")?)
            .map_err(|_| ParseError::IntegerOverflow {
                field: "luau proto count",
                value: u64::MAX,
            })?;
        let mut protos = Vec::with_capacity(proto_count);

        for _ in 0..proto_count {
            protos.push(self.parse_flat_proto(reader, layout)?);
        }

        Ok(protos)
    }

    fn parse_flat_proto(
        &mut self,
        reader: &mut BinaryReader<'_>,
        layout: LuauChunkLayout,
    ) -> Result<FlatProto, ParseError> {
        let start = reader.offset();
        let max_stack_size = reader.read_u8()?;
        let num_params = reader.read_u8()?;
        let upvalue_count = reader.read_u8()?;
        let raw_is_vararg = reader.read_u8()? != 0;

        let flags = if layout.bytecode_version >= 4 {
            reader.read_u8()?
        } else {
            0
        };
        let type_info = if layout.bytecode_version >= 4 {
            let size = usize::try_from(reader.read_varint_u32_luau("luau proto type info size")?)
                .map_err(|_| ParseError::IntegerOverflow {
                field: "luau proto type info size",
                value: u64::MAX,
            })?;
            reader.read_exact(size)?.to_vec()
        } else {
            Vec::new()
        };

        let decoded = self.parse_instructions(reader)?;
        let constants = self.parse_constants(reader)?;
        let child_indices = self.parse_child_proto_indices(reader)?;
        let constants = self.normalize_constants(constants, child_indices.as_slice())?;
        let defined_start = reader.read_varint_u32_luau("luau linedefined")?;
        let debug_name = self.read_string_ref(reader)?;
        let debug_info = self.parse_debug_info(
            reader,
            decoded.word_pc_by_raw.as_slice(),
            decoded.raw_by_word_pc.as_slice(),
            upvalue_count,
        )?;

        Ok(FlatProto {
            proto: RawProto {
                common: RawProtoCommon {
                    source: None,
                    line_range: ProtoLineRange {
                        defined_start,
                        defined_end: defined_start,
                    },
                    signature: ProtoSignature {
                        num_params,
                        is_vararg: raw_is_vararg,
                        has_vararg_param_reg: false,
                        named_vararg_table: false,
                    },
                    frame: ProtoFrameInfo { max_stack_size },
                    instructions: decoded.instrs,
                    constants,
                    upvalues: RawUpvalueInfo {
                        common: RawUpvalueInfoCommon {
                            count: upvalue_count,
                            descriptors: Vec::new(),
                        },
                        extra: DialectUpvalueExtra::Luau(LuauUpvalueExtra),
                    },
                    debug_info,
                    children: Vec::new(),
                },
                extra: DialectProtoExtra::Luau(LuauProtoExtra {
                    flags,
                    type_info,
                    debug_name,
                }),
                origin: Origin {
                    span: Span {
                        offset: start,
                        size: reader.offset() - start,
                    },
                    raw_word: None,
                },
            },
            child_indices,
        })
    }

    fn parse_instructions(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<DecodedInstrs, ParseError> {
        let word_count = usize::try_from(reader.read_varint_u32_luau("luau code word count")?)
            .map_err(|_| ParseError::IntegerOverflow {
                field: "luau code word count",
                value: u64::MAX,
            })?;
        let code_offset = reader.offset();
        let mut words = Vec::with_capacity(word_count);
        for _ in 0..word_count {
            words.push(reader.read_u32_le()?);
        }

        let mut instrs = Vec::new();
        let mut word_pc_by_raw = Vec::new();
        let mut raw_by_word_pc = vec![None; word_count + 1];
        let mut word_pc = 0usize;

        while word_pc < words.len() {
            let word = words[word_pc];
            let opcode_byte = (word & 0xff) as u8;
            let opcode =
                LuauOpcode::try_from(opcode_byte).map_err(|invalid| ParseError::InvalidOpcode {
                    pc: word_pc,
                    opcode: invalid,
                })?;
            let aux = opcode
                .has_aux()
                .then(|| {
                    words
                        .get(word_pc + 1)
                        .copied()
                        .ok_or(ParseError::UnexpectedEof {
                            offset: code_offset + word_pc * 4,
                            requested: 8,
                            remaining: words.len().saturating_sub(word_pc) * 4,
                        })
                })
                .transpose()?;
            let operands = opcode.decode_operands(word);
            let raw_index = instrs.len() as u32;
            raw_by_word_pc[word_pc] = Some(raw_index);
            word_pc_by_raw.push(word_pc as u32);
            instrs.push(RawInstr {
                opcode: RawInstrOpcode::Luau(opcode),
                operands: RawInstrOperands::Luau(operands),
                extra: DialectInstrExtra::Luau(LuauInstrExtra {
                    pc: word_pc as u32,
                    word_len: if aux.is_some() { 2 } else { 1 },
                    aux,
                }),
                origin: Origin {
                    span: Span {
                        offset: code_offset + word_pc * 4,
                        size: if aux.is_some() { 8 } else { 4 },
                    },
                    raw_word: Some(u64::from(word)),
                },
            });
            word_pc += if aux.is_some() { 2 } else { 1 };
        }

        raw_by_word_pc[word_count] = Some(instrs.len() as u32);

        Ok(DecodedInstrs {
            instrs,
            word_pc_by_raw,
            raw_by_word_pc,
        })
    }

    fn parse_constants(
        &mut self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<RawConstPool, ParseError> {
        let const_count = usize::try_from(reader.read_varint_u32_luau("luau const count")?)
            .map_err(|_| ParseError::IntegerOverflow {
                field: "luau const count",
                value: u64::MAX,
            })?;
        let mut literals = Vec::new();
        let mut entries = Vec::with_capacity(const_count);

        for _ in 0..const_count {
            let tag = reader.read_u8()?;
            let entry = match tag {
                0 => {
                    let literal_index = literals.len();
                    literals.push(RawLiteralConst::Nil);
                    LuauConstEntry::Literal { literal_index }
                }
                1 => {
                    let literal_index = literals.len();
                    literals.push(RawLiteralConst::Boolean(reader.read_u8()? != 0));
                    LuauConstEntry::Literal { literal_index }
                }
                2 => {
                    let literal_index = literals.len();
                    literals.push(RawLiteralConst::Number(reader.read_f64_le()?));
                    LuauConstEntry::Literal { literal_index }
                }
                3 => {
                    let literal_index = literals.len();
                    let value =
                        self.read_string_ref(reader)?
                            .ok_or(ParseError::UnsupportedValue {
                                field: "luau string constant",
                                value: 0,
                            })?;
                    literals.push(RawLiteralConst::String(value));
                    LuauConstEntry::Literal { literal_index }
                }
                4 => LuauConstEntry::Import {
                    import_id: reader.read_u32_le()?,
                },
                5 => {
                    let key_count =
                        usize::try_from(reader.read_varint_u32_luau("luau table key count")?)
                            .map_err(|_| ParseError::IntegerOverflow {
                                field: "luau table key count",
                                value: u64::MAX,
                            })?;
                    let mut key_consts = Vec::with_capacity(key_count);
                    for _ in 0..key_count {
                        key_consts.push(reader.read_varint_u32_luau("luau table key const")?);
                    }
                    LuauConstEntry::Table { key_consts }
                }
                6 => LuauConstEntry::Closure {
                    proto_index: reader.read_varint_u32_luau("luau closure const proto")?,
                    child_proto_index: 0,
                },
                7 => LuauConstEntry::Vector {
                    x: reader.read_f32_le()?,
                    y: reader.read_f32_le()?,
                    z: reader.read_f32_le()?,
                    w: reader.read_f32_le()?,
                },
                8 => {
                    let key_count = usize::try_from(
                        reader.read_varint_u32_luau("luau table-with-constants key count")?,
                    )
                    .map_err(|_| ParseError::IntegerOverflow {
                        field: "luau table-with-constants key count",
                        value: u64::MAX,
                    })?;
                    let mut table_entries = Vec::with_capacity(key_count);
                    for _ in 0..key_count {
                        let key_const =
                            reader.read_varint_u32_luau("luau table-with-constants key")?;
                        let value_const = reader.read_i32_le()?;
                        table_entries.push(LuauTableConstEntry {
                            key_const,
                            value_const: (value_const >= 0).then_some(value_const as u32),
                        });
                    }
                    LuauConstEntry::TableWithConstants {
                        entries: table_entries,
                    }
                }
                _ => {
                    return Err(ParseError::InvalidConstantTag {
                        offset: reader.offset().saturating_sub(1),
                        tag,
                    });
                }
            };
            entries.push(entry);
        }

        Ok(RawConstPool {
            common: RawConstPoolCommon { literals },
            extra: DialectConstPoolExtra::Luau(LuauConstPoolExtra { entries }),
        })
    }

    fn normalize_constants(
        &self,
        mut constants: RawConstPool,
        child_indices: &[usize],
    ) -> Result<RawConstPool, ParseError> {
        let DialectConstPoolExtra::Luau(extra) = &mut constants.extra else {
            unreachable!("luau parser should only normalize luau constant pools");
        };
        for (const_index, entry) in extra.entries.iter_mut().enumerate() {
            let LuauConstEntry::Closure {
                proto_index,
                child_proto_index,
            } = entry
            else {
                continue;
            };
            *child_proto_index = child_indices
                .iter()
                .position(|candidate| *candidate == *proto_index as usize)
                .ok_or(ParseError::InvalidLuauClosureProto {
                    const_index,
                    proto_index: *proto_index,
                    child_count: child_indices.len(),
                })?;
        }
        Ok(constants)
    }

    fn parse_child_proto_indices(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Vec<usize>, ParseError> {
        let child_count = usize::try_from(reader.read_varint_u32_luau("luau child proto count")?)
            .map_err(|_| ParseError::IntegerOverflow {
            field: "luau child proto count",
            value: u64::MAX,
        })?;
        let mut children = Vec::with_capacity(child_count);
        for _ in 0..child_count {
            children.push(
                usize::try_from(reader.read_varint_u32_luau("luau child proto index")?).map_err(
                    |_| ParseError::IntegerOverflow {
                        field: "luau child proto index",
                        value: u64::MAX,
                    },
                )?,
            );
        }
        Ok(children)
    }

    fn parse_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        word_pc_by_raw: &[u32],
        raw_by_word_pc: &[Option<u32>],
        upvalue_count: u8,
    ) -> Result<RawDebugInfo, ParseError> {
        let line_info_enabled = reader.read_u8()? != 0;
        let (line_info, line_gap_log2) = if line_info_enabled {
            let line_gap_log2 = reader.read_u8()?;
            let code_word_count = raw_by_word_pc.len().saturating_sub(1);
            let lines =
                self.parse_line_info(reader, word_pc_by_raw, code_word_count, line_gap_log2)?;
            (lines, Some(line_gap_log2))
        } else {
            (Vec::new(), None)
        };

        let debug_info_enabled = reader.read_u8()? != 0;
        let (local_vars, local_regs, upvalue_names) = if debug_info_enabled {
            let symbols = self.parse_symbol_debug_info(reader, raw_by_word_pc, upvalue_count)?;
            (
                symbols.local_vars,
                symbols.local_regs,
                symbols.upvalue_names,
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        Ok(RawDebugInfo {
            common: RawDebugInfoCommon {
                line_info,
                local_vars,
                upvalue_names,
            },
            extra: DialectDebugExtra::Luau(LuauDebugExtra {
                line_gap_log2,
                local_regs,
            }),
        })
    }

    fn parse_line_info(
        &self,
        reader: &mut BinaryReader<'_>,
        word_pc_by_raw: &[u32],
        code_word_count: usize,
        line_gap_log2: u8,
    ) -> Result<Vec<u32>, ParseError> {
        if word_pc_by_raw.is_empty() {
            return Ok(Vec::new());
        }

        let intervals = ((code_word_count - 1) >> line_gap_log2) + 1;
        let mut relative_offsets = vec![0u8; code_word_count];
        let mut last_offset = 0u8;
        for item in &mut relative_offsets {
            last_offset = last_offset.wrapping_add(reader.read_u8()?);
            *item = last_offset;
        }

        let mut absolute_lines = vec![0i32; intervals];
        let mut last_line = 0i32;
        for item in &mut absolute_lines {
            last_line += reader.read_i32_le()?;
            *item = last_line;
        }

        Ok(word_pc_by_raw
            .iter()
            .map(|word_pc| {
                let word_pc = *word_pc as usize;
                let interval = word_pc >> line_gap_log2;
                let base = absolute_lines.get(interval).copied().unwrap_or_default();
                let delta = i32::from(relative_offsets.get(word_pc).copied().unwrap_or_default());
                (base + delta).max(0) as u32
            })
            .collect())
    }

    fn parse_symbol_debug_info(
        &self,
        reader: &mut BinaryReader<'_>,
        raw_by_word_pc: &[Option<u32>],
        upvalue_count: u8,
    ) -> Result<LuauSymbolDebugInfo, ParseError> {
        let local_count = usize::try_from(reader.read_varint_u32_luau("luau local debug count")?)
            .map_err(|_| ParseError::IntegerOverflow {
            field: "luau local debug count",
            value: u64::MAX,
        })?;
        let mut locals = Vec::with_capacity(local_count);
        let mut regs = Vec::with_capacity(local_count);

        for _ in 0..local_count {
            let name = self
                .read_string_ref(reader)?
                .ok_or(ParseError::UnsupportedValue {
                    field: "luau local debug name",
                    value: 0,
                })?;
            let start_word = reader.read_varint_u32_luau("luau local startpc")?;
            let end_word = reader.read_varint_u32_luau("luau local endpc")?;
            let reg = reader.read_u8()?;
            locals.push(RawLocalVar {
                name,
                start_pc: raw_pc_from_word_pc(start_word, raw_by_word_pc)?,
                end_pc: raw_pc_from_word_pc(end_word, raw_by_word_pc)?,
            });
            regs.push(reg);
        }

        let encoded_upvalue_names =
            usize::try_from(reader.read_varint_u32_luau("luau upvalue debug name count")?)
                .map_err(|_| ParseError::IntegerOverflow {
                    field: "luau upvalue debug name count",
                    value: u64::MAX,
                })?;
        if !self.options.mode.is_permissive() && encoded_upvalue_names != usize::from(upvalue_count)
        {
            return Err(ParseError::UnsupportedValue {
                field: "luau upvalue debug name count",
                value: encoded_upvalue_names as u64,
            });
        }

        let mut upvalue_names = Vec::with_capacity(encoded_upvalue_names);
        for _ in 0..encoded_upvalue_names {
            if let Some(name) = self.read_string_ref(reader)? {
                upvalue_names.push(name);
            }
        }

        Ok(LuauSymbolDebugInfo {
            local_vars: locals,
            local_regs: regs,
            upvalue_names,
        })
    }

    fn read_string_ref(
        &self,
        reader: &mut BinaryReader<'_>,
    ) -> Result<Option<RawString>, ParseError> {
        let id = reader.read_varint_u32_luau("luau string id")?;
        if id == 0 {
            return Ok(None);
        }

        let index = usize::try_from(id - 1).map_err(|_| ParseError::IntegerOverflow {
            field: "luau string id",
            value: u64::MAX,
        })?;
        self.strings
            .get(index)
            .cloned()
            .ok_or(ParseError::UnsupportedValue {
                field: "luau string id",
                value: id as u64,
            })
            .map(Some)
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
}

fn build_proto_tree(
    proto_index: usize,
    flat_protos: &mut [FlatProtoSlot],
) -> Result<RawProto, ParseError> {
    let slot = flat_protos
        .get_mut(proto_index)
        .ok_or(ParseError::UnsupportedValue {
            field: "luau proto index",
            value: proto_index as u64,
        })?;
    let flat = match std::mem::replace(slot, FlatProtoSlot::Building) {
        FlatProtoSlot::Pending(flat) => *flat,
        FlatProtoSlot::Building => {
            return Err(ParseError::UnsupportedValue {
                field: "luau proto cycle",
                value: proto_index as u64,
            });
        }
        FlatProtoSlot::Consumed => {
            return Err(ParseError::UnsupportedValue {
                field: "luau proto index reuse",
                value: proto_index as u64,
            });
        }
    };
    let mut proto = flat.proto;
    proto.common.children = flat
        .child_indices
        .iter()
        .copied()
        .map(|index| build_proto_tree(index, flat_protos))
        .collect::<Result<Vec<_>, _>>()?;
    flat_protos[proto_index] = FlatProtoSlot::Consumed;
    Ok(proto)
}

fn raw_pc_from_word_pc(word_pc: u32, raw_by_word: &[Option<u32>]) -> Result<u32, ParseError> {
    raw_by_word
        .get(word_pc as usize)
        .and_then(|value| *value)
        .ok_or(ParseError::UnsupportedValue {
            field: "luau debug pc",
            value: u64::from(word_pc),
        })
}
