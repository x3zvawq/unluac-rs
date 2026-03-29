use crate::parser::error::ParseError;
use crate::parser::raw::{
    DialectInstrExtra, Origin, RawInstr, RawInstrOpcode, RawInstrOperands, Span,
};
use crate::parser::reader::BinaryReader;

use super::layout::{PucLuaLayout, RawInstructionWord, read_instruction_words};

const MAXARG_SBX_18: i32 = ((1 << 18) - 1) >> 1;
const MAXARG_SBX_17: i32 = ((1 << 17) - 1) >> 1;
const MAXARG_SJ_25: i32 = ((1 << 25) - 1) >> 1;
const OFFSET_SC_8: i16 = (((1 << 8) - 1) >> 1) as i16;

/// family 共享的“按 opcode 声明解码成 `RawInstr`”骨架。
pub(crate) trait PucLuaInstructionCodec {
    type Opcode: Copy + Eq + TryFrom<u8, Error = u8>;
    type Fields: Copy;
    type ExtraWordPolicy: Copy;
    type Operands;

    fn decode_fields(word: u32) -> Self::Fields;
    fn opcode_byte(fields: Self::Fields) -> u8;
    fn decode_operands(opcode: Self::Opcode, fields: Self::Fields) -> Self::Operands;
    fn extra_word_policy(opcode: Self::Opcode) -> Self::ExtraWordPolicy;
    fn should_read_extra_word(policy: Self::ExtraWordPolicy, fields: Self::Fields) -> bool;
    fn opcode_label(opcode: Self::Opcode) -> &'static str;
    fn extra_arg_opcode() -> Self::Opcode;
    fn extra_arg_ax(fields: Self::Fields) -> u32;
    fn wrap_opcode(opcode: Self::Opcode) -> RawInstrOpcode;
    fn wrap_operands(operands: Self::Operands) -> RawInstrOperands;
    fn wrap_extra(pc: u32, word_len: u8, extra_arg: Option<u32>) -> DialectInstrExtra;
}

/// 通用的 PUC-Lua 指令解码骨架：
/// 版本文件只提供“如何拆位、如何解释 operand、什么情况下吃 helper word”。
pub(crate) fn decode_puc_lua_instructions<C>(
    words: &[RawInstructionWord],
) -> Result<Vec<RawInstr>, ParseError>
where
    C: PucLuaInstructionCodec,
{
    let mut instructions = Vec::with_capacity(words.len());
    let mut pc = 0_usize;

    while pc < words.len() {
        let entry = words[pc];
        let fields = C::decode_fields(entry.word);
        let opcode = C::Opcode::try_from(C::opcode_byte(fields))
            .map_err(|opcode| ParseError::InvalidOpcode { pc, opcode })?;

        let mut word_len = 1_u8;
        let extra_arg = {
            let policy = C::extra_word_policy(opcode);
            if C::should_read_extra_word(policy, fields) {
                word_len = 2;
                Some(read_puc_lua_extra_arg_word::<C>(words, pc, opcode)?)
            } else {
                None
            }
        };
        let operands = C::decode_operands(opcode, fields);

        instructions.push(RawInstr {
            opcode: C::wrap_opcode(opcode),
            operands: C::wrap_operands(operands),
            extra: C::wrap_extra(pc as u32, word_len, extra_arg),
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

/// 共享的“读取 instruction section 并解码成 `RawInstr`”骨架。
pub(crate) fn parse_puc_lua_instruction_section<C, ReadCount, Prepare>(
    reader: &mut BinaryReader<'_>,
    layout: &PucLuaLayout,
    mut read_count: ReadCount,
    mut prepare: Prepare,
    size_field: &'static str,
) -> Result<(usize, Vec<RawInstr>), ParseError>
where
    C: PucLuaInstructionCodec,
    ReadCount: FnMut(&mut BinaryReader<'_>, &'static str) -> Result<u32, ParseError>,
    Prepare: FnMut(&mut BinaryReader<'_>, &PucLuaLayout) -> Result<(), ParseError>,
{
    let count = read_count(reader, "instruction count")?;
    prepare(reader, layout)?;
    let words = read_instruction_words(reader, layout, count, size_field)?;
    let instructions = decode_puc_lua_instructions::<C>(&words)?;
    Ok((words.len(), instructions))
}

fn read_puc_lua_extra_arg_word<C>(
    words: &[RawInstructionWord],
    pc: usize,
    opcode: C::Opcode,
) -> Result<u32, ParseError>
where
    C: PucLuaInstructionCodec,
{
    let Some(helper) = words.get(pc + 1).copied() else {
        return Err(ParseError::MissingExtraArgWord {
            pc,
            opcode: C::opcode_label(opcode),
        });
    };
    let helper_fields = C::decode_fields(helper.word);
    let helper_opcode = C::Opcode::try_from(C::opcode_byte(helper_fields)).map_err(|found| {
        ParseError::InvalidExtraArgWord {
            pc,
            opcode: C::opcode_label(opcode),
            found,
        }
    })?;
    if helper_opcode != C::extra_arg_opcode() {
        return Err(ParseError::InvalidExtraArgWord {
            pc,
            opcode: C::opcode_label(opcode),
            found: C::opcode_byte(helper_fields),
        });
    }
    Ok(C::extra_arg_ax(helper_fields))
}

/// PUC-Lua 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) b: u16,
    pub(crate) c: u16,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
}

/// Lua 5.4 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields54 {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) k: bool,
    pub(crate) b: u8,
    pub(crate) c: u8,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
    pub(crate) sj: i32,
    pub(crate) sb: i16,
    pub(crate) sc: i16,
}

/// Lua 5.5 指令字公共位域拆解结果。
#[derive(Debug, Clone, Copy)]
pub(crate) struct DecodedInstructionFields55 {
    pub(crate) opcode: u8,
    pub(crate) a: u8,
    pub(crate) k: bool,
    pub(crate) b: u8,
    pub(crate) c: u8,
    pub(crate) bx: u32,
    pub(crate) sbx: i32,
    pub(crate) ax: u32,
    pub(crate) sj: i32,
    pub(crate) sb: i16,
    pub(crate) sc: i16,
    pub(crate) vb: u8,
    pub(crate) vc: u16,
}

/// 按 PUC-Lua 5.x 共享编码格式拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word(word: u32) -> DecodedInstructionFields {
    let opcode = (word & 0x3f) as u8;
    let a = ((word >> 6) & 0xff) as u8;
    let c = ((word >> 14) & 0x1ff) as u16;
    let b = ((word >> 23) & 0x1ff) as u16;
    let bx = (word >> 14) & 0x3ffff;
    let sbx = bx as i32 - MAXARG_SBX_18;
    let ax = word >> 6;

    DecodedInstructionFields {
        opcode,
        a,
        b,
        c,
        bx,
        sbx,
        ax,
    }
}

/// 按 Lua 5.4 的 7-bit opcode 编码拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word_54(word: u32) -> DecodedInstructionFields54 {
    let opcode = (word & 0x7f) as u8;
    let a = ((word >> 7) & 0xff) as u8;
    let k = ((word >> 15) & 0x1) != 0;
    let b = ((word >> 16) & 0xff) as u8;
    let c = ((word >> 24) & 0xff) as u8;
    let bx = (word >> 15) & 0x1ffff;
    let sbx = bx as i32 - MAXARG_SBX_17;
    let ax = word >> 7;
    let sj_raw = (word >> 7) & 0x1ffffff;
    let sj = sj_raw as i32 - MAXARG_SJ_25;
    let sb = i16::from(b) - OFFSET_SC_8;
    let sc = i16::from(c) - OFFSET_SC_8;

    DecodedInstructionFields54 {
        opcode,
        a,
        k,
        b,
        c,
        bx,
        sbx,
        ax,
        sj,
        sb,
        sc,
    }
}

/// 按 Lua 5.5 的 7-bit opcode 编码拆开一条 32-bit 指令字。
pub(crate) fn decode_instruction_word_55(word: u32) -> DecodedInstructionFields55 {
    let opcode = (word & 0x7f) as u8;
    let a = ((word >> 7) & 0xff) as u8;
    let k = ((word >> 15) & 0x1) != 0;
    let b = ((word >> 16) & 0xff) as u8;
    let c = ((word >> 24) & 0xff) as u8;
    let bx = (word >> 15) & 0x1ffff;
    let sbx = bx as i32 - MAXARG_SBX_17;
    let ax = word >> 7;
    let sj_raw = (word >> 7) & 0x1ffffff;
    let sj = sj_raw as i32 - MAXARG_SJ_25;
    let sb = i16::from(b) - OFFSET_SC_8;
    let sc = i16::from(c) - OFFSET_SC_8;
    let vb = ((word >> 16) & 0x3f) as u8;
    let vc = ((word >> 22) & 0x03ff) as u16;

    DecodedInstructionFields55 {
        opcode,
        a,
        k,
        b,
        c,
        bx,
        sbx,
        ax,
        sj,
        sb,
        sc,
        vb,
        vc,
    }
}
