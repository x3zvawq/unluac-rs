//! 这个模块承载 PUC-Lua 5.x 各版本 parser 共用的稳定事实。
//!
//! 入口文件只负责导出共享接口；具体实现按 `header / layout / instruction /
//! sections / strings / macros` 分开，避免共享层自己再次膨胀成新的巨型文件。

mod header;
mod instruction;
mod layout;
mod macros;
mod proto;
mod sections;
mod strings;

pub(crate) use self::header::{
    LUA_SIGNATURE, LUA52_LUAC_TAIL, LUA53_LUAC_DATA, LUA53_LUAC_INT, LUA53_LUAC_NUM,
    LUA54_LUAC_DATA, LUA54_LUAC_INT, LUA54_LUAC_NUM, LUA55_LUAC_DATA, LUA55_LUAC_INST,
    LUA55_LUAC_INT, LUA55_LUAC_NUM, parse_luac_data_header_prelude, read_f64_sentinel,
    read_i64_sentinel, read_i64_sentinel_endianness, validate_instruction_word_size,
    validate_main_proto_upvalue_count,
};
pub(crate) use self::instruction::{
    DecodedInstructionFields, DecodedInstructionFields54, DecodedInstructionFields55,
    PucLuaInstructionCodec, decode_instruction_word, decode_instruction_word_54,
    decode_instruction_word_55, parse_puc_lua_instruction_section,
};
pub(crate) use self::layout::{
    PucLuaLayout, read_layout_lua_integer, read_sized_i64, read_sized_u32,
};
pub(crate) use self::macros::{define_puc_lua_instruction_codec, define_puc_lua_opcodes};
pub(crate) use self::proto::{
    PucLuaProtoSections, finish_puc_lua_proto, inherit_source, read_proto_prelude,
};
pub(crate) use self::sections::{
    AbsDebugDriver, AbsLineInfoConfig, ClassicDebugDriver, count_u8, parse_abs_debug_sections,
    parse_child_protos, parse_classic_debug_sections, parse_tagged_literal_pool,
    parse_upvalue_descriptors, parse_upvalues_with_kinds, require_present,
    validate_optional_count_match,
};
pub(crate) use self::strings::build_raw_string;
