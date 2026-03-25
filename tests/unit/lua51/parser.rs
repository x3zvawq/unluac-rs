//! 这些测试固定 Lua 5.1 parser 的层内契约。
//!
//! 它们只验证 raw 解析事实本身，不关心主 pipeline 或后续 lowering 是否已经接上，
//! 因此归类为 unit，而不是 regression。

use unluac::parser::{
    Dialect, DialectInstrExtra, DialectVersion, Lua51InstrExtra, Lua51Opcode, Lua51Operands,
    ParseOptions, RawInstrOpcode, RawInstrOperands, RawLiteralConst, StringEncoding,
    parse_lua51_chunk,
};

const SETFENV_CHUNK_HEX: &str = "
1b4c7561510001040804080023000000000000004074657374732f6361736573
2f6c7561352e312f30315f73657466656e762e6c756100000000000000000000
0002050d000000240000004a4000004940408085800000c0000000000180009c
40800185c00000c1800000000100001c0180009c4000001e0080000400000004
060000000000000076616c75650004090000000000000066726f6d2d656e7600
04080000000000000073657466656e76000406000000000000007072696e7400
0100000000000000000000000100000003000000000000020300000005000000
1e0000011e0080000100000004060000000000000076616c7565000000000003
00000002000000020000000300000000000000000000000d0000000300000005
00000006000000090000000900000009000000090000000a0000000a0000000a
0000000a0000000a0000000a000000020000000b00000000000000726561645f
76616c756500010000000c0000000400000000000000656e7600030000000c00
00000000000000
";

const CLOSURE_COUNTER_CHUNK_HEX: &str = "
1b4c7561510001040804080035000000000000004074657374732f6361736573
2f636f6d6d6f6e2f66756e6374696f6e732f30325f636c6f737572655f636f75
6e7465722e6c7561000000000000000000000002070f00000024000000400000
00810000005c80000185400000c1800000000180001c8180004001800081c100
005c810001800180009c0180009c4000001e0080000400000003000000000000
24400406000000000000007072696e7400040800000000000000636c6f737572
6500030000000000000040010000000000000000000000010000000800000000
0100030500000040000000a4000000000080009e0000011e0080000000000001
000000000000000000000004000000070000000101000309000000440000009b
40000016000080810000004c80800048000000440000005e0000011e00800001
00000003000000000000f03f0000000009000000050000000500000005000000
0500000005000000050000000600000006000000070000000100000005000000
000000007374657000000000000800000001000000060000000000000076616c
7565000500000002000000070000000700000007000000080000000200000006
000000000000007374617274000000000004000000060000000000000076616c
7565000100000004000000000000000f000000080000000a0000000a0000000a
0000000b0000000b0000000b0000000b0000000b0000000b0000000b0000000b
0000000b0000000b0000000b000000020000000d000000000000006d616b655f
636f756e74657200010000000e0000000800000000000000636f756e74657200
040000000e00000000000000
";

mod parse_lua51_chunk {
    use super::*;

    #[test]
    fn decodes_chunk_header_for_setfenv_fixture() {
        let chunk = parse_fixture(SETFENV_CHUNK_HEX);

        assert_eq!(chunk.header.dialect, Dialect::PucLua);
        assert_eq!(chunk.header.version, DialectVersion::Lua51);
        assert_eq!(chunk.header.integer_size, 4);
        assert_eq!(chunk.header.size_t_size, 8);
        assert_eq!(chunk.header.instruction_size, 4);
        assert_eq!(chunk.header.number_size, 8);
        assert!(!chunk.header.integral_number);
    }

    #[test]
    fn decodes_main_proto_shape_for_setfenv_fixture() {
        let chunk = parse_fixture(SETFENV_CHUNK_HEX);
        let proto = &chunk.main.common;

        assert_eq!(
            proto
                .source
                .as_ref()
                .and_then(|source| source.text.as_ref())
                .map(|text| text.value.as_str().ends_with("/01_setfenv.lua")),
            Some(true)
        );
        assert_eq!(proto.instructions.len(), 13);
        assert_eq!(proto.constants.common.literals.len(), 4);
        assert_eq!(proto.children.len(), 1);
        assert_eq!(proto.debug_info.common.line_info.len(), 13);
        assert_eq!(proto.debug_info.common.local_vars.len(), 2);
    }

    #[test]
    fn decodes_literal_constants_for_setfenv_fixture() {
        let chunk = parse_fixture(SETFENV_CHUNK_HEX);
        let literals = &chunk.main.common.constants.common.literals;

        assert_eq!(string_constant(&literals[0]), Some("value"));
        assert_eq!(string_constant(&literals[1]), Some("from-env"));
        assert_eq!(string_constant(&literals[2]), Some("setfenv"));
        assert_eq!(string_constant(&literals[3]), Some("print"));
    }

    #[test]
    fn decodes_nested_closure_structure_for_closure_counter_fixture() {
        let chunk = parse_fixture(CLOSURE_COUNTER_CHUNK_HEX);
        let main = &chunk.main.common;
        let outer = &main.children[0].common;
        let inner = &outer.children[0].common;

        assert_eq!(main.children.len(), 1);
        assert_eq!(outer.children.len(), 1);
        assert_eq!(outer.signature.num_params, 1);
        assert_eq!(inner.signature.num_params, 1);
        assert_eq!(inner.upvalues.common.count, 1);
        assert_eq!(inner.debug_info.common.upvalue_names.len(), 1);
        assert_eq!(
            inner.debug_info.common.upvalue_names[0]
                .text
                .as_ref()
                .map(|text| text.value.as_str()),
            Some("value")
        );
    }

    #[test]
    fn preserves_raw_pc_information_for_closure_counter_fixture() {
        let chunk = parse_fixture(CLOSURE_COUNTER_CHUNK_HEX);
        let instructions = &chunk.main.common.instructions;

        assert!(matches!(
            instructions[0].opcode,
            RawInstrOpcode::Lua51(Lua51Opcode::Closure)
        ));
        assert!(matches!(
            instructions[1].operands,
            RawInstrOperands::Lua51(Lua51Operands::AB { a: 1, b: 0 })
        ));

        let DialectInstrExtra::Lua51(first_extra) = instructions[0].extra else {
            panic!("lua51 fixture should preserve lua51 instruction extras");
        };
        let DialectInstrExtra::Lua51(last_extra) = instructions[14].extra else {
            panic!("lua51 fixture should preserve lua51 instruction extras");
        };

        assert_eq!(
            first_extra,
            Lua51InstrExtra {
                pc: 0,
                word_len: 1,
                setlist_extra_arg: None,
            }
        );
        assert_eq!(
            last_extra,
            Lua51InstrExtra {
                pc: 14,
                word_len: 1,
                setlist_extra_arg: None,
            }
        );
    }

    #[test]
    fn decodes_gbk_string_constant_when_requested() {
        let bytes = patch_first_occurrence(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            b"value",
            b"\xC4\xE3\xBA\xC3!",
        );
        let chunk = parse_lua51_chunk(
            &bytes,
            ParseOptions {
                string_encoding: StringEncoding::Gbk,
                ..ParseOptions::default()
            },
        )
        .expect("gbk fixture should parse");

        let literals = &chunk.main.common.constants.common.literals;
        assert_eq!(string_constant(&literals[0]), Some("你好!"));
    }
}

fn parse_fixture(hex: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::decode_hex(hex);
    parse_lua51_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn string_constant(constant: &RawLiteralConst) -> Option<&str> {
    match constant {
        RawLiteralConst::String(raw) => raw.text.as_ref().map(|text| text.value.as_str()),
        _ => None,
    }
}

fn patch_first_occurrence(haystack: &[u8], from: &[u8], to: &[u8]) -> Vec<u8> {
    assert_eq!(from.len(), to.len(), "补丁前后长度必须一致");

    let Some(offset) = haystack
        .windows(from.len())
        .position(|window| window == from)
    else {
        panic!("fixture should contain target bytes");
    };

    let mut patched = haystack.to_vec();
    patched[offset..offset + from.len()].copy_from_slice(to);
    patched
}
