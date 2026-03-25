//! 这些测试固定 Lua 5.2 parser 的层内契约。
//!
//! 它们只验证 raw 解析事实本身，尤其是 5.2 新增的 upvalue 描述符和分离的
//! `TFORCALL/TFORLOOP` 指令布局。

use unluac::parser::{
    Dialect, DialectInstrExtra, DialectVersion, Lua52InstrExtra, Lua52Opcode, Lua52Operands,
    ParseOptions, RawInstrOpcode, RawInstrOperands, parse_lua52_chunk,
};

mod parse_lua52_chunk {
    use super::*;

    #[test]
    fn decodes_chunk_header_for_env_redirect_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.2/02_env_redirect.lua");

        assert_eq!(chunk.header.dialect, Dialect::PucLua);
        assert_eq!(chunk.header.version, DialectVersion::Lua52);
        assert_eq!(chunk.header.integer_size, 4);
        assert_eq!(chunk.header.size_t_size, 8);
        assert_eq!(chunk.header.instruction_size, 4);
        assert_eq!(chunk.header.number_size, 8);
        assert!(!chunk.header.integral_number);
    }

    #[test]
    fn decodes_upvalue_descriptors_and_gettabup_for_env_redirect_fixture() {
        let chunk = parse_fixture_with_debug("tests/lua_cases/lua5.2/02_env_redirect.lua");
        let proto = &chunk.main.common;

        assert_eq!(proto.upvalues.common.count, 1);
        assert_eq!(proto.upvalues.common.descriptors.len(), 1);
        assert_eq!(
            proto.upvalues.common.descriptors[0],
            unluac::parser::RawUpvalueDescriptor {
                in_stack: true,
                index: 0,
            }
        );
        assert_eq!(
            proto.debug_info.common.upvalue_names[0]
                .text
                .as_ref()
                .map(|text| text.value.as_str()),
            Some("_ENV")
        );
        assert!(matches!(
            proto.instructions[1].opcode,
            RawInstrOpcode::Lua52(Lua52Opcode::GetTabUp)
        ));
        assert!(matches!(
            proto.instructions[1].operands,
            RawInstrOperands::Lua52(Lua52Operands::ABC { a: 1, b: 0, c: 256 })
        ));
    }

    #[test]
    fn preserves_raw_pc_for_generic_for_pair_fixture() {
        let chunk = parse_fixture("tests/lua_cases/common/control_flow/04_generic_for.lua");
        let instructions = &chunk.main.common.instructions;

        assert!(matches!(
            instructions[17].opcode,
            RawInstrOpcode::Lua52(Lua52Opcode::TForCall)
        ));
        assert!(matches!(
            instructions[18].opcode,
            RawInstrOpcode::Lua52(Lua52Opcode::TForLoop)
        ));

        let DialectInstrExtra::Lua52(call_extra) = instructions[17].extra else {
            panic!("generic-for call should carry lua52 instruction extras");
        };
        let DialectInstrExtra::Lua52(loop_extra) = instructions[18].extra else {
            panic!("generic-for loop should carry lua52 instruction extras");
        };

        assert_eq!(
            call_extra,
            Lua52InstrExtra {
                pc: 17,
                word_len: 1,
                extra_arg: None,
            }
        );
        assert_eq!(
            loop_extra,
            Lua52InstrExtra {
                pc: 18,
                word_len: 1,
                extra_arg: None,
            }
        );
    }

    #[test]
    fn collapses_loadkx_and_setlist_extraarg_without_standalone_extraarg() {
        let chunk = parse_fixture("tests/lua_cases/lua5.2/03_extraarg_boundary.lua");
        let instructions = &chunk.main.common.instructions;

        assert!(
            instructions
                .iter()
                .all(|instr| !matches!(instr.opcode, RawInstrOpcode::Lua52(Lua52Opcode::ExtraArg))),
            "collapsed parser output should not expose standalone EXTRAARG"
        );
        assert!(
            instructions.iter().any(|instr| {
                matches!(
                    (instr.opcode, &instr.extra),
                    (
                        RawInstrOpcode::Lua52(Lua52Opcode::LoadKx),
                        DialectInstrExtra::Lua52(Lua52InstrExtra {
                            extra_arg: Some(262144),
                            ..
                        }),
                    )
                )
            }),
            "fixture should contain a collapsed LOADKX with the boundary constant index"
        );
        assert!(
            instructions.iter().any(|instr| {
                matches!(
                    (&instr.operands, &instr.extra),
                    (
                        RawInstrOperands::Lua52(Lua52Operands::ABC { a: 0, b: 45, c: 0 }),
                        DialectInstrExtra::Lua52(Lua52InstrExtra {
                            extra_arg: Some(arg),
                            ..
                        }),
                    ) if *arg > 511
                )
            }),
            "fixture should contain a SETLIST collapsed with EXTRAARG beyond the normal C range"
        );
    }

    #[test]
    fn decodes_nested_env_shadowing_and_closure_capture_for_env_shadow_fixture() {
        let chunk =
            parse_fixture_with_debug("tests/lua_cases/lua5.2/07_env_shadow_and_closure.lua");
        let main = &chunk.main.common;
        let make_reader = &main.children[0].common;
        let reader = &make_reader.children[0].common;

        assert_eq!(main.upvalues.common.count, 1);
        assert_eq!(make_reader.upvalues.common.count, 1);
        assert_eq!(reader.upvalues.common.count, 2);

        let upvalue_names = reader
            .debug_info
            .common
            .upvalue_names
            .iter()
            .filter_map(|name| name.text.as_ref().map(|text| text.value.as_str()))
            .collect::<Vec<_>>();
        assert!(upvalue_names.contains(&"_ENV"));
        assert!(upvalue_names.contains(&"prefix"));
    }
}

fn parse_fixture(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case("lua5.2", source_relative);
    parse_lua52_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn parse_fixture_with_debug(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case_with_debug("lua5.2", source_relative);
    parse_lua52_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}
