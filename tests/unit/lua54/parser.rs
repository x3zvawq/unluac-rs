//! 这些测试固定 Lua 5.4 parser 的层内契约。

use unluac::parser::{
    Dialect, DialectDebugExtra, DialectUpvalueExtra, DialectVersion, Lua54Opcode, ParseOptions,
    RawInstrOpcode, parse_lua54_chunk,
};

mod parse_lua54_chunk {
    use super::*;

    #[test]
    fn decodes_chunk_header_for_tbc_close_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.4/01_tbc_close.lua");

        assert_eq!(chunk.header.dialect, Dialect::PucLua);
        assert_eq!(chunk.header.version, DialectVersion::Lua54);
        assert_eq!(chunk.header.integer_size, 0);
        assert_eq!(chunk.header.lua_integer_size, Some(8));
        assert_eq!(chunk.header.size_t_size, 0);
        assert_eq!(chunk.header.instruction_size, 4);
        assert_eq!(chunk.header.number_size, 8);
        assert!(!chunk.header.integral_number);
    }

    #[test]
    fn decodes_lua54_specific_opcodes_for_tbc_close_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.4/01_tbc_close.lua");
        let mut opcodes = Vec::new();
        collect_opcodes(&chunk.main, &mut opcodes);

        assert!(opcodes.contains(&Lua54Opcode::VarArgPrep));
        assert!(opcodes.contains(&Lua54Opcode::Tbc));
        assert!(opcodes.contains(&Lua54Opcode::Close));
        assert!(opcodes.contains(&Lua54Opcode::LFalseSkip));
        assert!(opcodes.contains(&Lua54Opcode::LoadTrue));
        assert!(opcodes.contains(&Lua54Opcode::GetField));
        assert!(!opcodes.contains(&Lua54Opcode::ExtraArg));
    }

    #[test]
    fn reconstructs_debug_lines_and_upvalue_kinds_for_tbc_close_fixture() {
        let chunk = parse_fixture_with_debug("tests/lua_cases/lua5.4/01_tbc_close.lua");
        let close_metamethod = &chunk.main.common.children[0].common.children[0].common;

        assert_eq!(
            close_metamethod.debug_info.common.line_info.len(),
            close_metamethod.instructions.len()
        );

        let DialectDebugExtra::Lua54(debug_extra) = &close_metamethod.debug_info.extra else {
            panic!("lua54 fixture should carry lua54 debug extras");
        };
        assert!(!debug_extra.line_deltas.is_empty());

        let DialectUpvalueExtra::Lua54(upvalue_extra) = &close_metamethod.upvalues.extra else {
            panic!("lua54 fixture should carry lua54 upvalue extras");
        };
        assert_eq!(
            upvalue_extra.kinds.len(),
            usize::from(close_metamethod.upvalues.common.count)
        );
    }

    #[test]
    fn decodes_loadi_and_return1_for_const_local_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.4/02_const_local.lua");
        let read_answer = &chunk.main.common.children[0].common;
        let opcodes = read_answer
            .instructions
            .iter()
            .map(|instr| match instr.opcode {
                RawInstrOpcode::Lua54(opcode) => opcode,
                _ => panic!("lua54 fixture should only contain lua54 opcodes"),
            })
            .collect::<Vec<_>>();

        assert!(opcodes.contains(&Lua54Opcode::LoadI));
        assert!(opcodes.contains(&Lua54Opcode::Return1));
    }
}

fn parse_fixture(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case("lua5.4", source_relative);
    parse_lua54_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn parse_fixture_with_debug(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case_with_debug("lua5.4", source_relative);
    parse_lua54_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn collect_opcodes(proto: &unluac::parser::RawProto, out: &mut Vec<Lua54Opcode>) {
    for instr in &proto.common.instructions {
        let RawInstrOpcode::Lua54(opcode) = instr.opcode else {
            panic!("lua54 fixture should only contain lua54 opcodes");
        };
        out.push(opcode);
    }

    for child in &proto.common.children {
        collect_opcodes(child, out);
    }
}
