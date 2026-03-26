//! 这些测试固定 Lua 5.5 parser 的层内契约。

use unluac::parser::{
    Dialect, DialectDebugExtra, DialectVersion, Lua55Opcode, ParseOptions, RawInstrOpcode,
    parse_lua55_chunk,
};

mod parse_lua55_chunk {
    use super::*;

    #[test]
    fn decodes_chunk_header_for_global_basic_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.5/01_global_basic.lua");

        assert_eq!(chunk.header.dialect, Dialect::PucLua);
        assert_eq!(chunk.header.version, DialectVersion::Lua55);
        assert_eq!(chunk.header.integer_size, 4);
        assert_eq!(chunk.header.lua_integer_size, Some(8));
        assert_eq!(chunk.header.size_t_size, 0);
        assert_eq!(chunk.header.instruction_size, 4);
        assert_eq!(chunk.header.number_size, 8);
        assert!(!chunk.header.integral_number);
    }

    #[test]
    fn decodes_errnnil_getvarg_and_folds_extraarg() {
        let global_chunk = parse_fixture("tests/lua_cases/lua5.5/01_global_basic.lua");
        let vararg_chunk = parse_fixture("tests/lua_cases/lua5.5/08_named_vararg_index_only.lua");

        let mut global_opcodes = Vec::new();
        collect_opcodes(&global_chunk.main, &mut global_opcodes);
        assert!(global_opcodes.contains(&Lua55Opcode::ErrNNil));
        assert!(global_opcodes.contains(&Lua55Opcode::VarArgPrep));

        let mut vararg_opcodes = Vec::new();
        collect_opcodes(&vararg_chunk.main, &mut vararg_opcodes);
        assert!(vararg_opcodes.contains(&Lua55Opcode::GetVarg));
        assert!(vararg_opcodes.contains(&Lua55Opcode::VarArg));
        assert!(!vararg_opcodes.contains(&Lua55Opcode::ExtraArg));
    }

    #[test]
    fn marks_named_vararg_table_and_debug_metadata() {
        let chunk = parse_fixture_with_debug("tests/lua_cases/lua5.5/07_named_vararg_return.lua");
        let expose = &chunk.main.common.children[0].common;

        assert!(expose.signature.is_vararg);
        assert!(expose.signature.has_vararg_param_reg);
        assert!(expose.signature.named_vararg_table);
        assert!(
            expose.instructions.iter().any(|instr| {
                matches!(instr.opcode, RawInstrOpcode::Lua55(Lua55Opcode::Return1))
            })
        );

        let DialectDebugExtra::Lua55(debug_extra) = &expose.debug_info.extra else {
            panic!("lua55 fixture should carry lua55 debug extras");
        };
        assert!(!debug_extra.line_deltas.is_empty());
        assert!(expose.debug_info.common.line_info.len() >= expose.instructions.len());
    }

    #[test]
    fn distinguishes_hidden_vararg_parameter_from_materialized_vararg_table() {
        let chunk = parse_fixture("tests/lua_cases/lua5.5/08_named_vararg_index_only.lua");
        let probe = &chunk.main.common.children[0].common;

        assert!(probe.signature.is_vararg);
        assert!(probe.signature.has_vararg_param_reg);
        assert!(!probe.signature.named_vararg_table);
    }
}

fn parse_fixture(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case("lua5.5", source_relative);
    parse_lua55_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn parse_fixture_with_debug(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case_with_debug("lua5.5", source_relative);
    parse_lua55_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn collect_opcodes(proto: &unluac::parser::RawProto, out: &mut Vec<Lua55Opcode>) {
    for instr in &proto.common.instructions {
        let RawInstrOpcode::Lua55(opcode) = instr.opcode else {
            panic!("lua55 fixture should only contain lua55 opcodes");
        };
        out.push(opcode);
    }

    for child in &proto.common.children {
        collect_opcodes(child, out);
    }
}
