//! 这些测试固定 Lua 5.3 parser 的层内契约。
//!
//! 它们只验证 raw 解析事实本身，重点覆盖 5.3 的 header 差异、整数/浮点常量标签，
//! 以及新增的位运算/整除 opcode 和字符串编码后的闭包调试信息。

use unluac::parser::{
    Dialect, DialectVersion, Lua53Opcode, ParseOptions, RawInstrOpcode, RawLiteralConst,
    RawUpvalueDescriptor, parse_lua53_chunk,
};

mod parse_lua53_chunk {
    use super::*;

    #[test]
    fn decodes_chunk_header_for_idiv_float_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.3/03_idiv_float_branching.lua");

        assert_eq!(chunk.header.dialect, Dialect::PucLua);
        assert_eq!(chunk.header.version, DialectVersion::Lua53);
        assert_eq!(chunk.header.integer_size, 4);
        assert_eq!(chunk.header.lua_integer_size, Some(8));
        assert_eq!(chunk.header.size_t_size, 8);
        assert_eq!(chunk.header.instruction_size, 4);
        assert_eq!(chunk.header.number_size, 8);
        assert!(!chunk.header.integral_number);
    }

    #[test]
    fn preserves_integer_and_float_constant_tags_for_idiv_float_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.3/03_idiv_float_branching.lua");
        let analyze = &chunk.main.common.children[0].common;
        let literals = &analyze.constants.common.literals;

        assert!(
            literals
                .iter()
                .any(|literal| matches!(literal, RawLiteralConst::Integer(0)))
        );
        assert!(
            literals
                .iter()
                .any(|literal| matches!(literal, RawLiteralConst::Integer(3)))
        );
        assert!(
            literals
                .iter()
                .any(|literal| matches!(literal, RawLiteralConst::Number(value) if *value == 0.0))
        );
        assert!(
            literals
                .iter()
                .any(|literal| matches!(literal, RawLiteralConst::Number(value) if *value == 0.4))
        );
    }

    #[test]
    fn decodes_binary_bitwise_opcodes_for_closure_mesh_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.3/02_bitwise_closure_mesh.lua");
        let mut opcodes = Vec::new();
        collect_opcodes(&chunk.main, &mut opcodes);

        assert!(opcodes.contains(&Lua53Opcode::Band));
        assert!(opcodes.contains(&Lua53Opcode::Bor));
        assert!(opcodes.contains(&Lua53Opcode::Bxor));
        assert!(opcodes.contains(&Lua53Opcode::Shl));
        assert!(opcodes.contains(&Lua53Opcode::Shr));
    }

    #[test]
    fn decodes_bnot_opcode_for_bnot_mask_pipeline_fixture() {
        let chunk = parse_fixture("tests/lua_cases/lua5.3/07_bnot_mask_pipeline.lua");
        let mut opcodes = Vec::new();
        collect_opcodes(&chunk.main, &mut opcodes);

        assert!(opcodes.contains(&Lua53Opcode::BNot));
    }

    #[test]
    fn decodes_upvalue_descriptors_and_names_for_integer_float_capture_fixture() {
        let chunk = parse_fixture_with_debug("tests/lua_cases/lua5.3/05_integer_float_capture.lua");
        let inner = &chunk.main.common.children[0].common.children[0].common;

        assert_eq!(inner.upvalues.common.count, 2);
        assert_eq!(
            inner.upvalues.common.descriptors,
            vec![
                RawUpvalueDescriptor {
                    in_stack: true,
                    index: 1,
                },
                RawUpvalueDescriptor {
                    in_stack: true,
                    index: 2,
                },
            ]
        );

        let names = inner
            .debug_info
            .common
            .upvalue_names
            .iter()
            .filter_map(|name| name.text.as_ref().map(|text| text.value.as_str()))
            .collect::<Vec<_>>();
        assert!(names.contains(&"base_int"));
        assert!(names.contains(&"base_float"));
    }
}

fn parse_fixture(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case("lua5.3", source_relative);
    parse_lua53_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn parse_fixture_with_debug(source_relative: &str) -> unluac::parser::RawChunk {
    let bytes = crate::support::compile_lua_case_with_debug("lua5.3", source_relative);
    parse_lua53_chunk(&bytes, ParseOptions::default()).expect("fixture should parse")
}

fn collect_opcodes(proto: &unluac::parser::RawProto, out: &mut Vec<Lua53Opcode>) {
    for instr in &proto.common.instructions {
        let RawInstrOpcode::Lua53(opcode) = instr.opcode else {
            panic!("lua53 fixture should only contain lua53 opcodes");
        };
        out.push(opcode);
    }

    for child in &proto.common.children {
        collect_opcodes(child, out);
    }
}
