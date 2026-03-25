//! 这些测试固定 Lua 5.4 transformer 的层内契约。

use unluac::parser::{ParseOptions, parse_lua54_chunk};
use unluac::transformer::{
    AccessBase, AccessKey, LowInstr, Reg, ValuePack, lower_lua54_chunk,
};

mod lower_lua54_chunk {
    use super::*;

    #[test]
    fn lowers_loadi_for_const_local_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.4/02_const_local.lua");
        let read_answer = &lowered.main.children[0];

        assert!(read_answer.instrs.iter().any(|instr| {
            matches!(instr, LowInstr::LoadInteger(load_int) if load_int.value == 42)
        }));
        assert!(read_answer.instrs.iter().any(|instr| {
            matches!(
                instr,
                LowInstr::Return(ret)
                    if matches!(ret.values, ValuePack::Fixed(range) if range.start == Reg(0) && range.len == 1)
            )
        }));
    }

    #[test]
    fn lowers_tbc_close_and_field_access_for_tbc_close_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.4/01_tbc_close.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| matches!(instr, LowInstr::Tbc(_))));
        assert!(proto_has_instr(&lowered.main, &|instr| matches!(instr, LowInstr::Close(_))));
        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(
                instr,
                LowInstr::GetTable(get_table)
                    if matches!(get_table.base, AccessBase::Reg(_))
                        && matches!(get_table.key, AccessKey::Const(_))
            )
        }));
    }

    #[test]
    fn lowers_lfalse_skip_into_false_load_and_jump() {
        let lowered = lower_fixture("tests/lua_cases/lua5.4/01_tbc_close.lua");
        let close_metamethod = &lowered.main.children[0].children[0];

        assert!(
            close_metamethod
                .instrs
                .windows(2)
                .any(|window| matches!(
                    window,
                    [LowInstr::LoadBool(load_bool), LowInstr::Jump(_)] if !load_bool.value
                ))
        );
        assert!(close_metamethod.instrs.iter().any(|instr| {
            matches!(instr, LowInstr::LoadBool(load_bool) if load_bool.value)
        }));
    }
}

fn lower_fixture(source_relative: &str) -> unluac::transformer::LoweredChunk {
    let bytes = crate::support::compile_lua_case("lua5.4", source_relative);
    let raw = parse_lua54_chunk(&bytes, ParseOptions::default())
        .expect("fixture should parse before lowering");
    lower_lua54_chunk(&raw).expect("fixture should lower")
}

fn proto_has_instr(
    proto: &unluac::transformer::LoweredProto,
    predicate: &dyn Fn(&LowInstr) -> bool,
) -> bool {
    proto.instrs.iter().any(predicate)
        || proto
            .children
            .iter()
            .any(|child| proto_has_instr(child, predicate))
}
