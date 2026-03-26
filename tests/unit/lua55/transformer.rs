//! 这些测试固定 Lua 5.5 transformer 的层内契约。

use unluac::parser::{ParseOptions, parse_lua55_chunk};
use unluac::transformer::{AccessBase, LowInstr, Reg, ValuePack, lower_lua55_chunk};

mod lower_lua55_chunk {
    use super::*;

    #[test]
    fn lowers_errnnil_for_global_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.5/01_global_basic.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(instr, LowInstr::ErrNil(err_nil) if err_nil.name.is_some())
        }));
    }

    #[test]
    fn lowers_named_vararg_index_reads_for_getvarg_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.5/08_named_vararg_index_only.lua");
        let probe = &lowered.main.children[0];

        assert!(probe.instrs.iter().any(|instr| {
            matches!(
                instr,
                LowInstr::GetTable(get_table)
                    if matches!(get_table.base, AccessBase::Reg(reg) if reg == Reg(1))
            )
        }));
        assert!(
            probe
                .instrs
                .iter()
                .any(|instr| matches!(instr, LowInstr::VarArg(_)))
        );
    }

    #[test]
    fn keeps_named_vararg_return_as_entry_register_value() {
        let lowered = lower_fixture("tests/lua_cases/lua5.5/07_named_vararg_return.lua");
        let expose = &lowered.main.children[0];

        assert!(expose.instrs.iter().any(|instr| {
            matches!(
                instr,
                LowInstr::Return(ret)
                    if matches!(ret.values, ValuePack::Fixed(range) if range.start == Reg(1) && range.len == 1)
            )
        }));
    }
}

fn lower_fixture(source_relative: &str) -> unluac::transformer::LoweredChunk {
    let bytes = crate::support::compile_lua_case("lua5.5", source_relative);
    let raw = parse_lua55_chunk(&bytes, ParseOptions::default())
        .expect("fixture should parse before lowering");
    lower_lua55_chunk(&raw).expect("fixture should lower")
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
