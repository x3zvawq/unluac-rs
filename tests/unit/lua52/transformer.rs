//! 这些测试固定 Lua 5.2 transformer 的层内契约。
//!
//! 它们验证 raw -> low-IR 的 lowering 规则，重点覆盖 5.2 新增的
//! `GETTABUP/SETTABUP`、分离的 generic-for pair，以及 `JMP(A)` close 语义。

use unluac::parser::{ParseOptions, parse_lua52_chunk};
use unluac::transformer::{
    AccessBase, AccessKey, BranchOperands, BranchPredicate, CaptureSource, InstrRef, LowInstr, Reg,
    RegRange, ResultPack, UpvalueRef, ValueOperand, ValuePack, lower_lua52_chunk,
};

mod lower_lua52_chunk {
    use super::*;

    #[test]
    fn lowers_env_redirect_upvalue_table_accesses() {
        let lowered = lower_fixture("tests/lua_cases/lua5.2/02_env_redirect.lua");
        let instrs = &lowered.main.instrs;

        assert!(matches!(
            &instrs[1],
            LowInstr::GetTable(instr)
                if instr.base == AccessBase::Upvalue(UpvalueRef(0))
                    && instr.key == AccessKey::Const(unluac::transformer::ConstRef(0))
        ));
        assert!(matches!(
            &instrs[2],
            LowInstr::SetTable(instr)
                if instr.base == AccessBase::Reg(Reg(0))
                    && instr.key == AccessKey::Const(unluac::transformer::ConstRef(0))
                    && instr.value == ValueOperand::Reg(Reg(1))
        ));
        assert!(matches!(
            &instrs[5],
            LowInstr::GetTable(instr)
                if instr.base == AccessBase::Reg(Reg(0))
                    && instr.key == AccessKey::Const(unluac::transformer::ConstRef(0))
        ));
    }

    #[test]
    fn lowers_generic_for_into_call_and_loop_pair() {
        let lowered = lower_fixture("tests/lua_cases/common/control_flow/04_generic_for.lua");
        let instrs = &lowered.main.instrs;

        assert!(matches!(
            &instrs[17],
            LowInstr::GenericForCall(instr)
                if instr.state == RegRange::new(Reg(2), 3)
                    && instr.results == ResultPack::Fixed(RegRange::new(Reg(5), 2))
        ));
        assert!(matches!(
            &instrs[18],
            LowInstr::GenericForLoop(instr)
                if instr.control == Reg(4)
                    && instr.bindings == RegRange::new(Reg(5), 2)
                    && instr.body_target == InstrRef(10)
                    && instr.exit_target == InstrRef(19)
        ));
    }

    #[test]
    fn lowers_helper_and_direct_jump_close_semantics() {
        let lowered = lower_fixture("tests/lua_cases/common/control_flow/05_break_and_closure.lua");
        let instrs = &lowered.main.instrs;

        assert!(matches!(
            &instrs[8],
            LowInstr::Closure(instr)
                if instr.captures.len() == 1
                    && matches!(instr.captures[0].source, CaptureSource::Reg(Reg(5)))
        ));
        assert!(matches!(
            &instrs[10],
            LowInstr::Branch(instr)
                if instr.cond.predicate == BranchPredicate::Eq
                    && instr.cond.operands
                        == BranchOperands::Binary(
                            unluac::transformer::CondOperand::Reg(Reg(4)),
                            unluac::transformer::CondOperand::Const(unluac::transformer::ConstRef(3)),
                        )
                    && !instr.cond.negated
                    && instr.then_target == InstrRef(11)
                    && instr.else_target == InstrRef(13)
        ));
        assert!(matches!(
            &instrs[11],
            LowInstr::Close(instr) if instr.from == Reg(5)
        ));
        assert!(matches!(
            &instrs[12],
            LowInstr::Jump(instr) if instr.target == InstrRef(16)
        ));
        assert!(matches!(
            &instrs[13],
            LowInstr::Close(instr) if instr.from == Reg(5)
        ));
        assert!(matches!(
            &instrs[14],
            LowInstr::Jump(instr) if instr.target == InstrRef(15)
        ));
    }

    #[test]
    fn lowers_extraarg_fixture_into_high_const_loads_and_boundary_setlist() {
        let lowered = lower_fixture("tests/lua_cases/lua5.2/03_extraarg_boundary.lua");
        let instrs = &lowered.main.instrs;

        assert!(
            instrs.iter().any(|instr| {
                matches!(
                    instr,
                    LowInstr::SetList(set_list)
                        if set_list.base == Reg(0)
                            && set_list.values == ValuePack::Fixed(RegRange::new(Reg(1), 45))
                            && set_list.start_index == 262101
                )
            }),
            "fixture should lower the collapsed SETLIST+EXTRAARG tail into one high start-index set-list"
        );
        assert!(
            instrs.iter().any(|instr| {
                matches!(
                    instr,
                    LowInstr::LoadConst(load)
                        if load.value == unluac::transformer::ConstRef(262144)
                            && matches!(load.dst, Reg(1) | Reg(2) | Reg(45))
                )
            }),
            "fixture should lower LOADKX into load-const for the boundary constant"
        );
        assert!(
            instrs.iter().any(|instr| {
                matches!(
                    instr,
                    LowInstr::GetTable(get_table)
                        if get_table.dst == Reg(2)
                            && get_table.base == AccessBase::Reg(Reg(0))
                            && get_table.key == AccessKey::Reg(Reg(2))
                )
            }),
            "high table index should lower through a register key after LOADKX"
        );
    }
}

fn lower_fixture(source_relative: &str) -> unluac::transformer::LoweredChunk {
    let bytes = crate::support::compile_lua_case("lua5.2", source_relative);
    let raw = parse_lua52_chunk(&bytes, ParseOptions::default())
        .expect("fixture should parse before lowering");
    lower_lua52_chunk(&raw).expect("fixture should lower")
}
