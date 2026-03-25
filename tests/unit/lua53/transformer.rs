//! 这些测试固定 Lua 5.3 transformer 的层内契约。
//!
//! 它们验证 raw -> low-IR 的 lowering 规则，重点覆盖 5.3 新增的整除和位运算，
//! 同时锁住 `_ENV`、方法调用和闭包捕获这些容易回归的路径。

use unluac::parser::{ParseOptions, parse_lua53_chunk};
use unluac::transformer::{
    AccessBase, AccessKey, BinaryOpKind, CaptureSource, LowInstr, Reg, UnaryOpKind, UpvalueRef,
    lower_lua53_chunk,
};

mod lower_lua53_chunk {
    use super::*;

    #[test]
    fn lowers_env_access_through_upvalue_table_for_integer_float_capture_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/05_integer_float_capture.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(
                instr,
                LowInstr::GetTable(get_table)
                    if get_table.base == AccessBase::Upvalue(UpvalueRef(0))
                        && matches!(get_table.key, AccessKey::Const(_))
            )
        }));
    }

    #[test]
    fn lowers_binary_bitwise_ops_for_closure_mesh_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/02_bitwise_closure_mesh.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(
                instr,
                LowInstr::BinaryOp(binary)
                    if matches!(
                        binary.op,
                        BinaryOpKind::BitAnd
                            | BinaryOpKind::BitOr
                            | BinaryOpKind::BitXor
                            | BinaryOpKind::Shl
                            | BinaryOpKind::Shr
                    )
            )
        }));
    }

    #[test]
    fn lowers_floor_div_for_idiv_float_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/03_idiv_float_branching.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(
                instr,
                LowInstr::BinaryOp(binary) if binary.op == BinaryOpKind::FloorDiv
            )
        }));
    }

    #[test]
    fn lowers_bit_not_for_bnot_mask_pipeline_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/07_bnot_mask_pipeline.lua");

        assert!(proto_has_instr(&lowered.main, &|instr| {
            matches!(instr, LowInstr::UnaryOp(unary) if unary.op == UnaryOpKind::BitNot)
        }));
    }

    #[test]
    fn preserves_method_call_kind_for_method_table_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/04_method_table_bitwise.lua");
        let method_calls = lowered
            .main
            .instrs
            .iter()
            .filter(|instr| matches!(instr, LowInstr::Call(call) if call.kind == unluac::transformer::CallKind::Method))
            .count();

        assert_eq!(method_calls, 2);
    }

    #[test]
    fn records_closure_captures_and_upvalue_writes_for_integer_float_capture_fixture() {
        let lowered = lower_fixture("tests/lua_cases/lua5.3/05_integer_float_capture.lua");
        let factory = &lowered.main.children[0];
        let inner = &factory.children[0];

        assert!(factory.instrs.iter().any(|instr| {
            matches!(
                instr,
                LowInstr::Closure(closure)
                    if closure.captures.len() == 2
                        && matches!(closure.captures[0].source, CaptureSource::Reg(Reg(1)))
                        && matches!(closure.captures[1].source, CaptureSource::Reg(Reg(2)))
            )
        }));
        assert!(inner.instrs.iter().any(|instr| {
            matches!(instr, LowInstr::SetUpvalue(set) if set.dst == UpvalueRef(0))
        }));
        assert!(inner.instrs.iter().any(|instr| {
            matches!(instr, LowInstr::SetUpvalue(set) if set.dst == UpvalueRef(1))
        }));
    }
}

fn lower_fixture(source_relative: &str) -> unluac::transformer::LoweredChunk {
    let bytes = crate::support::compile_lua_case("lua5.3", source_relative);
    let raw = parse_lua53_chunk(&bytes, ParseOptions::default())
        .expect("fixture should parse before lowering");
    lower_lua53_chunk(&raw).expect("fixture should lower")
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
