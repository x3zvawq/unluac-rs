//! 单元 case 矩阵；按通用与方言专属基础能力登记，不负责展开 dialect/variant。

use super::*;

pub(super) const UNIT_CASES: &[LuaCaseMatrixEntry] = &[
    // ── common cases ──
    // 每个文件内部以 `local function test_xxx()` 包裹，print 首参带 file#N 标签以便逐 proto 定位。
    LuaCaseMatrixEntry::new("tests/unit-case/common_01_basics.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_02_control_flow.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_03_repeat_until.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_04_generic_for.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_05_boolean_expr.lua", ALL_DIALECTS),
    // boolean_regression 包含原 tricky/32、33（ALL_NON_LUAU），取最严格的 dialect 集
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_06_boolean_regression.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_07_return_and_multiret.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/common_08_closures.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_09_method_and_self.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/common_10_tables.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_11_runtime.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_12_string_encoding.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_13_path_conditions.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_14_loop_lexical_arms.lua",
        ALL_DIALECTS,
    ),
    // ── dialect-specific cases ──
    LuaCaseMatrixEntry::new("tests/unit-case/lua51_01.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_01_env.lua", PUC_LUA_GE_52).with_options(
        LuaCaseOptions {
            retain_debug: true,
            ..LuaCaseOptions::DEFAULT
        },
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_02_goto.lua", LUA_GOTO_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_03_extraarg_boundary.lua", PUC_LUA_52)
        .with_options(NO_RECOMPILE_STRESS_OPTIONS),
    LuaCaseMatrixEntry::new("tests/unit-case/lua53_01.lua", PUC_LUA_GE_53),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_01_close.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_02_const.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_01_global.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_02_named_vararg.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/luajit_01.lua", LUAJIT_ONLY),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/luajit_02_ljlib_table_remove.lua",
        LUAJIT_ONLY,
    )
    .with_expectation(LuaCaseExpectation::LuaJitBuiltinTableRemove),
    LuaCaseMatrixEntry::new("tests/unit-case/luau_01.lua", LUAU_ONLY),
    LuaCaseMatrixEntry::new("tests/unit-case/luau_02_vector.lua", LUAU_ONLY)
        .with_options(LUAU_VECTOR_OPTIONS),
];
