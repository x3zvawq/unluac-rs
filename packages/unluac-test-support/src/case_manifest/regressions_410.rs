//! 回归 case 410；Lua 5.5 多目标 global 声明的尾部调用结果必须整体恢复。

use super::*;

pub(super) const REGRESSION_CASES_410: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_410_lua55_multi_global_tail_call.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_410_lua55_mixed_global_rhs.lua",
        &[LuaCaseDialect::Lua55],
    )
    .with_expectation(LuaCaseExpectation::GlobalDeclResidual),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_410_lua55_wide_mixed_global_rhs.lua",
        &[LuaCaseDialect::Lua55],
    )
    .with_expectation(LuaCaseExpectation::GlobalDeclResidual),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_410_lua55_global_nested_callee.lua",
        &[LuaCaseDialect::Lua55],
    ),
];
