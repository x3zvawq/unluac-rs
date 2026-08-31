//! 回归 case 411；Lua 5.5 普通 global 函数赋值不得伪装成重复声明。

use super::*;

pub(super) const REGRESSION_CASES_411: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_411_lua55_global_function_assignment.lua",
    &[LuaCaseDialect::Lua55],
)];
