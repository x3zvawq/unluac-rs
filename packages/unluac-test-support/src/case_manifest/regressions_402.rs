//! 回归 case 402；函数内 binding 边界与普通 name 函数声明糖应完整保留。

use super::*;

pub(super) const REGRESSION_CASES_402: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_402_function_sugar_nested_local_ids.lua",
        &[LuaCaseDialect::Lua54],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_402_upvalue_function_decl.lua",
        &[LuaCaseDialect::Lua54],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_402_method_alias_nested_write_ids.lua",
        &[LuaCaseDialect::Lua54],
    ),
];
