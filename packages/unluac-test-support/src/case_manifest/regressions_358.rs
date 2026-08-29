//! 回归 case 358；覆盖 temp-inline 的必达、条件、重复与构造器分配执行区域。

use super::*;

pub(super) const REGRESSION_CASES_358: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_358_temp_inline_nested_regions.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_358_temp_inline_repeated_closure.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_358_luau_fastcall_conditional.lua",
        LUAU_ONLY,
    ),
];
