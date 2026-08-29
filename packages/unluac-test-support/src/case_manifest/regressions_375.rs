//! 回归 case 375；覆盖常量 if 中循环控制的 owner 保持。

use super::*;

pub(super) const REGRESSION_CASES_375: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_375_constant_if_loop_control.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_375_luau_constant_if_continue.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_O0_ONLY),
];
