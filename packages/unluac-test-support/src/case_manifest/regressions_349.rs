//! 回归 case 349；覆盖嵌套循环 continue 的精确 owner。

use super::*;

pub(super) const REGRESSION_CASES_349: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_349_luau_nested_continue_owner.lua",
    LUAU_ONLY,
)];
