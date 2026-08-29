//! 回归 case 327；覆盖相邻 open SETLIST 的 vararg 宽度与后续 owner capture。

use super::*;

pub(super) const REGRESSION_CASES_327: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_327_adjacent_open_setlist.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_327_adjacent_open_setlist.lua",
        LUAU_ONLY,
    ),
];
