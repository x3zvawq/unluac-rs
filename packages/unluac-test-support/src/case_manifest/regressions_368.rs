//! 回归 case 368；覆盖 repeat 条件折叠对闭合 goto/label 子图的 owner 证明。

use super::*;

pub(super) const REGRESSION_CASES_368: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_368_repeat_closed_goto_owner.lua",
    LUA_GOTO_DIALECTS,
)];
