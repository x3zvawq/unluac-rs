//! 回归 case 369；覆盖 repeat-owner TBC 与尾条件折叠的关闭顺序。

use super::*;

const LUA55_ONLY: &[LuaCaseDialect] = &[LuaCaseDialect::Lua55];

pub(super) const REGRESSION_CASES_369: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_369_repeat_tbc_condition_owner.lua",
    LUA55_ONLY,
)];
