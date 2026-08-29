//! 回归 case 413；function-sugar 删除 repeat body binding 时必须计入 until 条件 use。

use super::*;

pub(super) const REGRESSION_CASES_413: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_413_repeat_condition_binding_use.lua",
    &[LuaCaseDialect::Lua54],
)];
