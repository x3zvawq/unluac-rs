//! 回归 case 408；多值纯 Name Assign 首项可收回 method alias 并保持单值宽度。

use super::*;

pub(super) const REGRESSION_CASES_408: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_408_method_alias_multi_assign_head.lua",
    &[LuaCaseDialect::Lua54],
)];
