//! 回归 case 405；多值 return 首项恢复 method alias 时保留单值宽度。

use super::*;

pub(super) const REGRESSION_CASES_405: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_405_method_alias_multi_return_head.lua",
    &[LuaCaseDialect::Lua54],
)];
