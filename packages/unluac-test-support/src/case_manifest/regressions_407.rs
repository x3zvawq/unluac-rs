//! 回归 case 407；NumericFor start 可收回 method alias 并保持单值宽度。

use super::*;

pub(super) const REGRESSION_CASES_407: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_407_method_alias_numeric_for_start.lua",
    &[LuaCaseDialect::Lua54],
)];
