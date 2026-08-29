//! 回归 case 395；generic-for 单项 iterator callee alias 可安全收回。

use super::*;

pub(super) const REGRESSION_CASES_395: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_395_generic_for_single_call_alias.lua",
    ALL_DIALECTS,
)];
