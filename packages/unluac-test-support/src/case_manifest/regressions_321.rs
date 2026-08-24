//! 回归 case 321；覆盖右结合 shared fallback 的稳定值吸收。

use super::*;

pub(super) const REGRESSION_CASES_321: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_321_right_associated_shared_fallback.lua",
    ALL_DIALECTS,
)];
