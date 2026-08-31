//! 回归 case 381；cleanup 清空 continuation 后收回 single-pass repeat fence。

use super::*;

pub(super) const REGRESSION_CASES_381: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_381_single_pass_empty_continuation.lua",
    PUC_LUA_ALL,
)];
