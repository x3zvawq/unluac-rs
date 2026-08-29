//! 回归 case 359；覆盖已结束 root branch 后的 terminal open-return nil pack。

use super::*;

pub(super) const REGRESSION_CASES_359: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_359_open_return_nil_after_branch.lua",
    PUC_LUA_54,
)];
