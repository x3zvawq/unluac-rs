//! 回归 case 374；覆盖 goto 污染 proto 内的 clean path-condition islands 与多入口拒绝。

use super::*;

pub(super) const REGRESSION_CASES_374: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_374_path_condition_clean_islands.lua",
    PUC_LUA_GE_52,
)
.with_options(LuaCaseOptions {
    retain_debug: true,
    ..LuaCaseOptions::DEFAULT
})];
