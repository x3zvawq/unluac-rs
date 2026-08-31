//! 回归 case 341；覆盖相邻顺序 local 合并时可观测的 debug 作用域边界。

use super::*;

pub(super) const REGRESSION_CASES_341: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_341_statement_merge_debug_scope.lua",
    PUC_LUA_54,
)
.with_options(LuaCaseOptions {
    retain_debug: true,
    ..LuaCaseOptions::DEFAULT
})];
