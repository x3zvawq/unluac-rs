//! 回归 case 351；覆盖 extended call run 的 debug local 作用域。

use super::*;

pub(super) const REGRESSION_CASES_351: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_351_extended_call_debug_scope.lua",
    PUC_LUA_54,
)
.with_options(LuaCaseOptions {
    retain_debug: true,
    ..LuaCaseOptions::DEFAULT
})];
