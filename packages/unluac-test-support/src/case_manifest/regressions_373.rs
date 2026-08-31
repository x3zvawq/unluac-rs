//! 回归 case 373；覆盖循环头机械 RHS 的不变量放宽。

use super::*;

pub(super) const REGRESSION_CASES_373: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_373_loop_invariant_rhs.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_373_loop_lookup_eval_count.lua",
        ALL_DIALECTS,
    ),
];
