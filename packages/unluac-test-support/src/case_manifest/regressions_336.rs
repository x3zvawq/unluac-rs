//! 回归 case 336；覆盖 carried-local branch state copy 的循环回边、可重入写与 debug 策略。

use super::*;

pub(super) const REGRESSION_CASES_336: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_336_loop_branch_state_copy.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_336_loop_branch_state_copy.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
];
