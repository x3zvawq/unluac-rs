//! 回归 case 339；覆盖 branch-control 丢弃不可达代码时的 debug 身份与显式诊断边界。

use super::*;

pub(super) const REGRESSION_CASES_339: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_339_branch_control_debug.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_339_branch_control_diagnostic.lua",
        PUC_LUA_GE_55,
    ),
];
