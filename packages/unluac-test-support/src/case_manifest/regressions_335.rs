//! 回归 case 335；覆盖 global-decl-pretty 的作用域、顺序、生命周期与 debug 身份证明。

use super::*;

pub(super) const REGRESSION_CASES_335: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_335_global_decl_guards.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_335_global_decl_debug.lua",
        PUC_LUA_GE_55,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
];
