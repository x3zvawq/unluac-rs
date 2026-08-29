//! 回归 case 343；覆盖 generic-for producer identity 与 vararg iterator pack 恢复。

use super::*;

pub(super) const REGRESSION_CASES_343: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_343_generic_for_iterator_live_out.lua",
        PUC_LUA_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_343_generic_for_iterator_debug_scope.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_343_generic_for_vararg_pack.lua",
        PUC_LUA_54,
    ),
];
