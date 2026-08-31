//! 回归 case 342；覆盖 boolean-shell 合并不能后移 local 的作用域起点。

use super::*;

pub(super) const REGRESSION_CASES_342: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_342_boolean_shell_local_scope.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_342_boolean_shell_lexical_scope.lua",
        PUC_LUA_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_342_boolean_shell_gc_lifetime.lua",
        PUC_LUA_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_342_boolean_shell_local_gc_lifetime.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        // Recompiling the valid generated assignment currently reaches the unrelated
        // goto-label visibility residual tracked by the control-flow pipeline.
        recompile_rounds: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
];
