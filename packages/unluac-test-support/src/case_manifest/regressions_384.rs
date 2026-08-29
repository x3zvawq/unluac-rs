//! 回归 case 384；结构化 Return 壳终结 guarded-local false path。

use super::*;

pub(super) const REGRESSION_CASES_384: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_384_guarded_local_return_shell.lua",
    PUC_LUA_54,
)];
