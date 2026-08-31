//! 回归 case 409；Lua 5.5 singleton global 合并不得逆转可观察写入顺序。

use super::*;

pub(super) const REGRESSION_CASES_409: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_409_lua55_multi_global_decl.lua",
    &[LuaCaseDialect::Lua55],
)];
