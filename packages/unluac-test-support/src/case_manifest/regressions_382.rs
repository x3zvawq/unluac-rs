//! 回归 case 382；显式空 return 证明 nested terminal guard 没有父级 continuation。

use super::*;

pub(super) const REGRESSION_CASES_382: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_382_nested_terminal_fallback_return.lua",
    PUC_LUA_ALL,
)];
