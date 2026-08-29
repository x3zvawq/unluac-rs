//! 回归 case 340；覆盖 decision synthesis 的 Lua 跨表示数值判等模型。

use super::*;

pub(super) const REGRESSION_CASES_340: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_340_decision_numeric_equality.lua",
    PUC_LUA_54,
)];
