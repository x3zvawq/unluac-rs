//! 回归 case 370；覆盖 repeat prefix Decision 与尾条件 owner 的独立收敛。

use super::*;

pub(super) const REGRESSION_CASES_370: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_370_repeat_prefix_decision.lua",
    PUC_LUA_GE_54,
)];
