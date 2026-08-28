//! 回归 case 324；覆盖短路条件纯 jump connector 的 branch ownership。

use super::*;

pub(super) const REGRESSION_CASES_324: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_324_condition_connector_ownership.lua",
    PUC_LUA_51,
)];
