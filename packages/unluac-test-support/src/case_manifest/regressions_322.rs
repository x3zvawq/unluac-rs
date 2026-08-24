//! 回归 case 322；覆盖 stripped alias/field sugar 与 call-result PhysicalRoot 边界。

use super::*;

pub(super) const REGRESSION_CASES_322: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_322_alias_and_sugar.lua",
    PUC_LUA_51,
)];
