//! 回归 case 363；覆盖公共 copy 越过已结束的嵌套 close scope。

use super::*;

pub(super) const REGRESSION_CASES_363: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_363_nested_close_common_copy.lua",
    PUC_LUA_GE_54,
)];
