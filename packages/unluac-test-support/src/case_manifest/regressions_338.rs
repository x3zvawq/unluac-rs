//! 回归 case 338；覆盖 locals promotion 的循环头状态与 branch 首次写前读取证明。

use super::*;

pub(super) const REGRESSION_CASES_338: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_338_locals_value_flow.lua",
    PUC_LUA_ALL,
)];
