//! 回归 case 337；覆盖 fixed SETLIST 的不确定 nil table shape。

use super::*;

pub(super) const REGRESSION_CASES_337: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_337_table_constructor_local_acceptance.lua",
    PUC_LUA_54,
)
.with_expectation(LuaCaseExpectation::TableSetListResidual)];
