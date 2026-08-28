//! 回归 case 325；覆盖失败根 proto 的诊断与直接子 proto 保留契约。

use super::*;

pub(super) const REGRESSION_CASES_325: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_325_proto_failure_recovery.lua",
    PUC_LUA_51,
)
.with_expectation(LuaCaseExpectation::ProtoFailureRecovery)];
