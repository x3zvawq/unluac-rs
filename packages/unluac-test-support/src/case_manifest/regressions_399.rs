//! 回归 case 399；allocation 触发 finalizer 时分支状态必须重新建立。

use super::*;

pub(super) const REGRESSION_CASES_399: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_399_branch_state_allocation_capture.lua",
    &[LuaCaseDialect::Lua54],
)];
