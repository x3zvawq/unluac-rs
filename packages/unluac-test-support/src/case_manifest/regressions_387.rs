//! 回归 case 387；stable-copy 收回无事件快照并保留写入与元方法边界。

use super::*;

pub(super) const REGRESSION_CASES_387: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_387_stable_copy_eventless_snapshot.lua",
    PUC_LUA_ALL,
)];
