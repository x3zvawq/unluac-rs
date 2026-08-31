//! 回归 case 385；local 预算分段保留 PhysicalRoot 的原词法生命周期。

use super::*;

pub(super) const REGRESSION_CASES_385: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_385_local_scope_physical_root.lua",
    PUC_LUA_54,
)];
