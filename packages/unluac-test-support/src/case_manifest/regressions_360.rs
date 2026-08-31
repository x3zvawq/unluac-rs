//! 回归 case 360；覆盖并行 nil overwrite 终止多个物理 root 的生命周期配对。

use super::*;

pub(super) const REGRESSION_CASES_360: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_360_multi_nil_allocation_root.lua",
    PUC_LUA_ALL,
)];
