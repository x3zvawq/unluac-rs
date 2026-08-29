//! 回归 case 388；fixed multi-call 结果跨事件性覆盖时保持逐 home 的物理 root 生命周期。

use super::*;

pub(super) const REGRESSION_CASES_388: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_388_cleanup_full_parallel_overwrite.lua",
    PUC_LUA_ALL,
)];
