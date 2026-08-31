//! 回归 case 396；child block 的 lookup 物理 root 在已证明的 home 复用点结束。

use super::*;

pub(super) const REGRESSION_CASES_396: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_396_lookup_child_scope_end.lua",
    PUC_LUA_GE_54,
)];
