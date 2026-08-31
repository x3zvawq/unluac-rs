//! 回归 case 377；覆盖仍以 temp 表示的参数同 home 写不能伪装成稳定参数。

use super::*;

pub(super) const REGRESSION_CASES_377: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_377_dead_temp_param_home_lifetime.lua",
    PUC_LUA_GE_52,
)];
