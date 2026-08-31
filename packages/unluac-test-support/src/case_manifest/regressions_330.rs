//! 回归 case 330；覆盖命名安装器 IIFE 的 closure root 生命周期。

use super::*;

pub(super) const REGRESSION_CASES_330: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_330_installer_iife_lifetime.lua",
    PUC_LUA_54,
)];
