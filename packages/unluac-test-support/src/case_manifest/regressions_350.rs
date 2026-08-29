//! 回归 case 350；覆盖 mechanical run 向多值 return 的标量收敛。

use super::*;

pub(super) const REGRESSION_CASES_350: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_350_mechanical_multi_return_scalars.lua",
    PUC_LUA_ALL,
)];
