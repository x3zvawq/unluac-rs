//! 回归 case 344；覆盖与函数出口重合的尾部 do 作用域清理。

use super::*;

pub(super) const REGRESSION_CASES_344: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_344_tail_do_same_exit.lua",
    PUC_LUA_54,
)];
