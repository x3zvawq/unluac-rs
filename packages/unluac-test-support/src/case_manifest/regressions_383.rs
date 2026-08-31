//! 回归 case 383；StableCopy 原子替换分散在多个顶层语句中的全部读取。

use super::*;

pub(super) const REGRESSION_CASES_383: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_383_stable_copy_multi_stmt.lua",
    PUC_LUA_ALL,
)];
