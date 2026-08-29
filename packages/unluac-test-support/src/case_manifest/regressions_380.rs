//! 回归 case 380；StableCopy 原子收回同一语句内的多次读取。

use super::*;

pub(super) const REGRESSION_CASES_380: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_380_stable_copy_same_stmt_multi_use.lua",
    PUC_LUA_ALL,
)];
