//! 回归 case 391；HIR 不能把 LuaJIT cdata equality 当作无事件 primitive 比较。

use super::*;

pub(super) const REGRESSION_CASES_391: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_391_luajit_cdata_equality_branch.lua",
    LUAJIT_ONLY,
)];
