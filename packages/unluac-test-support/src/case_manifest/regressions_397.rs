//! 回归 case 397；exact call tail 不能在 generic-for 合并中变成 open tail。

use super::*;

pub(super) const REGRESSION_CASES_397: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_397_generic_for_exact_tail_arity.lua",
    &[LuaCaseDialect::Lua54],
)];
