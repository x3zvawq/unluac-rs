//! 回归 case 323；覆盖终态 fixed nil pack 的 HIR 收敛。

use super::*;

pub(super) const REGRESSION_CASES_323: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_323_terminal_nil_return_pack.lua",
    ALL_DIALECTS,
)];
