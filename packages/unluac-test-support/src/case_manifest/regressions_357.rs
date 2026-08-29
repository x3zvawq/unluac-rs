//! 回归 case 357；覆盖 direct goto-value 壳原样搬移 effectful parallel assignment。

use super::*;

pub(super) const REGRESSION_CASES_357: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_357_direct_goto_parallel_assignment.lua",
    LUA_GOTO_DIALECTS,
)];
