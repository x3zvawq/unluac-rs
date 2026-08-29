//! 回归 case 345；覆盖 dead temp 的 root-prefix entry-nil 删除。

use super::*;

pub(super) const REGRESSION_CASES_345: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_345_dead_temp_entry_nil.lua",
    PUC_LUA_54,
)];
