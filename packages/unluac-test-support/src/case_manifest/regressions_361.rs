//! 回归 case 361；覆盖 numeric-for 状态准备区间内稳定 binding source 的快照链消除。

use super::*;

pub(super) const REGRESSION_CASES_361: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_361_numeric_for_stable_binding_source.lua",
    ALL_DIALECTS,
)];
