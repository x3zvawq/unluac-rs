//! 回归 case 328；覆盖 dead-labels 对 TBC active-set 证据的保留。

use super::*;

pub(super) const REGRESSION_CASES_328: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_328_dead_label_tbc_barrier.lua",
    PUC_LUA_54,
)];
