//! 回归 case 347；覆盖 generic-for dead mirror local 的 weak-value GC lifetime。

use super::*;

pub(super) const REGRESSION_CASES_347: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_347_generic_for_dead_mirror_gc_root.lua",
    PUC_LUA_54,
)];
