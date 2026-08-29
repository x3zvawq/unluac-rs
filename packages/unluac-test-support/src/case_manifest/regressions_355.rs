//! 回归 case 355；覆盖 mechanical run 搬入循环条件的求值次数与删除 root 的生命周期差异。

use super::*;

pub(super) const REGRESSION_CASES_355: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_355_mechanical_loop_condition_snapshot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_355_mechanical_run_root_lifetime.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_355_mechanical_return_root_lifetime.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
];
