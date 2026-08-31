//! 回归 case 354；覆盖 call-alias run owner 拒绝后的单项相邻值内联。

use super::*;

pub(super) const REGRESSION_CASES_354: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_354_adjacent_final_arg_value_arity.lua",
        ALL_DIALECTS,
    ),
];
