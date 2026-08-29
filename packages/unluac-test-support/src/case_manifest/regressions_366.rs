//! 回归 case 366；覆盖 repeat 条件折叠对嵌套 loop continue 的 owner 区分。

use super::*;

pub(super) const REGRESSION_CASES_366: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_366_repeat_nested_continue_owner.lua",
    LUAU_ONLY,
)
.with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)];
