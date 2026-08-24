//! 回归 case 319；覆盖 Luau captured-shared dependency DAG 的正向复用与 alias 边界。

use super::*;

pub(super) const REGRESSION_CASES_319: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_319_luau_captured_shared_diamond.lua",
    LUAU_ONLY,
)
.with_options(LUAU_OPTIMIZED_OPTIONS)];
