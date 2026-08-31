//! 回归 case 332；覆盖 logical-simplify 的 occurrence 证明、标量 vararg 与 Luau f64 边界。

use super::*;

pub(super) const REGRESSION_CASES_332: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_332_logical_simplify.lua",
    LUAU_ONLY,
)
.with_variants(LUAU_O0_ONLY)];
