//! 回归 case 393；不同类型的 primitive 字面量 equality 恒为 false。

use super::*;

pub(super) const REGRESSION_CASES_393: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_393_mismatched_primitive_equality.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_393_mismatched_primitive_equality.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_O0_ONLY),
];
