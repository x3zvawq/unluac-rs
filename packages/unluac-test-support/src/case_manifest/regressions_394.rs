//! 回归 case 394；混合 Integer/Number 比较按目标方言的数值域精确折叠。

use super::*;

pub(super) const REGRESSION_CASES_394: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_394_puc_mixed_numeric.lua",
        &[LuaCaseDialect::Lua53, LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_394_binary64_mixed_numeric.lua",
        &[LuaCaseDialect::Luajit],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_394_binary64_mixed_numeric.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_O0_ONLY),
];
