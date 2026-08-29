//! 回归 case 376；覆盖已初始化多 local 的未使用尾槽清理与前缀 value-pack 屏障。

use super::*;

pub(super) const REGRESSION_CASES_376: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_376_unused_initialized_local_suffix.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_376_unused_initialized_local_prefix.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
];
