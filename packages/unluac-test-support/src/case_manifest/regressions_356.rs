//! 回归 case 356；覆盖 temp-inline 缩短 lookup/copy 物理 root 导致对象提前回收。

use super::*;

pub(super) const REGRESSION_CASES_356: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_356_temp_inline_lookup_root_lifetime.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_356_physical_root_copy_lifetime.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_356_lookup_distinct_home_lifetime.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_356_lookup_multi_nil_release.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_356_lookup_copy_only_root.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
];
