//! 回归 case 392；PUC Lua 字符串排序受 locale 影响，LuaJIT 与 Luau 按字节排序。

use super::*;

pub(super) const REGRESSION_CASES_392: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_392_puc_locale_string_order.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_392_bytewise_string_order.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_392_bytewise_string_order.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_O0_ONLY),
];
