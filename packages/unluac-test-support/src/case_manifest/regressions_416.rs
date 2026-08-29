//! 回归 case 416；纯 copy 的独立 VM home 跨 callback 时仍须保留为 GC root。

use super::*;

pub(super) const REGRESSION_CASES_416: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_416_copy_local_callback_root.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_416_expired_copy_root.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
];
