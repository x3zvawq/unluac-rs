//! 回归 case 501–600；保持按历史编号的稳定执行顺序，不负责 case 展开。

use super::*;

pub(super) const REGRESSION_CASES_501_600: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_501_ast_scope_checkpoints.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_501_ast_scope_checkpoints.lua",
        &[LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_502_repeat_permission_checkpoints.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_502_repeat_permission_checkpoints.lua",
        &[LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_503_wide_local_nil_clear.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_503_wide_local_nil_clear.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
];
