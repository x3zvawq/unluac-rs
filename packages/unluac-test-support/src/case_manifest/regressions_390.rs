//! 回归 case 390；删除无事件的 primitive literal 运算并保留错误路径。

use super::*;

pub(super) const REGRESSION_CASES_390: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_discard_safe_literal_ops.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_discard_safe_literal_ops.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_O0_ONLY),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_discard_safe_primitive_equality.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_discard_safe_integer_ops.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_reject_integer_op_errors.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_390_luajit_cdata_equality.lua",
        LUAJIT_ONLY,
    ),
];
