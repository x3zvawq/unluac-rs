//! 回归 case 601–700；声明源码与方言矩阵，展开及验证仍由统一 runner 负责。

use super::*;

pub(super) const REGRESSION_CASES_601_700: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_601_call_copy_owner_release.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_601_call_copy_owner_release.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_602_nested_array_generic_header.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_602_nested_array_generic_header.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_603_template_record_call_order.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_603_template_record_call_order.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
];
