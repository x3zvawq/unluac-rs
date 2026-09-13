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
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_604_closed_cell_frame_slots.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_604_closed_cell_frame_slots.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_605_fastcall_direct_tables.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_605_fastcall_direct_tables.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_606_numeric_for_conversion.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_606_numeric_for_conversion.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_606_numeric_for_conversion.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_606_numeric_for_conversion.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_607_numeric_for_writable_header.lua",
        MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_607_numeric_for_writable_header.lua",
        MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_607_numeric_for_writable_header.lua",
        LUAU_ONLY,
    )
    .with_variants(&[LuaCaseVariant::LuauO0, LuaCaseVariant::LuauO2]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_607_numeric_for_writable_header.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO0, LuaCaseVariant::LuauO2]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_608_numeric_for_skip_index_release.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_608_numeric_for_skip_index_release.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_609_nil_write_groups.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_609_nil_write_groups.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_610_nil_scope_successor_frame.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_610_nil_scope_successor_frame.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_611_preserved_nil_branch_orientation.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_612_debug_phi_lexical_window.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_613_numeric_for_reused_frame.lua",
        &[LuaCaseDialect::Lua54],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_613_numeric_for_reused_frame.lua",
        &[LuaCaseDialect::Lua54],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_614_parameter_snapshot_pure_end.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_614_parameter_snapshot_pure_end.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_615_numeric_for_step_normal_state.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_615_numeric_for_step_normal_state.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_616_luajit_for_init_binding_state.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_616_luajit_for_init_binding_state.lua",
        LUAJIT_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_617_for_loop_binding_exit_state.lua",
        &[
            LuaCaseDialect::Lua51,
            LuaCaseDialect::Lua52,
            LuaCaseDialect::Lua53,
            LuaCaseDialect::Lua54,
        ],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_617_for_loop_binding_exit_state.lua",
        &[
            LuaCaseDialect::Lua51,
            LuaCaseDialect::Lua52,
            LuaCaseDialect::Lua53,
            LuaCaseDialect::Lua54,
        ],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
];
