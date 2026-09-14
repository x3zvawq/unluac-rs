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
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_618_condition_evaluation_entry.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_618_condition_evaluation_entry.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_619_ordered_comparison_snapshots.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_619_ordered_comparison_snapshots.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_620_comparison_upvalue_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_620_comparison_upvalue_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_621_comparison_literal_preparations.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_621_comparison_literal_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_622_comparison_root_endpoints.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_622_comparison_root_endpoints.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_623_nested_operand_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_623_nested_operand_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_624_ordered_frame_preparations.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_624_ordered_frame_preparations.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_625_puc_assignment_call_frame.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_625_puc_assignment_call_frame.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_626_closure_overwrite_frame.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_626_closure_overwrite_frame.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_627_closure_callee_prefix.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_627_closure_callee_prefix.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_628_terminal_capture_scope.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_628_terminal_capture_scope.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_629_vararg_table_call_frames.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_630_chunk_capture_return.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_630_chunk_capture_return.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_631_indexed_concat_snapshot.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_631_indexed_concat_snapshot.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_632_call_comparison_low_operand.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_632_call_comparison_low_operand.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_633_function_expression_comments.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_634_nested_function_comment_placement.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_635_nested_closure_constructors.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_635_nested_closure_constructors.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_636_nested_lookup_assignment_frames.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_636_nested_lookup_assignment_frames.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_637_indexed_arithmetic_order.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_637_indexed_arithmetic_order.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_638_concat_prefix_scratch_lifetime.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_638_concat_prefix_scratch_lifetime.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_639_concat_call_fallback.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_639_concat_call_fallback.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_640_loop_private_exit_results.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_640_loop_private_exit_results.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_640_loop_private_exit_scope.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_640_loop_private_exit_scope.lua",
        PUC_LUA_GE_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_640_loop_private_exit_readability.lua",
        PUC_LUA_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_641_return_decision_result_home.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_641_return_decision_result_home.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
];
