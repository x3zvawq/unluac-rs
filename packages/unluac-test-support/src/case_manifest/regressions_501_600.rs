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
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_504_allocation_home_index.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_504_allocation_home_index.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_505_debug_root_handoff.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_506_captured_root_handoff.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_506_captured_root_handoff.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_507_resource_root_handoff.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_507_resource_root_handoff.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_508_grouped_root_owner_chain.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_508_grouped_root_owner_chain.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_509_call_dispatch_root_order.lua",
        &[LuaCaseDialect::Luajit],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_509_call_dispatch_root_order.lua",
        &[LuaCaseDialect::Luajit],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_510_return_lookup_value_dag.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_511_shared_result_values.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_511_luajit_result_identity.lua",
        &[LuaCaseDialect::Luajit],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_512_table_result_nil_shape.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_513_luau_table_template.lua",
        &[LuaCaseDialect::Luau],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_514_luau_table_preallocation.lua",
        &[LuaCaseDialect::Luau],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_515_loop_binding_decision.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_516_luau_record_key_syntax.lua",
        &[LuaCaseDialect::Luau],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_517_decl_sink_write_scope.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_518_pending_integer_key_shadow.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_519_constructor_nil_prefix.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_520_capture_closed_nil_slot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_521_deep_arithmetic_chain.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_522_lua55_function_target_global_gate.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_523_lua55_global_missing_promotion.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_524_debug_scope_object_cohort.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_524_debug_scope_object_cohort.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_525_debug_scope_lookup_root.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_525_debug_scope_lookup_root.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_526_call_argument_root_handoff.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_526_call_argument_root_handoff.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_527_debug_scope_across_branch.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_527_debug_scope_across_branch.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_528_debug_scope_loop_windows.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_528_debug_scope_loop_windows.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_529_repeat_parenthesized_call_separator.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_529_repeat_parenthesized_call_separator.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_530_debug_scope_numeric_for.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_530_debug_scope_numeric_for.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_531_debug_scope_generic_for.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_531_debug_scope_generic_for.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_532_debug_scope_generic_for_close.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_532_debug_scope_generic_for_close.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_533_debug_scope_mutable_callee.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_533_debug_scope_mutable_callee.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_534_debug_overwrite_lookup_root.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_534_debug_overwrite_lookup_root.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_535_multi_result_frame_roots.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_535_multi_result_frame_roots.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_536_multi_result_callee_lookup.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_536_multi_result_callee_lookup.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_537_cyclic_copy_root.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_537_cyclic_copy_root.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_538_cyclic_copy_debug_owner.lua",
        &[LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_538_cyclic_copy_debug_owner.lua",
        &[LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_539_initializer_plain_table_scope.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_540_cyclic_copy_source_scope.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_541_nested_close_source_scope.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_542_observing_snapshot_overwrite.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_543_snapshot_holder_reuse.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_544_copy_root_forward_exit.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_545_copy_root_entry_epoch.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_545_copy_root_entry_epoch.lua",
        PUC_LUA_GE_52,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_546_shared_home_root_intervals.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_546_shared_home_root_intervals.lua",
        PUC_LUA_GE_52,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_547_not_value_chain.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_548_pure_assignment_suffix.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_548_pure_assignment_suffix.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_549_pure_suffix_close_loop.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_549_pure_suffix_close_loop.lua",
        PUC_LUA_GE_52,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_550_pure_callable_chain.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_550_pure_callable_chain.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_551_pure_argument_chain.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_551_pure_argument_chain.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_551_pure_argument_chain.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_552_param_alias_control_flow.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_552_param_alias_control_flow.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_553_entry_nil_nested_flow.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_553_entry_nil_nested_flow.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_554_constructor_run_boundaries.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_554_constructor_run_boundaries.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_555_constructor_field_targets.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_555_constructor_field_targets.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_556_method_chain_frame_roots.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_556_method_chain_frame_roots.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_557_short_circuit_constant_snapshot.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_558_operator_result_gc_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_558_operator_result_gc_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_559_recursive_closure_table_results.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_560_close_return_error_order.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_560_close_return_error_order.lua",
        &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55],
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_561_private_constructor_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_561_private_constructor_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_562_shared_short_circuit.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_562_shared_short_circuit.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_562_short_circuit_entry_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_562_short_circuit_entry_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_563_loop_tail_capture_cleanup.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_563_loop_tail_capture_cleanup.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_564_pure_decision_graph.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_564_pure_decision_graph.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_564_pure_decision_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_564_pure_decision_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_565_boolean_value_predicate_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_565_boolean_value_predicate_gc.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_566_short_circuit_root_frontier.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_566_short_circuit_root_frontier.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_568_luajit_logical_literals.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_568_vararg_logical_atoms.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_568_luau_logical_vectors.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_VECTOR_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_567_scoped_short_circuit_frontier.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_567_scoped_short_circuit_frontier.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_569_indexed_logical_factors.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_569_indexed_logical_factors.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_570_private_table_fields.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_570_private_table_fields.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_570_luajit_field_observer.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_571_lookup_root_callback.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_571_lookup_root_callback.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_572_decision_assignment_commit.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_572_decision_assignment_commit.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_573_lookup_overwrite_home.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_573_lookup_overwrite_home.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_574_lookup_method_receiver_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_574_lookup_method_receiver_roots.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_575_known_call_return_values.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_575_known_call_return_values.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_576_template_nil_slot_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_576_template_nil_slot_order.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_577_nested_argument_callee.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_577_nested_argument_callee.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_578_cdata_boolean_root.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_578_cdata_boolean_root.lua",
        LUAJIT_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_579_constructor_call_frames.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_579_constructor_call_frames.lua",
        PUC_LUA_51,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_580_scratch_write_retirement.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_580_scratch_write_retirement.lua",
        PUC_LUA_51,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_581_conditional_constructor_frame.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_581_conditional_constructor_frame.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_582_native_return_frames.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_582_native_return_frames.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_583_caller_prefix_residuals.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_583_caller_prefix_residuals.lua",
        PUC_LUA_51,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_584_luau_call_result_copy.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_CONVERGENCE_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_585_luau_fastcall_boolean_fallback.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_586_luau_comparison_call_frames.lua",
        LUAU_ONLY,
    )
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_587_native_concat_frames.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_587_native_concat_frames.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_588_luau_array_lookup_initializer.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_588_luau_array_lookup_initializer.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LUAU_OPTIMIZED_OPTIONS
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_589_luau_inlined_factory_activation.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_590_luau_alternative_read_sources.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        luau_optimization_level: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_591_discarded_call_result_frame.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_591_discarded_call_result_frame.lua",
        ALL_NON_LUAU_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_592_luau_fresh_constant_capture.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_592_luau_fresh_constant_capture.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_593_nested_identical_read_returns.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        luau_optimization_level: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_594_luau_template_initialization_recompile.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_594_luau_template_initialization_recompile.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_595_luau_numeric_for_debug_phi.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_595_luau_numeric_for_debug_phi.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_596_debug_outer_nil_binding.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_597_luau_open_assert_lookup_order.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_598_luau_nonvararg_fresh_capture.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_598_luau_nonvararg_fresh_capture.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        // O0 debug 只多一轮声明拆分；后续三次生成逐字符固定，不能外推其它配置。
        recompile_rounds: Some(4),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO0]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_598_luau_nonvararg_fresh_capture.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_599_closed_cell_call_prefix.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_600_luau_mixed_fastcall_arguments.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_600_luau_mixed_fastcall_arguments.lua",
        LUAU_ONLY,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        recompile_rounds: Some(3),
        ..LuaCaseOptions::DEFAULT
    })
    .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
];
