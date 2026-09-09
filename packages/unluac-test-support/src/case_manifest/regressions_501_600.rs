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
];
