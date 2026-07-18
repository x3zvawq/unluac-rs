//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 真正的事实源是“一个 case 属于哪类测试、支持哪些 dialect”。
//! 目录负责区分 `unit` / `regression`，矩阵只负责展开具体 `(case, dialect)` 测试单元，
//! 这样后续给 common case 显式挂多个 dialect 时，不需要回到“每行一个组合”的散乱写法。

use strum_macros::{Display, IntoStaticStr};
use unluac::ast::NamingMode;
use unluac::decompile::DecompileDialect;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Display, IntoStaticStr)]
pub enum LuaCaseDialect {
    #[strum(serialize = "lua5.1")]
    Lua51,
    #[strum(serialize = "lua5.2")]
    Lua52,
    #[strum(serialize = "lua5.3")]
    Lua53,
    #[strum(serialize = "lua5.4")]
    Lua54,
    #[strum(serialize = "lua5.5")]
    Lua55,
    #[strum(serialize = "luajit")]
    Luajit,
    #[strum(serialize = "luau")]
    Luau,
}

impl LuaCaseDialect {
    pub(crate) const fn decompile_dialect(self) -> DecompileDialect {
        match self {
            Self::Lua51 => DecompileDialect::Lua51,
            Self::Lua52 => DecompileDialect::Lua52,
            Self::Lua53 => DecompileDialect::Lua53,
            Self::Lua54 => DecompileDialect::Lua54,
            Self::Lua55 => DecompileDialect::Lua55,
            Self::Luajit => DecompileDialect::Luajit,
            Self::Luau => DecompileDialect::Luau,
        }
    }
}

/// 矩阵里的单个 case 定义。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseMatrixEntry {
    pub(crate) path: &'static str,
    pub(crate) dialects: &'static [LuaCaseDialect],
    pub(crate) options: LuaCaseOptions,
}

impl LuaCaseMatrixEntry {
    const fn new(path: &'static str, dialects: &'static [LuaCaseDialect]) -> Self {
        Self {
            path,
            dialects,
            options: LuaCaseOptions::DEFAULT,
        }
    }

    const fn with_options(mut self, options: LuaCaseOptions) -> Self {
        self.options = options;
        self
    }
}

/// 单个源码 case 需要的宿主编译与反编译选项。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub(crate) struct LuaCaseOptions {
    pub(crate) retain_debug: bool,
    pub(crate) naming_mode: Option<NamingMode>,
    pub(crate) luau_optimization_level: Option<u8>,
    pub(crate) luau_vector: Option<LuauVectorCaseOptions>,
    pub(crate) recompile_rounds: Option<u32>,
}

impl LuaCaseOptions {
    const DEFAULT: Self = Self {
        retain_debug: false,
        naming_mode: None,
        luau_optimization_level: None,
        luau_vector: None,
        recompile_rounds: None,
    };
}

/// Luau 编译器和反编译器共同使用的 vector 宿主身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuauVectorCaseOptions {
    pub(crate) library: Option<&'static str>,
    pub(crate) constructor: &'static str,
    pub(crate) components: u8,
}

/// 展开后的 `(case, dialect)` 测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub(crate) options: LuaCaseOptions,
}

const ALL_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
    LuaCaseDialect::Luau,
];
const ALL_NON_LUAU_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
];
const MUTABLE_NUMERIC_FOR_BINDING_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Luajit,
    LuaCaseDialect::Luau,
];
const PUC_LUA_ALL: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const PUC_LUA_51: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51];
const LUA_51_AND_LUAU: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51, LuaCaseDialect::Luau];
const LUA_51_AND_LUAJIT: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51, LuaCaseDialect::Luajit];
const PUC_LUA_52: &[LuaCaseDialect] = &[LuaCaseDialect::Lua52];
const PUC_LUA_54: &[LuaCaseDialect] = &[LuaCaseDialect::Lua54];
const PUC_LUA_GE_52: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const LUA_GOTO_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
];
const PUC_LUA_GE_53: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const PUC_LUA_GE_54: &[LuaCaseDialect] = &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55];
const PUC_LUA_GE_55: &[LuaCaseDialect] = &[LuaCaseDialect::Lua55];
const LUAU_ONLY: &[LuaCaseDialect] = &[LuaCaseDialect::Luau];
const LUAJIT_ONLY: &[LuaCaseDialect] = &[LuaCaseDialect::Luajit];
const LUAU_OPTIMIZED_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    retain_debug: false,
    naming_mode: None,
    luau_optimization_level: Some(2),
    luau_vector: None,
    recompile_rounds: None,
};
const LUAU_VECTOR_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    retain_debug: false,
    naming_mode: None,
    luau_optimization_level: Some(2),
    luau_vector: Some(LuauVectorCaseOptions {
        library: Some("vector"),
        constructor: "create",
        components: 3,
    }),
    recompile_rounds: None,
};
const LONG_CHAIN_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    recompile_rounds: Some(0),
    ..LuaCaseOptions::DEFAULT
};

const UNIT_CASES: &[LuaCaseMatrixEntry] = &[
    // ── common cases ──
    // 每个文件内部以 `local function test_xxx()` 包裹，print 首参带 file#N 标签以便逐 proto 定位。
    LuaCaseMatrixEntry::new("tests/unit-case/common_01_basics.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_02_control_flow.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_03_repeat_until.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_04_generic_for.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_05_boolean_expr.lua", ALL_DIALECTS),
    // boolean_regression 包含原 tricky/32、33（ALL_NON_LUAU），取最严格的 dialect 集
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_06_boolean_regression.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_07_return_and_multiret.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/common_08_closures.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_09_method_and_self.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/common_10_tables.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/unit-case/common_11_runtime.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/unit-case/common_12_string_encoding.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    // ── dialect-specific cases ──
    LuaCaseMatrixEntry::new("tests/unit-case/lua51_01.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_01_env.lua", PUC_LUA_GE_52).with_options(
        LuaCaseOptions {
            retain_debug: true,
            ..LuaCaseOptions::DEFAULT
        },
    ),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_02_goto.lua", PUC_LUA_GE_52),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_03_extraarg_boundary.lua", PUC_LUA_52),
    LuaCaseMatrixEntry::new("tests/unit-case/lua53_01.lua", PUC_LUA_GE_53),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_01_close.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_02_const.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_01_global.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_02_named_vararg.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/luajit_01.lua", LUAJIT_ONLY),
    LuaCaseMatrixEntry::new("tests/unit-case/luau_01.lua", LUAU_ONLY),
    LuaCaseMatrixEntry::new("tests/unit-case/luau_02_vector.lua", LUAU_ONLY)
        .with_options(LUAU_VECTOR_OPTIONS),
];

const REGRESSION_CASES: &[LuaCaseMatrixEntry] = &[
    // ── regression / adversarial cases ──
    // 这些 case 暴露了已知反编译 bug，单独建文件避免 decompile/runtime 失败波及同文件其他 proto。
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_01_boolean_adversarial.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_02_repeat_inner_ref.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_03_guarded_return_chain.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_04_short_circuit_header_call.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_05_if_else_short_circuit_shared_body.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_06_nested_repeat_continue_flag.lua",
        ALL_DIALECTS,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_07_close_scope_slot_reuse.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_08_goto_loop_phi_seed.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_09_loadnil_capture_range.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_10_loop_closure_capture_slot.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_11_assert_short_circuit_value_merge.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_12_loop_break_shared_continuation.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_13_entry_loop_state.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_07_method_receiver_single_value.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_08_global_table_install_readability.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_09_mechanical_call_and_for_inline.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_10_lua51_event_guard_goto_recovery.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_11_branch_carried_closure_capture.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_12_nested_bvm_short_circuit_tail.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_13_if_then_merge_ownership.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_14_generic_for_nested_continue.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_15_generic_for_terminal_guard.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_16_numeric_for_terminal_body.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_17_generic_for_break_pad.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_18_short_circuit_loop_shared_tail.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_19_generic_for_break_tail_binding.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_20_numeric_for_latch_shared_else.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_21_shared_terminal_return.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_22_short_circuit_pure_call_operand.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_23_or_guard_shared_tail.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_24_branch_shared_continuation.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_25_table_setlist_trailing_short_circuit.lua",
        LUA_51_AND_LUAU,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_26_forward_capture_function_coalesce.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_27_while_true_latch_tail.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_28_lua51_loop_branch_recovery.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_29_lua51_retry_loop_live_out.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_30_table_setlist_nested_producer.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_31_numeric_for_terminal_branch_coverage.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_32_generic_for_immediate_break.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_33_table_setlist_binary_producer.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_34_short_circuit_exit_jump_pad.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_35_multi_entry_loop_state.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_36_nil_fallback_alias.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_37_shared_terminal_closure_tail.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_38_method_chain_live_receiver.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_39_method_hint_open_arg_call.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_40_branch_state_and_short_prefix_escape.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_41_negated_relational_metamethod.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_42_call_arg_eval_order.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_43_global_arg_eval_order.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_44_loop_cond_eval_order.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_45_inline_stmt_eval_order.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_46_method_alias_receiver_eval_count.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_47_conditional_reassign_multi_phi.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_48_decision_value_truthiness.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_49_closure_capture_branch_write.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_50_method_chain_dead_local_side_effect.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_51_method_hint_short_circuit_arg.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_52_table_trailing_multivalue_boundary.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_53_loop_exit_state_preheader.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_54_method_alias_wide_call_args.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_55_leading_newline_string.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_56_negative_zero_float.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_57_utf8_control_string.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_58_binary_string_bytes.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_59_integer_min_literal.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_60_integral_float_literal.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_61_numeric_for_float_step.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_62_keyword_method_name.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_63_shared_fallback_value_merge.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_64_multiret_global_and_return_alias.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_65_method_decl_captured_owner.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_66_preserved_value_guard.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_67_branch_update_used_after_if.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_68_multi_value_merge_defer_to_bvm.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_69_infinite_loop_branch_merge.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_70_infinite_loop_local_merge.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_71_shared_tail_loop_path_check.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_72_loop_exit_generic_owner.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_73_branch_owns_nested_loop_exit_phi.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_74_degenerate_numeric_for.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_75_guard_bvm_priority.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_76_luau_empty_generic_for.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_77_loop_nested_break_continuation.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_78_adjacent_loop_state_handoff.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_79_generic_for_short_break.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_80_same_header_nested_loops.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_81_degenerate_numeric_for_exit_pad.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_82_numeric_for_control_pad.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_83_nested_break_exit_pad.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_84_nested_loop_scope_state.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_85_repeat_nested_numeric_body.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_86_numeric_for_duplicated_return_state.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_87_repeat_short_condition_in_degenerate_generic_for.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_88_repeat_degenerate_continue_branch.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_89_loop_break_terminal_split.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_90_degenerate_numeric_for_nested_while.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_91_branch_owned_multi_entry_loop_state.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_92_repeat_single_condition_and_generic_break.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_93_numeric_for_continue_pad_state.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_94_multi_exit_loop_terminal_state.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_95_luau_shared_continue_edge_owner.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_96_luau_loop_exit_bounded_branch.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_97_repeat_header_break_pad.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_98_short_circuit_shared_return_value.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_99_nested_loop_branch_state_seed.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_100_adjacent_loop_redefining_header_state.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_101_branch_into_loop_header_phi.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_102_implicit_else_loop_backedge.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_103_repeat_nested_loop_shared_tail.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_104_luau_repeat_skip_numeric_for.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_105_luau_same_header_loop_path_owner.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_106_luau_repeat_current_iteration_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_107_luau_linear_break_exit_pad.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_108_luau_repeat_optimized_core_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_109_luau_repeat_condition_entry_state.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_110_luau_generic_for_exit_break_pad.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_110_luau_generic_for_exit_break_pad.lua",
        LUA_51_AND_LUAJIT,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_111_luau_short_continue_shared_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_112_luau_continue_merge_state_owner.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_113_luau_short_circuit_outer_break.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_114_luau_repeat_shared_nested_loop_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_115_luau_branch_mixed_entry_update_owner.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_116_luau_numeric_for_shared_nested_preheader.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_117_luau_repeat_continue_pad_shared_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_118_luau_early_continue_nested_loop_tail.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_119_luau_repeat_continue_pad_owner.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_120_luau_short_continue_nested_tail_break.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_121_luau_short_circuit_immediate_repeat_break.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_122_luau_same_header_loop_break_owner.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_123_luau_dual_early_return_soft_merge.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_124_luau_loop_break_header_phi_owner.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_125_luau_repeat_condition_side_effect.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_126_lua51_legacy_arg_table.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_127_puc54_metamethod_operand_flip.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_128_same_header_plain_nested_loops.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_129_lua51_nonempty_backedge_pad.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_130_env_keyword_table_access.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_131_lua55_anonymous_vararg.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_132_luajit_infinite_imaginary.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_133_luajit_wide_compare_operand.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_134_negative_literal_power.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_135_same_header_sibling_latches.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_136_luau_global_operands.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_137_luajit_contextual_goto.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_138_luau_contextual_continue.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_139_lua55_contextual_global.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_140_luajit_prior_handoff_target.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_141_lua51_vararg_fixed_results.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_142_loop_multi_exit_downstream_value_merge.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_143_loop_parameter_entry_value.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_144_loop_header_eval_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_145_loop_header_snapshot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_146_direct_method_receiver_eval_count.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_147_inline_call_alias_eval_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_148_luau_repeat_recompile_state_owner.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_149_lua51_single_arm_nested_generic_for.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_150_luau_numeric_for_branch_owner.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_151_luau_nested_repeat_short_circuit_merge.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_152_luau_while_continue_break_tail.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_153_lua55_generic_for_close_break_pad.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_154_lua55_generic_for_binding_scope.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_155_outer_for_binding_inner_loops.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_156_numeric_for_binding_inner_loop.lua",
        MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_157_repeat_nested_break_return.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_158_luau_short_circuit_break_shared_tail.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_159_cross_slot_snapshot_loop_state.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_160_captured_slot_receiver_eval.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_161_lua55_abs_line_info_layout.lua",
        PUC_LUA_GE_55,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_162_table_checkpoint_new_pending_rollback.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_163_lua54_wide_env_upvalue.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_164_lua55_wide_global_decl.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_165_global_name_binding_shadow.lua",
        PUC_LUA_GE_52,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        naming_mode: Some(NamingMode::Simple),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_166_parenthesized_call_separator.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_167_same_header_repeat_short_circuit.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_168_puc_repeat_condition_exit.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_169_same_header_conditional_sibling_latch.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_170_same_header_repeat_body.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_171_captured_alias_group_home_slot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_172_temp_inline_eval_regions.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_173_terminal_return_call_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_174_explicit_value_pack.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_175_lua54_close_value_pack.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_176_sibling_latch_terminal_loop.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_177_lua55_generic_for_live_out.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_178_observable_expression_reads.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_179_long_bracket_suffix_delimiter.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_180_numeric_for_shared_tail.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_181_generic_for_branch_phi.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_182_numeric_for_before_irreducible_goto.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_183_mixed_irreducible_explicit_close.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_184_mixed_irreducible_generic_close.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_185_branch_control_forward_guards.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_186_truthy_ternary_hir_owner.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_187_irreducible_plain_loop_owner.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_188_luau_nan_fixed_point.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_189_terminal_empty_return_guard.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_190_luau_import_open_pack.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_191_vararg_open_pack_setup.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_192_luau_open_pack_callee_move.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_193_luau_unreachable_numeric_for_control.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_194_discarded_table_open_tail.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_195_terminal_exit_unknown_loop.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_196_child_writes_parent_capture.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_197_long_bracket_control_byte.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_198_local_scope_limit.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_199_nested_local_scope_budget.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_200_close_managed_writable_capture.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_201_repeat_live_out.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_202_irreducible_numeric_for_owner.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_203_irreducible_generic_for_owner.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_204_irreducible_explicit_close_owner.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_205_while_true_header_guard.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_206_luau_home_slot_compaction.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_207_decision_naturalize_budget.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_208_short_circuit_repeat_state_init.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_209_method_fixed_prefix_open_tail.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_210_repeat_multileaf_backedges.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_211_temp_inline_binding_snapshot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_212_table_constructor_field_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_213_numeric_for_short_circuit_assignment.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_214_loop_if_then_continuation.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_215_repeat_short_circuit_state.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_216_irreducible_linear_exit.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_217_terminal_close_capture_epoch.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_218_parent_write_terminal_capture.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_219_luau_capture_value_reuse.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_220_branch_close_capture_epoch.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_221_repeat_candidate_identity.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_222_shared_short_circuit_dag.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_223_multiret_global_write_order.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_224_table_capture_writeback.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_225_repeat_shared_condition_break.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_226_repeat_direct_break_condition_owner.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_227_while_short_condition_body_backedge.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_228_generic_for_cleanup_shared_continuation.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_229_long_short_circuit_chain.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_230_numeric_for_tbc_break.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_231_repeat_refine_exit_phi_owner.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_232_parent_write_after_reference_capture.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_233_raw_branch_value_before_locals.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_234_nested_phi_short_value_merge.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_235_table_constructor_eval_ownership.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_236_table_constructor_pending_alias.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_237_table_constructor_open_overlap.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_238_nested_loop_owner_exit.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_239_lua55_degenerate_generic_scope.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_240_lua55_tforprep_swap.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_241_branch_value_single_eval.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_242_repeat_nested_break_shared_fallthrough.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_243_repeat_tbc_iteration_scope.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_244_effectful_errnnil_tbc.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_245_observable_repeat_prefix_ops.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_246_repeat_nested_close_scope.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_247_disconnected_if_else_no_merge.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_248_luajit_negated_compare.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_249_boolean_shell_table_lvalue_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_250_ast_inline_ordered_snapshot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_251_method_alias_sink_order.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_252_materialize_preserves_eval.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_253_luau_deferred_open_setlist.lua",
        LUAU_ONLY,
    )
    .with_options(LUAU_OPTIMIZED_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_254_table_constructor_handoff_snapshot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_255_header_retry_terminal_state.lua",
        LUA_51_AND_LUAJIT,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_256_nested_loop_header_arm.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_257_enclosing_loop_escape_fence.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_258_short_circuit_subject_ownership.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_259_env_snapshot_identity.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_260_lua55_degenerate_generic_shared_exit.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_261_branch_shared_continuation_nearest.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_262_infinite_loop_nearest_merge.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_263_repeat_tail_temp_inline.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_264_phi_home_slot_local_limit.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_265_entry_loop_exit_state.lua",
        LUA_51_AND_LUAJIT,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_266_branch_exit_prefix_effect.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_267_branch_value_mutable_source_snapshot.lua",
        MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_268_short_circuit_nonempty_continue_reentry.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_270_luau_repeat_condition.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_271_loop_break_soft_phi.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_272_lua52_goto_capture_identity.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_273_close_capture_post_slot_reuse.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_274_temp_live_use_boundaries.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_275_nested_loop_body_scope_exit.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_276_degenerate_generic_body_region.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_277_boundary_alias_snapshot.lua",
        LUA_GOTO_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_278_conditional_captured_writeback.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_279_repeat_short_body_scope_break.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_280_nested_loop_break_shared_tail.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_281_while_nested_loop_outer_break.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_282_long_logical_ast_depth.lua",
        PUC_LUA_54,
    )
    .with_options(LONG_CHAIN_OPTIONS),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_283_nested_table_candidate.lua",
        ALL_DIALECTS,
    ),
];

pub(crate) fn unit_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries(UNIT_CASES)
}

pub(crate) fn regression_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries(REGRESSION_CASES)
}

fn manifest_entries(
    cases: &'static [LuaCaseMatrixEntry],
) -> impl Iterator<Item = LuaCaseManifestEntry> {
    cases.iter().flat_map(|entry| {
        entry
            .dialects
            .iter()
            .copied()
            .map(move |dialect| LuaCaseManifestEntry {
                path: entry.path,
                dialect,
                options: entry.options,
            })
    })
}
