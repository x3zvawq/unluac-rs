//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 真正的事实源是“一个 case 属于哪类测试、支持哪些 dialect”。
//! 目录负责区分 `unit` / `regression`，矩阵只负责展开具体 `(case, dialect)` 测试单元，
//! 这样后续给 common case 显式挂多个 dialect 时，不需要回到“每行一个组合”的散乱写法。

use strum_macros::{Display, IntoStaticStr};
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
    pub(crate) const fn decompile_dialect(self) -> Option<DecompileDialect> {
        match self {
            Self::Lua51 => Some(DecompileDialect::Lua51),
            Self::Lua52 => Some(DecompileDialect::Lua52),
            Self::Lua53 => Some(DecompileDialect::Lua53),
            Self::Lua54 => Some(DecompileDialect::Lua54),
            Self::Lua55 => Some(DecompileDialect::Lua55),
            Self::Luajit => Some(DecompileDialect::Luajit),
            Self::Luau => Some(DecompileDialect::Luau),
        }
    }
}

/// 矩阵里的单个 case 定义。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseMatrixEntry {
    pub(crate) path: &'static str,
    pub(crate) dialects: &'static [LuaCaseDialect],
}

impl LuaCaseMatrixEntry {
    const fn new(path: &'static str, dialects: &'static [LuaCaseDialect]) -> Self {
        Self { path, dialects }
    }
}

/// 展开后的 `(case, dialect)` 测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
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
const PUC_LUA_51: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51];
const PUC_LUA_GE_52: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
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
    // ── dialect-specific cases ──
    LuaCaseMatrixEntry::new("tests/unit-case/lua51_01.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_01_env.lua", PUC_LUA_GE_52),
    LuaCaseMatrixEntry::new("tests/unit-case/lua52_02_goto.lua", PUC_LUA_GE_52),
    // lua52_03_extraarg_boundary 太大，保留但不注册
    LuaCaseMatrixEntry::new("tests/unit-case/lua53_01.lua", PUC_LUA_GE_53),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_01_close.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua54_02_const.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_01_global.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/lua55_02_named_vararg.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/unit-case/luajit_01.lua", LUAJIT_ONLY),
    LuaCaseMatrixEntry::new("tests/unit-case/luau_01.lua", LUAU_ONLY),
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
        PUC_LUA_51,
    ),
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
        PUC_LUA_51,
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
            })
    })
}
