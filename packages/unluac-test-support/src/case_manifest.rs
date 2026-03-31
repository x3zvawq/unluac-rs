//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 真正的事实源是“一个 case 支持哪些 dialect、进入哪些 suite”。
//! `unit` 和 `regression` 再从这份矩阵里展开成具体的 `(case, dialect)` 测试单元，
//! 这样后续给 common case 显式挂多个 dialect 时，不需要回到“每行一个组合”的散乱写法。

use unluac::decompile::DecompileDialect;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuaCaseDialect {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    Luajit,
    Luau,
}

impl LuaCaseDialect {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
            Self::Lua54 => "lua5.4",
            Self::Lua55 => "lua5.5",
            Self::Luajit => "luajit",
            Self::Luau => "luau",
        }
    }

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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseSuites {
    pub(crate) case_health: bool,
    pub(crate) decompile_pipeline_health: bool,
}

impl LuaCaseSuites {
    pub(crate) const fn all() -> Self {
        Self {
            case_health: true,
            decompile_pipeline_health: true,
        }
    }

    pub(crate) const fn case_health_only() -> Self {
        Self {
            case_health: true,
            decompile_pipeline_health: false,
        }
    }
}

/// 矩阵里的单个 case 定义。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseMatrixEntry {
    pub(crate) path: &'static str,
    pub(crate) dialects: &'static [LuaCaseDialect],
    pub(crate) suites: LuaCaseSuites,
}

impl LuaCaseMatrixEntry {
    const fn new(path: &'static str, dialects: &'static [LuaCaseDialect]) -> Self {
        Self::new_with_suites(path, dialects, LuaCaseSuites::all())
    }

    const fn new_with_suites(
        path: &'static str,
        dialects: &'static [LuaCaseDialect],
        suites: LuaCaseSuites,
    ) -> Self {
        Self {
            path,
            dialects,
            suites,
        }
    }
}

/// 展开后的 `(case, dialect)` 测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub(crate) suites: LuaCaseSuites,
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

pub(crate) const ALL_CASES: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/basics/01_assignments.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/basics/02_locals_and_blocks.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/01_if_elseif_else.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/02_loops.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/03_repeat_until.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/04_generic_for.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/05_break_and_closure.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/control_flow/07_branch_state_carry.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/edge_cases/01_return_truncation.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/edge_cases/02_boolean_precedence.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/expressions/01_arithmetic_and_logic.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/01_calls_and_returns.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/02_closure_counter.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/03_vararg_and_tailcall.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/04_method_sugar.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/05_recursive_local_function.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/06_closure_pipeline.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/functions/07_closure_counter_impure_step.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/common/runtime/01_pcall.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/runtime/02_coroutine.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/common/runtime/03_xpcall.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tables/01_constructor_and_index.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tables/02_metatable_index.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tables/03_deep_constructor.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tables/04_deep_lookup_and_overwrite.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/01_boolean_hell.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/03_repeat_until_closure_runtime.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/05_table_stress.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/06_self_sugar_trap.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/07_vararg_tail_barrier.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/08_return_truncation_barriers.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/09_closure_table_ctor.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/10_alias_mutation_trap.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/11_generic_for_mutator.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/12_crazy_table_init.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/13_closure_return_pair.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/14_coroutine_resume_shadow.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/16_nested_closure_factory.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/17_nested_short_circuit_calls.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/18_phi_shadowed_locals.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/19_numeric_for_rebound.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/20_multi_assign_rotation.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/21_method_chain_with_vararg.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/22_repeat_break_value_flow.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/23_nested_table_call_index.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/24_return_call_argument_barrier.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/25_xpcall_handler_reuse.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/26_pcall_multi_return_reuse.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/27_deep_table_dynamic_overwrite.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/27_recursive_local_function_slot.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/28_table_ctor_function_mix.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/29_loop_closure_break_return.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/30_while_repeat_closure_interleave.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/32_short_circuit_branch_shared_subjects.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common/tricky/33_inline_adjacent_result_sinks.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.1/01_setfenv.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.1/02_module_legacy.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.1/03_setfenv_nested_closure.lua",
        PUC_LUA_51,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.2/01_goto_and_label.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.2/02_env_redirect.lua", PUC_LUA_GE_52),
    // 这个case太大了，跑起来很墨迹
    // LuaCaseMatrixEntry::new(
    //     "tests/lua_cases/lua5.2/03_extraarg_boundary.lua",
    //     PUC_LUA_GE_52,
    // ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.2/05_goto_continue_like.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.2/06_goto_irreducible_mesh.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.2/07_env_shadow_and_closure.lua",
        PUC_LUA_GE_52,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/01_bitwise_and_idiv.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/02_bitwise_closure_mesh.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/03_idiv_float_branching.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/04_method_table_bitwise.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/05_integer_float_capture.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.3/07_bnot_mask_pipeline.lua",
        PUC_LUA_GE_53,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.4/01_tbc_close.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.4/02_const_local.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/03_const_closure_mesh.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/04_tbc_multi_exit.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/06_close_tailcall_barrier.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/07_generic_for_const_close.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.4/08_vararg_const_pipeline.lua",
        PUC_LUA_GE_54,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua5.5/01_global_basic.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/02_global_function_capture.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/03_named_vararg_basic.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/04_named_vararg_closure_mesh.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/05_global_const_gate.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/06_global_named_vararg_pipeline.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/07_named_vararg_return.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/lua5.5/08_named_vararg_index_only.lua",
        PUC_LUA_GE_55,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/01_continue_compound_pipeline.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/02_if_expression_router.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/03_interp_escape_nested.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/luau/04_typed_callback_mesh.lua", LUAU_ONLY),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/05_repeat_continue_funnel.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/06_compound_index_side_effects.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/luau/07_generic_fold_branch.lua", LUAU_ONLY),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/08_optional_closure_dispatch.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/luau/09_recursive_if_interp.lua", LUAU_ONLY),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luau/10_nested_continue_closure_mesh.lua",
        LUAU_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/01_goto_cdata_accumulator.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/02_imaginary_wave_fold.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/03_ffi_struct_goto_mesh.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/04_bit_cdata_pipeline.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/05_hexfloat_dispatch.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/06_label_closure_reentry.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/07_ffi_metatype_counter.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/08_imaginary_branch_mesh.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/09_ull_table_rotation.lua",
        LUAJIT_ONLY,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/luajit/10_jit_status_hexfloat.lua",
        LUAJIT_ONLY,
    ),
];

pub(crate) fn case_health_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries().filter(|entry| entry.suites.case_health)
}

pub(crate) fn decompile_pipeline_health_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries().filter(|entry| entry.suites.decompile_pipeline_health)
}

fn manifest_entries() -> impl Iterator<Item = LuaCaseManifestEntry> {
    ALL_CASES.iter().flat_map(|entry| {
        entry
            .dialects
            .iter()
            .copied()
            .map(move |dialect| LuaCaseManifestEntry {
                path: entry.path,
                dialect,
                suites: entry.suites,
            })
    })
}
