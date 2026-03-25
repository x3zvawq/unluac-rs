//! 这个模块集中声明仓库里的 Lua case 清单。
//!
//! 让回归测试直接扫目录虽然省事，但“哪些 case 当前已经纳入哪一层的契约回归”会散落在
//! 各个测试文件里，后面新增 dialect 或给单个 case 挂期望输出时就很难收口。这里先把
//! case 列表、所属 dialect 和当前是否纳入 HIR 出口回归集中到一处，后续再往上加
//! 期望输出或例外说明，也只需要扩这份 manifest。

use unluac::decompile::DecompileDialect;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum LuaCaseDialect {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
}

impl LuaCaseDialect {
    pub(crate) const fn luac_label(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
            Self::Lua54 => "lua5.4",
        }
    }

    pub(crate) const fn decompile_dialect(self) -> Option<DecompileDialect> {
        match self {
            Self::Lua51 => Some(DecompileDialect::Lua51),
            Self::Lua52 => Some(DecompileDialect::Lua52),
            Self::Lua53 => Some(DecompileDialect::Lua53),
            Self::Lua54 => Some(DecompileDialect::Lua54),
        }
    }

    pub(crate) const fn supports_hir_regression(self) -> bool {
        matches!(self, Self::Lua51)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseManifestEntry {
    pub(crate) path: &'static str,
    pub(crate) dialect: LuaCaseDialect,
    pub(crate) expect_clean_hir_exit: bool,
}

impl LuaCaseManifestEntry {
    const fn new(path: &'static str, dialect: LuaCaseDialect) -> Self {
        Self::new_with_hir_exit(path, dialect, dialect.supports_hir_regression())
    }

    const fn new_with_hir_exit(
        path: &'static str,
        dialect: LuaCaseDialect,
        expect_clean_hir_exit: bool,
    ) -> Self {
        Self {
            path,
            dialect,
            expect_clean_hir_exit,
        }
    }
}

pub(crate) const ALL_CASES: &[LuaCaseManifestEntry] = &[
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/basics/01_assignments.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/basics/02_locals_and_blocks.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/01_if_elseif_else.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/02_loops.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/03_repeat_until.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/04_generic_for.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/05_break_and_closure.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/control_flow/07_branch_state_carry.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/edge_cases/01_return_truncation.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/edge_cases/02_boolean_precedence.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/expressions/01_arithmetic_and_logic.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/01_calls_and_returns.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/02_closure_counter.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/03_vararg_and_tailcall.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/04_method_sugar.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/05_recursive_local_function.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/functions/06_closure_pipeline.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/runtime/01_pcall.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/runtime/02_coroutine.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/runtime/03_xpcall.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tables/01_constructor_and_index.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tables/02_metatable_index.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tables/03_deep_constructor.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tables/04_deep_lookup_and_overwrite.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/01_boolean_hell.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/03_repeat_until_closure_runtime.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/05_table_stress.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/06_self_sugar_trap.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/07_vararg_tail_barrier.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/08_return_truncation_barriers.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/09_closure_table_ctor.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/10_alias_mutation_trap.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/11_generic_for_mutator.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/12_crazy_table_init.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/13_closure_return_pair.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/14_coroutine_resume_shadow.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/16_nested_closure_factory.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/17_nested_short_circuit_calls.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/18_phi_shadowed_locals.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/19_numeric_for_rebound.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/20_multi_assign_rotation.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/21_method_chain_with_vararg.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/22_repeat_break_value_flow.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/23_nested_table_call_index.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/24_return_call_argument_barrier.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/25_xpcall_handler_reuse.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/26_pcall_multi_return_reuse.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/27_deep_table_dynamic_overwrite.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/27_recursive_local_function_slot.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/28_table_ctor_function_mix.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/29_loop_closure_break_return.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/common/tricky/30_while_repeat_closure_interleave.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.1/01_setfenv.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.1/02_module_legacy.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.1/03_setfenv_nested_closure.lua",
        LuaCaseDialect::Lua51,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/01_goto_and_label.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/02_env_redirect.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.2/03_extraarg_boundary.lua",
        LuaCaseDialect::Lua52,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/05_goto_continue_like.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/06_goto_irreducible_mesh.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new_with_hir_exit(
        "tests/lua_cases/lua5.2/07_env_shadow_and_closure.lua",
        LuaCaseDialect::Lua52,
        true,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/01_bitwise_and_idiv.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/02_bitwise_closure_mesh.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/03_idiv_float_branching.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/04_method_table_bitwise.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/05_integer_float_capture.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.3/07_bnot_mask_pipeline.lua",
        LuaCaseDialect::Lua53,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/01_tbc_close.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/02_const_local.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/03_const_closure_mesh.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/04_tbc_multi_exit.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/06_close_tailcall_barrier.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/07_generic_for_const_close.lua",
        LuaCaseDialect::Lua54,
    ),
    LuaCaseManifestEntry::new(
        "tests/lua_cases/lua5.4/08_vararg_const_pipeline.lua",
        LuaCaseDialect::Lua54,
    ),
];

pub(crate) fn hir_exit_regression_cases() -> impl Iterator<Item = &'static LuaCaseManifestEntry> {
    ALL_CASES.iter().filter(|entry| entry.expect_clean_hir_exit)
}
