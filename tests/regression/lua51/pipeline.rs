//! 这些测试固定 Lua 5.1 下已经修好的特定回归点。
//!
//! 它们不再承担通用 stage smoke 或 pipeline 健康检查职责，只保护那些已经
//! 被 case 固定下来的结构恢复、可读性和命名回归。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileOptions, DecompileStage, decompile,
};
use unluac::naming::{NamingMode, NamingOptions};
use unluac::readability::ReadabilityOptions;

mod decompile_pipeline {
    use super::*;

    #[test]
    fn boolean_hell_hir_prefers_guarded_or_shape_for_initial_short_circuit_value() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/01_boolean_hell.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("boolean_hell hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("decision("), "{dump}");
        assert!(
            !dump.contains("local [\"l0\"] = ((p0 or (p3 and (p1 and p2))) and"),
            "{dump}"
        );
        assert!(
            dump.contains("local [\"l0\"] = ((p0 and")
                || dump.contains("local [\"l0\"] = (((p0 and"),
            "{dump}"
        );
    }

    #[test]
    fn ultimate_mess_hir_folds_single_access_segments_without_collapsing_the_whole_chain() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                readability: ReadabilityOptions {
                    return_inline_max_complexity: usize::MAX,
                    index_inline_max_complexity: usize::MAX,
                    args_inline_max_complexity: usize::MAX,
                    access_base_inline_max_complexity: usize::MAX,
                },
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("ultimate_mess hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("local [\"l1\"] = p0[\"branches\"]["),
            "{dump}"
        );
        assert!(dump.contains("local [\"l2\"] = l1[\"items\"]["), "{dump}");
        assert!(dump.contains("return "), "{dump}");
        assert!(dump.contains("l2[\"value\"]"), "{dump}");
    }

    #[test]
    fn ultimate_mess_debug_chunk_still_keeps_two_access_chain_locals() {
        let result = decompile(
            &crate::support::compile_lua_case_with_debug(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                readability: ReadabilityOptions {
                    return_inline_max_complexity: usize::MAX,
                    index_inline_max_complexity: usize::MAX,
                    args_inline_max_complexity: usize::MAX,
                    access_base_inline_max_complexity: usize::MAX,
                },
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("ultimate_mess hir stage with debug chunk should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("local [\"l1\"] = p0[\"branches\"]["),
            "{dump}"
        );
        assert!(dump.contains("local [\"l2\"] = l1[\"items\"]["), "{dump}");
        assert!(dump.contains("return "), "{dump}");
        assert!(dump.contains("l2[\"value\"]"), "{dump}");
    }

    #[test]
    fn ultimate_mess_readability_recovers_guarded_short_circuit_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("ultimate_mess readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains(
                "local l0 = ((((p1 and p2) or p3) and (p2 or (p3 and p1))) or ((not p1) and (not p2)))"
            ),
            "{dump}"
        );
        assert!(
            dump.contains("local l1 = p0.branches[((p1 and \"t\") or \"f\")]"),
            "{dump}"
        );
        assert!(
            dump.contains("local l2 = l1.items[((p2 and 1) or 2)]"),
            "{dump}"
        );
        assert!(
            dump.contains("return ((l0 and \"T\") or \"F\"), l2.value"),
            "{dump}"
        );
    }

    #[test]
    fn short_circuit_side_effects_readability_sinks_hoisted_multi_return_locals() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("local l1, l2, l3, l4"), "{dump}");
        assert!(dump.contains("local l1, l2 = l0(false, true)"), "{dump}");
        assert!(dump.contains("local l3, l4 = l0(true, 0)"), "{dump}");
    }

    #[test]
    fn short_circuit_side_effects_generate_uses_register_like_names_in_debug_like_mode() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                naming: NamingOptions {
                    mode: NamingMode::DebugLike,
                    debug_like_include_function: true,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("local function r0_0("),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local function r1_1("),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local r0_1, r0_2 = r0_0(false, true)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("r1_0[#r1_0 + 1] = p2_0"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("u2_0[#u2_0 + 1] = p2_0"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local function fn("),
            "{}",
            generated.source
        );
    }

    #[test]
    fn short_circuit_side_effects_generate_numbers_function_shape_names_in_simple_mode() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert_eq!(
            generated.source.matches("local function fn(").count(),
            1,
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local function fn2("),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local function fn2(c, d)"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local function fn2(a, b)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn short_circuit_side_effects_hir_collapses_index_temps_before_locals() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign u0[((# u0) + 1)] = p0"), "{dump}");
        assert!(!dump.contains("local [\"l0\"] = u0"), "{dump}");
        assert!(!dump.contains("local [\"l1\"] = (# u0)"), "{dump}");
    }

    #[test]
    fn short_circuit_side_effects_hir_restores_impure_value_short_circuit() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains(
                "local [\"l2\"] = ((call(normal) l1(\"a\", p0) multiret=false and call(normal) l1(\"b\", p1) multiret=false) or (call(normal) l1(\"c\", true) multiret=false and call(normal) l1(\"d\", \"done\") multiret=false))"
            ),
            "{dump}"
        );
        assert!(!dump.contains("if l2"), "{dump}");
        assert!(!dump.contains("local [\"l5\"] = -"), "{dump}");
    }

    #[test]
    fn short_circuit_side_effects_generate_inherits_parent_local_name_for_closure_upvalue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("tbl[#tbl + 1] = c"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("up[#up + 1] = c"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn short_circuit_side_effects_generate_restores_impure_short_circuit_expression() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains(
                "local ok = fn2(\"a\", a) and fn2(\"b\", b) or fn2(\"c\", true) and fn2(\"d\", \"done\")"
            ),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("if result"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn short_circuit_side_effects_generate_inlines_single_use_concat_alias() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated
                .source
                .contains("return ok, table.concat(tbl, \",\")"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local concat = table.concat"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn short_circuit_side_effects_generate_omits_terminal_empty_chunk_return() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            !generated.source.trim_end().ends_with("return"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .trim_end()
                .ends_with("print(\"short\", result2, value2)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn nested_loop_mesh_hir_keeps_inner_loop_tail_as_break_without_synthetic_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("nested_loop_mesh hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("break"), "{dump}");
        assert!(!dump.contains("continue"), "{dump}");
    }

    #[test]
    fn nested_loop_mesh_readability_inlines_loop_header_and_branch_exprs() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("nested_loop_mesh readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("for l0 = 1, p0, 1 do"), "{dump}");
        assert!(dump.contains("if ((l0 + l3) % 2) == 0 then"), "{dump}");
        assert!(
            dump.contains("l1[((# l1) + 1)] = ((l0 * 10) + l3)"),
            "{dump}"
        );
        assert!(!dump.contains("local l2 = 1"), "{dump}");
        assert!(!dump.contains("local l4 = 1"), "{dump}");
        assert!(!dump.contains("local l7 = (l0 + l3)"), "{dump}");
        assert!(!dump.contains("local l8 = (l7 % 2)"), "{dump}");
    }

    #[test]
    fn nested_loop_mesh_generate_stage_succeeds_without_continue_or_goto() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("nested_loop_mesh generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("for i = 1, a, 1 do"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("break"), "{}", generated.source);
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("goto"), "{}", generated.source);
        assert!(
            !generated.source.contains("local value = 1"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value2 = a"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value3 = 1"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local ok2"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local ok3"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn branch_state_carry_hir_keeps_numeric_for_branch_merge_without_synthetic_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/07_branch_state_carry.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("branch_state_carry hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign l2[((# l2) + 1)] = l1"), "{dump}");
        assert!(!dump.contains("continue"), "{dump}");
    }

    #[test]
    fn branch_state_carry_readability_recovers_for_header_and_elseif_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/07_branch_state_carry.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("branch_state_carry readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("for l0 = 1, (# p0), 1 do"), "{dump}");
        assert!(dump.contains("if l4 > 0 then"), "{dump}");
        assert!(dump.contains("elseif l4 == 0 then"), "{dump}");
        assert!(!dump.contains("local l3 = 1"), "{dump}");
        assert!(!dump.contains("else\n      if"), "{dump}");
        assert!(!dump.contains("if 0 < l4 then"), "{dump}");
    }

    #[test]
    fn branch_state_carry_generate_stage_succeeds_without_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/control_flow/07_branch_state_carry.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("branch_state_carry generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("tbl[#tbl + 1] = ok"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("for i = 1, #a, 1 do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("if item > 0 then"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("elseif item == 0 then"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"branch-state\", fn({ 2, 0, -3, 1, -1 }))"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value = 1"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local ok2 = #a"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("else\n        if"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("if 0 < item then"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn return_truncation_hir_folds_set_list_tail_into_table_constructor() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/edge_cases/01_return_truncation.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("return_truncation hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("table(array=2, record=0, trailing=call(normal) l0() multiret=true)"),
            "{dump}"
        );
        assert!(!dump.contains("table-set-list"), "{dump}");
    }

    #[test]
    fn return_truncation_generate_stage_keeps_tail_multiret_constructor_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/edge_cases/01_return_truncation.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                naming: NamingOptions {
                    mode: NamingMode::DebugLike,
                    debug_like_include_function: true,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("return_truncation generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated
                .source
                .contains("local r0_1 = { r0_0(), \"tail\", r0_0() }"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"ret\", table.concat(r0_1, \",\"))"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("table-set-list"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn closure_counter_hir_recovers_short_circuit_update_without_dead_materialization_shell() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/02_closure_counter.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("closure_counter hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign u0 = (u0 + (p0 or 1))"), "{dump}");
        assert!(!dump.contains("if p0"), "{dump}");
        assert!(!dump.contains("assign t1 = p0"), "{dump}");
        assert!(!dump.contains("assign t2 = 1"), "{dump}");
        assert!(!dump.contains("local [\"l0\"] = u0"), "{dump}");
    }

    #[test]
    fn closure_counter_generate_restores_compact_closure_counter_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/02_closure_counter.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("closure_counter generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("value = value + (b or 1)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"closure\", result(), result(2), result())"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("if b then"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value3, value4"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value = value2"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn closure_counter_impure_step_hir_keeps_impure_short_circuit_expr_without_if_fallback() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/07_closure_counter_impure_step.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("closure_counter_impure_step hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign u0 = (l0 + (l3 or 1))"), "{dump}");
        assert!(
            dump.contains("call(method) l2(l1) multiret=false"),
            "{dump}"
        );
        assert!(!dump.contains("if l3"), "{dump}");
        assert!(!dump.contains("if p0"), "{dump}");
    }

    #[test]
    fn closure_counter_impure_step_generate_keeps_impure_or_shape_without_if_fallback() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/07_closure_counter_impure_step.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("closure_counter_impure_step generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("value = value2 + (result or 1)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"closure-impure\", result(), result(), result(), result())"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("if result then"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("if value3.next"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("value4"), "{}", generated.source);
    }

    #[test]
    fn recursive_local_function_hir_recovers_self_capture_as_local_binding() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/05_recursive_local_function.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("recursive_local_function hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("local [\"l0\"] = closure(proto#2 captures=l0)"),
            "{dump}"
        );
        assert!(!dump.contains("captures=t0"), "{dump}");
        assert!(
            dump.contains("return call(normal) l0(p0, 1) multiret=true"),
            "{dump}"
        );
    }

    #[test]
    fn recursive_local_function_generate_keeps_recursive_call_on_local_name() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/05_recursive_local_function.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                naming: NamingOptions {
                    mode: NamingMode::DebugLike,
                    debug_like_include_function: true,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("recursive_local_function generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("local function r1_0("),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("return r1_0(p2_0 - 1, p2_1 * p2_0)"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("u2_0("), "{}", generated.source);
        assert!(
            !generated.source.contains("local r1_0"),
            "{}",
            generated.source
        );
    }
}

fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    crate::support::compile_lua_case(dialect_label, source_relative)
}
