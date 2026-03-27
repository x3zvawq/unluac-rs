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
    fn repeat_until_closure_runtime_hir_keeps_break_funnel_without_synthetic_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/03_repeat_until_closure_runtime.lua",
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
        .expect("repeat_until_closure_runtime hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("repeat"), "{dump}");
        assert!(dump.contains("break"), "{dump}");
        assert!(!dump.contains("continue"), "{dump}");
    }

    #[test]
    fn repeat_until_closure_runtime_generate_stage_succeeds_without_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/03_repeat_until_closure_runtime.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("repeat_until_closure_runtime generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("repeat"), "{}", generated.source);
        assert!(generated.source.contains("until"), "{}", generated.source);
        assert!(generated.source.contains("break"), "{}", generated.source);
        assert!(
            generated
                .source
                .contains("if ok2 > 10 and ok % 2 == 0 then"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains(
                "print(\"repeat-closure\", result[1](), result[3](), result[6](), result[7] == nil)"
            ),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local item = result[1]"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn generic_for_mutator_hir_keeps_guard_return_without_synthetic_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/11_generic_for_mutator.lua",
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
        .expect("generic_for_mutator hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("generic-for l0, l1 in"), "{dump}");
        assert!(
            dump.contains("assign l2 = (((l2 + l3) + l4) + l5)"),
            "{dump}"
        );
        assert!(dump.contains("if (20 < l2)"), "{dump}");
        assert!(dump.contains("return l3, l4, l5, l2"), "{dump}");
        assert!(!dump.contains("continue"), "{dump}");
    }

    #[test]
    fn generic_for_mutator_generate_restores_guard_return_shape_without_continue() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/11_generic_for_mutator.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("generic_for_mutator generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("for "), "{}", generated.source);
        assert!(
            generated.source.contains("in ipairs("),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local value, value2, item = k, v, a[k]"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("> 20 then"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("return "), "{}", generated.source);
        assert!(!generated.source.contains("else"), "{}", generated.source);
        assert!(
            !generated.source.contains("continue"),
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
    fn return_truncation_barriers_hir_folds_open_pack_barrier_into_constructor() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/08_return_truncation_barriers.lua",
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
        .expect("return_truncation_barriers hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("table(array=2, record=0, trailing=...)"),
            "{dump}"
        );
        assert!(!dump.contains("table-set-list"), "{dump}");
        assert!(!dump.contains("assign t1, t2 = ..."), "{dump}");
    }

    #[test]
    fn return_truncation_barriers_generate_keeps_vararg_barrier_constructor_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/08_return_truncation_barriers.lua",
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
        .expect("return_truncation_barriers generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated
                .source
                .contains("local r1_0 = { ..., \"barrier\", ... }"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"retbarrier\", table.concat(r0_1, \",\"), r0_2, r0_3, r0_4)"),
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
    fn crazy_table_init_hir_folds_mixed_constructor_without_residual_set_list() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/12_crazy_table_init.lua",
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
        .expect("crazy_table_init hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("table(array=5, record=3"), "{dump}");
        assert!(
            dump.contains("trailing=call(normal) global(string)[\"byte\"](\"A\") multiret=true"),
            "{dump}"
        );
        assert!(!dump.contains("table-set-list"), "{dump}");
    }

    #[test]
    fn crazy_table_init_generate_restores_mixed_table_literal_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/12_crazy_table_init.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("crazy_table_init generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("local function"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("a = 4"), "{}", generated.source);
        assert!(generated.source.contains("[5] = 6"), "{}", generated.source);
        assert!(
            generated.source.contains("f = function()"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("string.byte(\"A\")"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("print(\"crazy-table\""),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains(
                "print(\"crazy-table\", result[1], result[2], result[3], result[4], result[5], result[6], result.a, result.f())"
            ),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local item = result[1]"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local item2 = result[2]"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local a = result.a"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("result.f()"),
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
        assert!(
            generated
                .source
                .contains("if p2_0 == 0 then\n            return p2_1\n        end"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("u2_0("), "{}", generated.source);
        assert!(!generated.source.contains("else"), "{}", generated.source);
        assert!(
            !generated.source.contains("local r1_0"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn vararg_and_tailcall_generate_inlines_unpack_alias_chain_initializer() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/03_vararg_and_tailcall.lua",
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
        .expect("vararg_and_tailcall generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated
                .source
                .contains("local r0_0 = table.unpack or unpack"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local r0_1 = table.unpack"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("return r1_1(r0_0(r1_0))"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn self_sugar_trap_generate_recovers_method_chain_and_method_decls() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/06_self_sugar_trap.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("self_sugar_trap generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("a:method1():method2(a.prop)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("function tbl:method1()"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("function tbl:method2(b)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("function tbl.method3(a)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("a.method3(a)"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains(":method3("),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("print(\"self\", fn(tbl) == tbl)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn nested_control_flow_hir_keeps_branch_carried_loop_state_without_unresolved_phi() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
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
        .expect("nested_control_flow hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("repeat\n              assign l2 = (l2 + 1)"),
            "{dump}"
        );
        assert!(
            dump.contains("numeric-for l0 = t6, t7, t8\n              assign l2 = (l2 + l0)"),
            "{dump}"
        );
        assert!(!dump.contains("unresolved("), "{dump}");
        assert!(!dump.contains("continue"), "{dump}");
    }

    #[test]
    fn nested_control_flow_generate_restores_repeat_and_numeric_for_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("nested_control_flow generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("elseif a > 5 then"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local ok = 0"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("repeat"), "{}", generated.source);
        assert!(
            generated.source.contains("for i = 1, 5, 1 do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local result, value = fn(v)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("return ok, a > 0 and \"positive\" or \"negative\""),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local _, _,"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value2 = 1"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("ok = value"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn method_sugar_generate_recovers_method_decl_without_rewriting_explicit_dot_call() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/functions/04_method_sugar.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("method_sugar generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("function tbl:add(b)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("function tbl:read()"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("tbl:add(3)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("result2:read()"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("tbl.read(tbl)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn coroutine_hir_keeps_loop_state_update_as_assignment_before_yield() {
        let result = decompile(
            &compile_lua_case("lua5.1", "tests/lua_cases/common/runtime/02_coroutine.lua"),
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
        .expect("coroutine hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("l1 = (l1 + l0)"), "{dump}");
        assert!(
            dump.contains("call(normal) global(coroutine)[\"yield\"](l1)"),
            "{dump}"
        );
        assert!(
            !dump.contains("global(coroutine)[\"yield\"]((l1 + l0))"),
            "{dump}"
        );
    }

    #[test]
    fn coroutine_generate_keeps_state_update_before_yield() {
        let result = decompile(
            &compile_lua_case("lua5.1", "tests/lua_cases/common/runtime/02_coroutine.lua"),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("coroutine generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("for i = 1, 2, 1 do"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("coroutine.yield(") && !line.contains("+ i)")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains(" = ") && line.contains("+ i")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .filter(|line| line.contains("coroutine.yield("))
                .all(|line| !line.contains("+ i)")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.trim_start().starts_with("return ") && line.contains("* 2")),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local _, "),
            "{}",
            generated.source
        );
    }

    #[test]
    fn coroutine_generate_debug_like_compacts_visible_binding_indices_without_gaps() {
        let result = decompile(
            &compile_lua_case("lua5.1", "tests/lua_cases/common/runtime/02_coroutine.lua"),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                naming: NamingOptions {
                    mode: NamingMode::DebugLike,
                    debug_like_include_function: true,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("coroutine debug-like generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("local r0_0 = coroutine.create("),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local r0_1, r0_2 = coroutine.resume(r0_0, 10)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local r0_3, r0_4 = coroutine.resume(r0_0)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local r0_5, r0_6 = coroutine.resume(r0_0)"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("r0_11"), "{}", generated.source);
    }

    #[test]
    fn loops_hir_removes_exit_phi_after_while_to_numeric_for_chain() {
        let result = decompile(
            &compile_lua_case("lua5.1", "tests/lua_cases/common/control_flow/02_loops.lua"),
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
        .expect("loops hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("while (l2 <= 3)"), "{dump}");
        assert!(dump.contains("numeric-for l0 = 4, 6, 1"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn loops_generate_recovers_while_then_numeric_for_shape() {
        let result = decompile(
            &compile_lua_case("lua5.1", "tests/lua_cases/common/control_flow/02_loops.lua"),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("loops generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("while "), "{}", generated.source);
        assert!(
            generated.source.contains(" <= 3 do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("for i = 4, 6, 1 do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("print(\"loop\", "),
            "{}",
            generated.source
        );
    }
}

fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    crate::support::compile_lua_case(dialect_label, source_relative)
}
