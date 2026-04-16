//! 这些测试固定 Luau 已经修好的主 pipeline 回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::naming::NamingOptions;

mod decompile_pipeline {
    use super::*;

    #[test]
    fn boolean_hell_hir_stage_recovers_structured_bool_flow_without_residual_nodes() {
        let chunk = crate::support::compile_lua_case(
            "luau",
            "tests/lua_cases/common/tricky/01_boolean_hell.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luau,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("luau boolean_hell hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("if ((l0 and p0) or ((not l0) and p1))"),
            "{dump}"
        );
        assert!(!dump.contains("goto "), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn boolean_hell_generate_stage_emits_luau_without_goto() {
        let chunk = crate::support::compile_lua_case(
            "luau",
            "tests/lua_cases/common/tricky/01_boolean_hell.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luau,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("luau boolean_hell generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("if "), "{}", generated.source);
        assert!(!generated.source.contains("goto "), "{}", generated.source);
    }

    #[test]
    fn repeat_break_value_flow_hir_stage_uses_current_state_for_break_guard() {
        let chunk = crate::support::compile_lua_case(
            "luau",
            "tests/lua_cases/common/tricky/22_repeat_break_value_flow.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luau,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("luau repeat_break_value_flow hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("if (10 < l1)"), "{dump}");
        assert!(!dump.contains("local [\"l3\"] = -"), "{dump}");
        assert!(!dump.contains("assign l3 ="), "{dump}");
    }

    #[test]
    fn repeat_continue_funnel_hir_stage_keeps_branch_carried_state_writeback() {
        let chunk = crate::support::compile_lua_case(
            "luau",
            "tests/lua_cases/luau/05_repeat_continue_funnel.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luau,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("luau repeat_continue_funnel hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign t1 = (t1 * t0)"), "{dump}");
        assert!(!dump.contains("local [\"l5\"] = (t1 * t0)"), "{dump}");
    }

    #[test]
    fn nested_continue_closure_mesh_generate_stage_reuses_captured_table_binding() {
        let chunk = crate::support::compile_lua_case(
            "luau",
            "tests/lua_cases/luau/10_nested_continue_closure_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luau,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("luau nested_continue_closure_mesh generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("in ipairs(tbl) do"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("ipairs(up)"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local up"),
            "{}",
            generated.source
        );
    }
}
