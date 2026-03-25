//! 这些测试固定 Lua 5.4 主 pipeline 的 smoke 契约。

use unluac::decompile::{
    DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage, decompile,
};

mod decompile_pipeline {
    use super::*;

    #[test]
    fn lua54_transform_stage_reports_tbc_close_and_loadi() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/01_tbc_close.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Transform,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Transform],
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 transform stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Transform)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("lir dialect=lua5.4"), "{dump}");
        assert!(dump.contains("tbc "), "{dump}");
        assert!(dump.contains("close from"), "{dump}");
        assert!(dump.contains("get-table"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_runs_for_const_local_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/02_const_local.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump HIR ====="), "{dump}");
        assert!(dump.contains("proto#0"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_models_tbc_as_structured_stmt() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/01_tbc_close.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 hir stage should succeed for tbc fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("to-be-closed l1"), "{dump}");
        assert!(!dump.contains("unstructured summary=tbc"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_keeps_goto_close_semantics_explicit_without_unstructured_fallback() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 hir stage should succeed for goto close fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("to-be-closed t10"), "{dump}");
        assert!(dump.contains("close from r4"), "{dump}");
        assert!(dump.contains("goto L1"), "{dump}");
        assert!(!dump.contains("unstructured summary=close"), "{dump}");
    }
}
