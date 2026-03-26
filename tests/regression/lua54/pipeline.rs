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
        assert!(dump.contains("to-be-closed l"), "{dump}");
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

    #[test]
    fn lua54_ast_stage_absorbs_simple_tbc_into_local_close_decl() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/01_tbc_close.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Ast,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Ast],
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 ast stage should succeed for simple tbc fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("<close> ="), "{dump}");
        assert!(!dump.contains("to-be-closed"), "{dump}");
        assert!(!dump.contains("close from"), "{dump}");
    }

    #[test]
    fn lua54_ast_stage_rejects_goto_close_fixture_until_close_scopes_are_recovered() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        );
        let error = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Ast,
                ..DecompileOptions::default()
            },
        )
        .expect_err("lua5.4 ast stage should currently reject residual close fixture");

        let message = error.to_string();
        assert!(message.contains("explicit close semantics"), "{message}");
    }

    #[test]
    fn lua54_readability_stage_absorbs_generic_for_hidden_close_state_into_source_like_for_loop() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/07_generic_for_const_close.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 readability stage should succeed for generic-for close fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Readability));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("for l0, l1, l2 in l5({\"aa\", \"bbb\", \"c\"}) do"), "{dump}");
        assert!(dump.contains("local l13<close> ="), "{dump}");
        assert!(!dump.contains("to-be-closed"), "{dump}");
        assert!(!dump.contains("local t9"), "{dump}");
    }
}
